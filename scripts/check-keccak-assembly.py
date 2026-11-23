"""Translate the release AVX-512 permutation to single-lane Lean expressions.

The accepted instruction subset has independent 64-bit lanes. Restrict memory to
the transposed argument, the read-only round constants, and leaf-function spills
inside the SysV red zone. Reject changes to the loop, addressing, or ABI unless
the translator explicitly supports them.
"""
import argparse
import ast
import re
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reg(operand):
    require(re.fullmatch(r"%zmm(?:[12]?[0-9]|3[01])", operand), operand)
    return operand


def matrix(operand):
    match = re.fullmatch(r"(\d*)\(%rdi\)", operand)
    require(match, operand)
    offset = int(match[1] or 0)
    require(offset % 64 == 0 and offset < 25 * 64, operand)
    return offset // 64


def translate(asm):
    symbols = re.findall(r"^([^\s:]*8shake2568parallel6avx5127permute):$", asm, re.M)
    require(len(symbols) == 1, "expected one AVX-512 permutation")
    body = asm.split(symbols[0] + ":\n", 1)[1].split("\t.cfi_endproc", 1)[0]
    lines = [line.strip() for line in body.splitlines() if line.strip()]
    require(lines[0] == ".cfi_startproc", lines[0])
    i = 1
    slots = {}
    while lines[i].startswith("vmovdqu64"):
        source, dest = lines[i].split(None, 1)[1].split(", ")
        require(reg(dest) not in slots, dest)
        slots[dest] = matrix(source)
        i += 1
    require(sorted(slots.values()) == list(range(25)), "incomplete state load")
    counters = {"xorl\t%eax, %eax": ("%rax", "%rcx"), "xorl\t%ecx, %ecx": ("%rcx", "%rax")}
    counter, base = counters[lines[i]]
    address = re.fullmatch(r"leaq\s+([.\w]+)\(%rip\), " + base, lines[i+1])
    require(address, lines[i+1])
    table = re.search(r"^" + re.escape(address[1]) + r':\n\s+\.ascii\s+("[^\n]*")\n\s+\.size\s+' +
                      re.escape(address[1]) + r", 192$", asm, re.M)
    require(table, "missing round table")
    data = ast.literal_eval("b" + table[1])
    require(len(data) == 192, "invalid round table")
    if lines[i+2].startswith(".p2align"):
        i += 1
    label = lines[i+2]
    require(re.fullmatch(r"\.LBB\d+_\d+:", label), label)
    i += 3
    state = {key: f"a[{index}]!" for key, index in slots.items()}
    spills = {}

    def read(arg):
        if arg.startswith("%"):
            return state[reg(arg)]
        if arg == f"({counter},{base}){{1to8}}":
            return "rc"
        offset = stack(arg)
        return spills[offset]

    def stack(arg):
        match = re.fullmatch(r"(-\d+)\(%rsp\)", arg)
        require(match, arg)
        offset = int(match[1])
        require(-128 <= offset <= -64, arg)
        return offset

    while not lines[i].startswith("addq"):
        op, operands = lines[i].split(None, 1)
        args = operands.split(", ")
        if op in ("vmovdqa64", "vmovdqu64"):
            source, dest = args
            if "(%rsp)" in dest:
                offset = stack(dest)
                require(all(x == offset or abs(x-offset) >= 64 for x in spills), "overlapping spill")
                spills[offset] = read(source)
            else:
                state[reg(dest)] = read(source)
        else:
            dest = reg(args[-1])
            if op == "vpternlogq":
                imm, c, b, _ = args
                require(imm in ("$150", "$210"), imm)
                expr = f"X86.ternary {imm[1:]} {read(dest)} {read(b)} {read(c)}"
            elif op == "vprolq":
                imm, source, _ = args
                require(re.fullmatch(r"\$\d+", imm), imm)
                expr = f"({read(source)}).rotateLeft {int(imm[1:]) % 64}"
            elif op == "vpxorq":
                left, right, _ = args
                expr = f"{read(right)} ^^^ {read(left)}"
            else:
                raise ValueError(lines[i])
            state[dest] = f"({expr})"
        i += 1
    require(lines[i:i+3] == [f"addq\t$8, {counter}", f"cmpq\t$192, {counter}", "jne\t"+label[:-1]], "unexpected loop")
    i += 3
    result = {}
    while lines[i].startswith("vmovdqu64"):
        source, dest = lines[i].split(None, 1)[1].split(", ")
        index = matrix(dest)
        require(slots[reg(source)] == index and index not in result, "loop/store lane mismatch")
        result[index] = read(source)
        i += 1
    require(len(result) == 25 and lines[i:i+2] == ["vzeroupper", "retq"], "incomplete state store")
    require(len(lines) == i+4 and re.fullmatch(r"\.Lfunc_end\d+:", lines[i+2]) and
            lines[i+3] == f".size\t{symbols[0]}, {lines[i+2][:-1]}-{symbols[0]}", "unexpected epilogue")
    constants = [str(int.from_bytes(data[i:i+8], "little")) for i in range(0, len(data), 8)]
    return "\n".join(["-- Generated from the x86-64 Linux release assembly by scripts/check-keccak-assembly.py.",
        "import Platform.Rounds", "import Spec.Shake256", "namespace slhdsa.KeccakAsm", "open Spec.Keccak",
        *[f"def word{j} (a : State) (rc : Lane) : Lane := {result[j]}" for j in range(25)],
        "def roundCode (a : State) (rc : Lane) : State := #[" + ",".join(f"word{j} a rc" for j in range(25)) + "]",
        "def constants : Array Lane := #["+",".join(constants)+"]",
        "def permutation (a : State) := constants.foldl roundCode a", "end slhdsa.KeccakAsm", ""])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("assembly", type=Path)
    parser.add_argument("lean_output", type=Path)
    options = parser.parse_args()
    options.lean_output.write_text(translate(options.assembly.read_text()))
