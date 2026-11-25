#!/usr/bin/env python3
"""Check pinned, optimized OnceLock getter and constructor probes for signer cell types."""
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
ROOT, LEAN = facade["ROOT"], facade["LEAN"]
TYPES = {**{f"array{n}": (f"[u8;{n}]", n) for n in (16, 24, 32)},
         "bytes": ("Vec<u8>", 24),
         **{f"rows{n}": (f"Vec<[u8;{n}]>", 24) for n in (16, 24, 32)}}
TARGETS = ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu")


def body(ir, symbol):
    alias = re.search(rf"^@{symbol} = .*? alias .*?ptr @(\w+)$", ir, re.M)
    if alias:
        symbol = alias[1]
    match = re.search(rf"^define [^\n]* @{symbol}\([^\n]*\{{\nstart:\n(.*?)^\}}", ir, re.M | re.S)
    if not match:
        raise ValueError(f"missing probe {symbol}")
    return match[1].strip()


def check(ir, target, name, size):
    apple = target.startswith("aarch64-apple")
    width = 8 if apple else 4
    flag, payload = (0, 8) if apple and size == 24 else (size, 0)
    scalar, zero = ("ptr", "null") if apple else ("i32", "0")
    # Recognize every instruction and its SSA operands. Constructor and getter
    # use independent LLVM values for their pointers; bind each in its own body.
    def gep(base, offset):
        return rf"(?P<addr>%[\w.]+) = getelementptr inbounds nuw i8, ptr {base}, i64 {offset}\s+"
    fptr = r"(?P=addr)" if flag else "%x"
    pptr = r"(?P=addr)" if payload else "%x"
    align = max(width, 8 if "array" not in name else 1)
    load = rf"(?P<tag>%[\w.]+) = load atomic {scalar}, ptr {fptr} acquire, align {align}\s+"
    cmp = rf"(?P<eq>%[\w.]+) = icmp eq {scalar} (?P=tag), {zero}\s+"
    select = rf"(?P<ref>%[\w.]+) = select i1 (?P=eq), ptr {pptr}, ptr null\s+ret ptr (?P=ref)"
    getter = (gep("%x", flag) if flag else "") + load + cmp + (gep("%x", payload) if payload else "") + select
    empty = (gep("%_0", flag) if flag else "") + rf"store i{8*width} 3, ptr {fptr.replace('%x','%_0')}, align {align}\s+ret void"
    init = (gep("%_0", flag) if flag else "") + rf"store i{8*width} 0, ptr {fptr.replace('%x','%_0')}, align {align}\s+"
    init += (gep("%_0", payload) if payload else "")
    init += (rf"tail call void @llvm\.memcpy\.p0\.p0\.i64\(ptr noundef nonnull align \d+ dereferenceable\({size}\) {pptr.replace('%x','%_0')}, "
             rf"ptr noundef nonnull align \d+ dereferenceable\({size}\) %x, i64 {size}, i1 false\)\s+ret void")
    for prefix, pattern in (("get_", getter), ("empty_", empty), ("full_", init)):
        if not re.fullmatch(pattern, body(ir, prefix + name)):
            raise ValueError(f"{target} {prefix}{name} does not match the checked instructions")
    return f"example : (Layout.mk {flag} {width} {payload} {size}).separate := by decide"


def check_getter_assembly(assembly, target, name, size):
    symbol = ("_" if "apple" in target else "") + "get_" + name
    alias = re.search(rf"^{symbol} = (\w+)$", assembly, re.M)
    if alias:
        symbol = alias[1]
    match = re.search(rf"^{symbol}:\n(.*?)^\s*(retq?)\s*$", assembly, re.M | re.S)
    if not match:
        raise ValueError(f"missing getter instructions for {target} {symbol}")
    lines = [line.strip() for line in match[1].splitlines() if line.strip() and line.strip() != ".cfi_startproc"]
    if "apple" in target:
        if size == 24:
            ops = ["ldapr x8, [x0]", "add x9, x0, #8", "cmp x8, #0", "csel x0, x9, xzr, eq"]
        else:
            ops = [f"ldapur x8, [x0, #{size}]", "cmp x8, #0", "csel x0, x0, xzr, eq"]
    elif target.startswith("aarch64"):
        ops = [f"add x8, x0, #{size}", "ldar w8, [x8]", "cmp w8, #0", "csel x0, x0, xzr, eq"]
    else:
        ops = [f"movl {size}(%rdi), %ecx", "xorl %eax, %eax", "testl %ecx, %ecx", "cmoveq %rdi, %rax"]
    if [" ".join(line.split()) for line in lines] != ops or match[2] != ("retq" if target.startswith("x86") else "ret"):
        raise ValueError(f"unexpected getter instructions on {target} for {symbol}")


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".cargo/bin"), str(Path.home()/".elan/bin"), os.environ["PATH"]])
    toolchain = ROOT / ".tools/aeneas/charon/charon"
    module = "Parallel.OnceRead"
    facade["run"](["lake", "build", module], LEAN)
    examples = [f"import {module}", "open ParallelOnceRead"]
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp, "once.rs")
        definitions = ["use std::sync::OnceLock;"]
        for name, (ty, _) in TYPES.items():
            definitions.extend([
                f"#[no_mangle] pub fn get_{name}(x:&OnceLock<{ty}>)->Option<&{ty}> {{ x.get() }}",
                f"#[no_mangle] pub fn empty_{name}()->OnceLock<{ty}> {{ OnceLock::new() }}",
                f"#[no_mangle] pub fn full_{name}(x:{ty})->OnceLock<{ty}> {{ OnceLock::from(x) }}"])
        src.write_text("\n".join(definitions))
        for target in TARGETS:
            out = Path(tmp, target+".ll")
            asm = out.with_suffix(".s")
            subprocess.run(["rustc", "-O", "--crate-type=lib", f"--emit=llvm-ir={out},asm={asm}", "--target", target, src],
                           cwd=toolchain, check=True)
            ir, assembly = out.read_text(), asm.read_text()
            for name, (_, size) in TYPES.items():
                examples.append(check(ir, target, name, size))
                check_getter_assembly(assembly, target, name, size)
            for old, new in ((" acquire,", " monotonic,"), ("ret ptr %", "ret ptr null ; %"), ("i64 16, i1 false", "i64 15, i1 false")):
                try:
                    check(ir.replace(old, new), target, "array16", 16)
                except ValueError:
                    continue
                raise ValueError(f"undetected OnceLock mutation on {target}: {old}")
    facade["run"](["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(examples), text=True)
    facade["audit_theorems"](module, [f"ParallelOnceRead.{n}" for n in ("get_empty", "get_complete", "other_state")])
    print("Checked 21 hosted OnceLock layouts, getter and constructor probes, and 9 negative controls.")


if __name__ == "__main__":
    main()
