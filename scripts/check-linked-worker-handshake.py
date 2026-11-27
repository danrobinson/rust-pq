#!/usr/bin/env python3
"""Check normal direct control flow and closure-field provenance of six Apple arm64 signing workers.

Calls follow the platform ABI and may return normally. This check models compiler
private spill slots and read-only closure captures. It does not model callee memory
effects, unwinding, speculative execution, or the Arm memory model.
"""

import argparse
from collections import deque
from dataclasses import dataclass
import hashlib
from pathlib import Path
import re
import subprocess
import tempfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


@dataclass(frozen=True)
class Insn:
    op: str
    args: str
    line: str

    @property
    def regs(self):
        return re.findall(r"\b[wx](\d+)\b", self.args)


def parse(dump):
    code = {}
    for line in dump.splitlines():
        m = re.match(r"^([0-9a-f]+):\s+(\S+)\s*(.*)", line)
        if m:
            code[int(m[1], 16)] = Insn(
                m[2], re.split(r"\s*[;<]", m[3])[0].strip(), line
            )
    require(
        code and list(code) == list(range(min(code), max(code) + 4, 4)),
        "non-contiguous disassembly",
    )
    return code


SUPPORTED = set(
    """add add.4s adds adrp and b b.eq b.gt b.hi b.hs b.lo b.ls b.lt
    b.mi b.ne bl brk cas cbnz cbz ccmp cinc cmn cmp csel dup.4s eor eor.16b fmov isb
    ld1.s ldadd ldaddal ldapr ldaprb ldapur ldp ldr ldrb ldrh ldur ldurb lsl lsr
    madd mov mov.s movi.4s mul neg.4s ret stlrb stp str strb stur sturb sub subs tbnz
    tst umaddl umulh ushl.4s""".split()
)


def successors(pc, ins):
    require(ins.op in SUPPORTED, f"unmodeled instruction {ins.op}")
    if ins.op in ("ret", "brk"):
        return []
    if (
        ins.op == "b"
        or ins.op.startswith("b.")
        or ins.op in ("tbnz", "tbz", "cbz", "cbnz")
    ):
        target = int(ins.args.split()[-1], 16)
        return [target] if ins.op == "b" else [target, pc + 4]
    return [pc + 4]


def stack_slot(offset):
    return ("spill", offset)


def provenance(code, edges):
    # Values are frame/closure addresses, individual capture pointers, and 1.
    # Joins retain a fact only if all predecessors agree. Unknown destinations
    # lose their fact. Stack slots are addressed relative to entry SP.
    states = {min(code): {"0": ("env", 0), "sp": ("stack", 0)}}
    work = deque(states)
    while work:
        pc = work.popleft()
        ins, before = code[pc], states[pc]
        state = dict(before)
        op, args, regs = ins.op, ins.args, ins.regs
        mem = re.search(r"\[(sp|x\d+)(?:, #(-?0x[0-9a-f]+))?\](!?)", args)
        if mem:
            reg = mem[1].removeprefix("x")
            base = before.get(reg)
            offset = int(mem[2] or "0", 0)
            if base and base[0] in ("stack", "env"):
                addr = (base[0], base[1] + offset)
            else:
                addr = None

            def read(i):
                if addr and addr[0] == "env":
                    return ("capture", addr[1] + 8 * i)
                if addr and addr[0] == "stack":
                    return before.get(stack_slot(addr[1] + 8 * i))

            if op in ("ldp", "ldr", "ldur") and args.startswith("x"):
                for i, dest in enumerate(regs[:2] if op == "ldp" else regs[:1]):
                    state[dest] = read(i)
            elif op in ("str", "stp", "stur", "strb", "sturb"):
                if addr and addr[0] == "stack":
                    srcs = args.split("[")[0].strip(", ").split(", ")
                    for i, src in enumerate(srcs):
                        key = stack_slot(addr[1])
                        width = {"x": 8, "w": 4, "q": 16, "d": 8, "s": 4, "b": 1}.get(
                            src[0], 16
                        )
                        if op in ("strb", "sturb"):
                            width = 1
                        start = key[1] + i * width
                        for k in list(state):
                            if (
                                isinstance(k, tuple)
                                and k[0] == "spill"
                                and k[1] < start + width
                                and start < k[1] + 8
                            ):
                                del state[k]
                        if src.startswith("x") and width == 8:
                            state[stack_slot(start)] = before.get(src[1:])
            elif op in ("ldadd", "ldaddal"):
                state.pop(regs[1], None)
            elif op.startswith(("ld", "cas")) and regs and args.startswith(("x", "w")):
                state.pop(regs[0], None)
            if mem[3] and addr:
                state[reg] = addr
        elif op == "bl":
            for r in range(19):
                state.pop(str(r), None)
        elif op == "mov" and args.startswith(("x", "w")):
            state[regs[0]] = (
                ("one", 1)
                if args.endswith("#0x1")
                else (
                    before.get(regs[1])
                    if args.startswith("x") and len(regs) == 2
                    else None
                )
            )
        elif op in ("sub", "add") and (
            m := re.fullmatch(r"(sp|x\d+), (sp|x\d+), #(0x[0-9a-f]+)", args)
        ):
            dest, src = (v.removeprefix("x") for v in (m[1], m[2]))
            val = before.get(src)
            state[dest] = (
                (val[0], val[1] + (1 if op == "add" else -1) * int(m[3], 0))
                if val and val[0] in ("env", "stack")
                else None
            )
        elif (
            op not in ("cmp", "cmn", "ccmp", "tst")
            and not op.startswith(("b", "cb", "tb"))
            and regs
            and args.startswith(("x", "w"))
        ):
            state.pop(regs[0], None)
        state = {k: v for k, v in state.items() if v is not None}
        for target in edges[pc]:
            if target not in code:  # tail transfer exits this function
                continue
            old = states.get(target)
            joined = (
                state
                if old is None
                else {k: v for k, v in old.items() if state.get(k) == v}
            )
            if joined != old:
                states[target] = joined
                work.append(target)
    return states


def check(code):
    edges = {pc: successors(pc, ins) for pc, ins in code.items()}
    states = provenance(code, edges)

    def sites(op):
        return [pc for pc in code if code[pc].op == op]

    def value(pc, r):
        return states.get(pc, {}).get(r)

    def capture(pc, r, offset):
        require(
            value(pc, r) == ("capture", offset),
            f"capture {offset:#x} at {pc:#x} is {value(pc, r)}",
        )

    def one(pc, r):
        require(
            value(pc, r) == ("one", 1),
            f"increment or READY payload at {pc:#x} is {value(pc, r)}",
        )

    def ready_edge(pc, branch):
        dest = code[pc].regs[0]
        require(
            code[pc + 4].args == f"w{dest}, #0x1"
            and code[pc + 4].op == "cmp"
            and branch in ("b.eq", "b.ne"),
            "acquire must test READY",
        )
        return pc + 8, edges[pc + 8][branch == "b.ne"]

    loads = sites("ldaprb")
    pubs = sites("stlrb")
    done = sites("ldaddal")
    require(len(loads) == 4 and len(pubs) == 1 and done, "missing state operations")
    for pc in loads:
        capture(pc, code[pc].regs[1], 0)
    pub = pubs[0]
    capture(pub, code[pub].regs[1], 0)
    one(pub, code[pub].regs[0])
    require(
        code[pub + 8].op == "bl" and "Condvar10notify_all" in code[pub + 8].line,
        "release must precede condition notification",
    )
    grants = {ready_edge(pc, code[pc + 8].op) for pc in (loads[0], loads[1], loads[3])}
    require(
        code[loads[2] + 4].op == "cbnz" and edges[loads[2] + 4][0] == loads[3],
        "parked wake must recheck state",
    )
    winners = set()
    for pc in done:
        src, old, ptr = code[pc].regs
        capture(pc, ptr, 0x80)
        one(pc, src)
        require(
            code[pc + 4].op == "add" and code[pc + 4].args == f"x{old}, x{old}, #0x1",
            "completion count must increment",
        )
        total, ref = code[pc + 8].regs
        capture(pc + 8, ref, 0x88)
        require(
            code[pc + 8].op == "ldr"
            and code[pc + 8].args == f"x{total}, [x{ref}]"
            and code[pc + 12].op == "cmp"
            and code[pc + 12].args == f"x{old}, x{total}",
            "last finisher comparison",
        )
        branch = code[pc + 16].op
        require(branch in ("b.eq", "b.ne"), "last finisher must test equality")
        winners.add((pc + 16, edges[pc + 16][branch == "b.ne"]))
    claims = []
    for pc in sites("ldadd"):
        src, old, ptr = code[pc].regs
        if value(pc, ptr) == ("capture", 0x18):  # phase-one work cursor
            continue
        capture(pc, ptr, 0xE8)
        one(pc, src)
        size, table = code[pc + 4].regs
        capture(pc + 4, table, 0xF0)
        require(
            code[pc + 4].op == "ldr"
            and code[pc + 4].args == f"x{size}, [x{table}, #0x10]"
            and code[pc + 8].op == "cmp"
            and code[pc + 8].args == f"x{old}, x{size}"
            and code[pc + 12].op in ("b.hs", "b.lo"),
            "ticket must be range checked",
        )
        claims.append(pc)
    require(len(claims) == 2, "missing phase-two ticket site")
    return edges, winners, pub, grants, claims


def cut_graph(edges, grants, targets):
    """Contract straight-line runs; every grant and every sink remains visible."""
    entry = min(edges)
    incoming = {pc: 0 for pc in edges}
    leaders = {entry, *targets}
    for pc, dests in edges.items():
        for dest in dests:
            if dest in incoming:
                incoming[dest] += 1
                if dests != [pc + 4]:
                    leaders.add(dest)
    leaders.update(pc for pc, degree in incoming.items() if degree != 1)
    blocks = {}
    for leader in sorted(leaders):
        pc = leader
        while edges[pc] == [pc + 4] and pc + 4 in edges and pc + 4 not in leaders:
            require((pc, pc + 4) not in grants, "hidden granting edge")
            pc += 4
        blocks[leader] = [(d, (pc, d) in grants) for d in edges[pc] if d in edges]

    def reachable(allow):
        reached = {entry}
        work = [entry]
        while work:
            for dest, grant in blocks[work.pop()]:
                if (allow or not grant) and dest not in reached:
                    reached.add(dest)
                    work.append(dest)
        return reached

    unrestricted = reachable(True)
    restricted = reachable(False)
    require(
        all(t in unrestricted and t not in restricted for t in targets),
        "missing control-flow cut or unreachable target",
    )

    def label(pc):
        return ((pc - entry) // 4) * 2 + int(pc not in restricted)

    return (
        [
            (label(pc), label(d), grant)
            for pc, exits in blocks.items()
            for d, grant in exits
        ],
        label(entry),
        list(map(label, targets)),
    )


def certificate(name, graph):
    edges, start, targets = graph
    rows = ",\n".join(f"⟨{u},{v},{str(g).lower()}⟩" for u, v, g in edges)
    lines = [
        f"private def {name} : List Edge := [{rows}]",
        f"private theorem {name}_checked : {name}.all preserves=true := by decide",
    ]
    for i, target in enumerate(targets):
        lines.append(
            f"theorem {name}_sink{i} : ¬ WithoutGrant {name} {start} {target} := must_cross _ {name}_checked (by decide) (by decide)"
        )
    return "\n".join(lines)


def graphs(code):
    edges, winners, pub, grants, claims = check(code)
    return cut_graph(edges, winners, [pub]), cut_graph(edges, grants, claims)


def mutation_controls(code):
    edges, winners, pub, ready, claims = check(code)
    load = min(ready)[0] - 8
    branch = min(winners)[0]
    tests = [
        (load, "ldrb", code[load].args),
        (pub, "strb", code[pub].args),
        (branch, "b.ne" if code[branch].op == "b.eq" else "b.eq", code[branch].args),
        (
            load + 8,
            "b.ne" if code[load + 8].op == "b.eq" else "b.eq",
            code[load + 8].args,
        ),
        (claims[0], "ldadd", re.sub(r"\[x\d+\]", "[x0]", code[claims[0]].args)),
    ]
    for pc, op, args in tests:
        changed = dict(code)
        changed[pc] = Insn(op, args, code[pc].line)
        try:
            graphs(changed)
        except ValueError:
            continue
        raise ValueError(f"accepted altered {code[pc].op} at {pc:#x}")


def arm_litmus(binary, libdir, root, tmp):
    # Project the verified opcodes into two publishers and one reader. The
    # two payload markers separate the completion sequence and READY handoff.
    source = (
        root / "scripts/parallel-proof/pool/linked-worker-arm64.litmus"
    ).read_text()
    root_stale = source.replace("X6=0", "X8=0")
    cases = [
        (source, "Never"),
        (root_stale, "Never"),
        (source.replace("X6=0", r"X6=1 /\ 2:X8=1"), "Sometimes"),
        (source.replace("LDADDAL X3,X4,[X1]  |", "LDADD X3,X4,[X1]    |"), "Sometimes"),
        (root_stale.replace("STLRB", "STRB"), "Sometimes"),
        (root_stale.replace("LDAPRB", "LDRB"), "Sometimes"),
    ]
    path = tmp / "Handshake.litmus"
    for content, want in cases:
        path.write_text(content)
        cmd = (
            [binary]
            + (["-I", libdir] if libdir else [])
            + ["-model", "aarch64.cat", path]
        )
        out = subprocess.check_output(
            cmd, stderr=subprocess.STDOUT, text=True, timeout=120
        )
        require(
            re.search(
                r"^Observation LinkedWorkerHandshake " + want + r" \d+ \d+$", out, re.M
            ),
            out,
        )
    print(
        "Arm memory model checked two stale payloads, the successful handoff, and three weakened instructions"
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument(
        "--herd",
        help="also run the three-thread Arm memory model projection with this herd7 executable",
    )
    parser.add_argument("--libdir", help="herd7 model library directory")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    root = Path(__file__).resolve().parents[1]
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp = Path(tmpdir)
        binary = tmp / "consumer"
        binary.write_bytes(data)
        nm = subprocess.check_output(["nm", "-n", binary], text=True)
        symbols = [
            (int(m[1], 16), m[2])
            for m in re.finditer(r"^([a-f0-9]+) [tT] (\S+)$", nm, re.M)
        ]
        sources = [
            "import Parallel.LinkedWorkerCut",
            "open slhdsa.LinkedWorkerCut",
            "set_option maxRecDepth 10000",
            "set_option maxHeartbeats 3000000",
        ]
        found = set()
        for i, (pc, symbol) in enumerate(symbols):
            match = re.fullmatch(
                r"__RNCINv.+6slhdsa(5shake)?3slh8parallel4signKj(10|18|20)_Es4_0B\w+_",
                symbol,
            )
            if not match:
                continue
            name = ("shake" if match[1] else "sha2") + str(int(match[2], 16))
            require(name not in found, "duplicate worker " + name)
            found.add(name)
            dis = subprocess.check_output(
                [
                    "xcrun",
                    "llvm-objdump",
                    "-d",
                    "--no-show-raw-insn",
                    f"--start-address={pc}",
                    f"--stop-address={symbols[i + 1][0]}",
                    binary,
                ],
                text=True,
            )
            code = parse(dis)
            require(
                min(code) == pc and max(code) + 4 == symbols[i + 1][0],
                "unexpected worker extent",
            )
            last, ready = graphs(code)
            if args.self_test:
                mutation_controls(code)
            sources.extend(
                [certificate(name + "Last", last), certificate(name + "Ready", ready)]
            )
            print(
                f"{name}: {len(last[0])} completion-cut edges, {len(ready[0])} readiness-cut edges",
                flush=True,
            )
        require(
            found == {f + n for f in ("sha2", "shake") for n in ("16", "24", "32")},
            "expected six linked worker specializations",
        )
        subprocess.run(
            ["lake", "build", "Parallel.LinkedWorkerCut"],
            cwd=root / "lean-hw",
            check=True,
        )
        source = tmp / "Witness.lean"
        source.write_text("\n".join(sources))
        subprocess.run(
            ["lake", "env", "lean", source], cwd=root / "lean-hw", check=True
        )
        if args.herd:
            arm_litmus(args.herd, args.libdir, root, tmp)
        print(
            "Kernel-checked worker control-flow cuts for image SHA-256",
            hashlib.sha256(data).hexdigest(),
        )


if __name__ == "__main__":
    main()
