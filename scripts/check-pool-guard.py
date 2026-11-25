#!/usr/bin/env python3
"""Kernel-check all paths in the pinned rustc MIR of PoolGuard::drop."""
import argparse
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
FACADE = runpy.run_path(str(ROOT / "scripts/check-platform-facade.py"))


def one(pattern, text):
    matches = list(re.finditer(pattern, text))
    if len(matches) != 1:
        raise ValueError(f"expected one MIR match for {pattern}; found {len(matches)}")
    return matches[0]


def graph_from_mir(mir, source):
    # MIR projects fields by ordinal. Recover these from the same crate, and
    # verify the address-producing instructions, not just the atomic call names.
    struct = source.split("struct Pool {", 1)[1].split("\n}", 1)[0]
    fields = re.findall(r"(?m)^    (\w+):", struct)
    busy, job, remaining = (fields.index(k) for k in ("busy", "job", "remaining"))
    body = one(r"(?ms)^fn pool::<impl at src/pool.rs:[^\n]+>::drop\(_1: &mut PoolGuard<'_>\) -> \(\) \{(.*?)^\}", mir)[1]
    blocks = {int(k): " ".join(v.split()) for k, v in re.findall(r"    bb(\d+)(?: \(cleanup\))?: \{(.*?)\n    \}", body, re.S)}
    var = r"(_\d+)"
    def locate(pattern):
        [(k, match)] = [(k, match) for k, text in blocks.items() for match in re.finditer(pattern, text)]
        return k, match
    field = lambda i, ty: rf"{var} = no_retag copy \(\(\*_1\)\.0: &pool::Pool\); {var} = &\(\(\*\1\)\.{i}: {ty}\); "
    read, load = locate(field(remaining, r"core::sync::atomic::Atomic<usize>") +
                        rf"{var} = core::sync::atomic::Ordering::Acquire; {var} = Atomic::<usize>::load\(move \2, move \3\) -> \[return: bb(\d+), unwind continue\];")
    test = int(load[5])
    compare = re.fullmatch(rf"{var} = Lt\(copy {load[4]}, const 2_usize\); switchInt\(move \1\) -> \[0: bb(\d+), otherwise: bb(\d+)\];", blocks[test])
    if not compare:
        raise ValueError("changed low-count exit condition")
    low = int(compare[3])
    if [i for i, body in blocks.items() if test in map(int, re.findall(r"\bbb(\d+)\b", body))] != [read]:
        raise ValueError("low check bypasses the acquire load")
    get, pointee = locate(field(job, r"core::cell::UnsafeCell<core::option::Option<pool::Job>>") +
                          rf"{var} = UnsafeCell::<Option<pool::Job>>::get\(move \2\)")
    none = one(r"(_\d+) = Option::<pool::Job>::None;", blocks[get])[1]
    for local in (pointee[3], none):
        one(rf"(?m)^        {local} = ", body)
    clear, _ = locate(rf"^\(\*{pointee[3]}\) = move {none};")
    if len(re.findall(r"\(\*_\d+\) = ", body)) != 1:
        raise ValueError("unexpected raw write in the destructor")
    release, store = locate(field(busy, r"core::sync::atomic::Atomic<bool>") +
                            rf"{var} = core::sync::atomic::Ordering::Release; _\d+ = Atomic::<bool>::store\(move \2, const false, move \3\) -> \[return: bb(\d+), unwind continue\];")
    ret, _ = locate(r"^return;$")
    panic, _ = locate(r"panic_fmt\([^;]+\) -> unwind continue;")
    edges = []
    synthetic = max(blocks) + 1
    # Exceptional calls can leave before returning. Such unwind suffixes, and
    # compiler-inserted aborts, are deliberately not labeled completed drops.
    for pc, text in blocks.items():
        targets = list(map(int, re.findall(r"\bbb(\d+)\b", text)))
        if any(dst not in blocks for dst in targets):
            raise ValueError("unknown MIR successor")
        if pc in (ret, panic):
            edges.append((pc, "finish", synthetic))
            synthetic += 1
        origin = pc
        if pc == clear:
            edges.append((pc, "clearJob", synthetic))
            origin, synthetic = synthetic, synthetic + 1
        for dst in targets:
            name = "other"
            if pc == test and dst == low:
                name = "acquiredLow"
            if pc == release and dst == int(store[4]):
                name = "releaseBusy"
            edges.append((origin, name, dst))
    return edges, read, low, ret


def certificate(edges):
    # Synthesize a convenient overapproximation; Lean checks the certificate.
    sequence = ("waiting", "joined", "cleared", "released", "finished")
    actions = ("acquiredLow", "clearJob", "releaseBusy", "finish")
    states, todo = {(0, "waiting")}, [(0, "waiting")]
    while todo:
        pc, phase = todo.pop()
        for origin, action, dst in edges:
            if pc != origin:
                continue
            nxt = phase if action == "other" else "bad"
            if action in actions and phase == sequence[actions.index(action)]:
                nxt = sequence[actions.index(action) + 1]
            if (dst, nxt) not in states:
                states.add((dst, nxt))
                todo.append((dst, nxt))
    return sorted(states)


def check_instance(edges, path, *, rejected=False):
    graph = ",".join(f"({x},.{a},{y})" for x, a, y in edges)
    states = ",".join(f"({x},.{p})" for x, p in certificate(edges))
    path.write_text(f"""import Parallel.PoolGuard
open ParallelPool.Guard
def cfg : List Edge := [{graph}]
def invariant : Certificate := [{states}]
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
theorem valid : check cfg invariant = true := by decide
theorem order {{pc p history}} (path : Walk cfg pc p history) :
    p ≠ .bad ∧ history.filter (· != .other) = events p := walk_order valid path
def workers := @clears_after_workers cfg invariant valid
theorem complete {{pc p history dst}} (path : Walk cfg pc p history) (exitEdge : (pc,.finish,dst) ∈ cfg) :
    history.filter (· != .other) = [.releaseBusy,.clearJob,.acquiredLow] := exit_order valid path exitEdge
""")
    result = subprocess.run(["lake", "env", "lean", path], cwd=ROOT / "lean-hw", text=True, capture_output=True)
    if rejected:
        if not result.returncode or "proved that the proposition" not in result.stdout.lower():
            raise ValueError(f"expected kernel rejection of a bypass: {result.stdout}{result.stderr}")
    elif result.returncode:
        raise ValueError(result.stdout + result.stderr)


def check(mir, source, scratch):
    edges, read, low, ret = graph_from_mir(mir, source)
    check_instance(edges, scratch / "GuardCertificate.lean")
    for name, origin, target in (("BypassJoin", read, low), ("ReturnBeforeRelease", low, ret)):
        check_instance(edges + [(origin, "other", target)], scratch / (name + ".lean"), rejected=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="nightly-2026-09-17")
    args = parser.parse_args()
    FACADE["run"](["lake", "build", "Parallel.PoolGuard"], ROOT / "lean-hw")
    FACADE["audit_theorems"]("Parallel.PoolGuard", ["ParallelPool.Guard.walk_order", "ParallelPool.Guard.exit_order",
                                                  "ParallelPool.Guard.clears_after_workers"])
    with tempfile.TemporaryDirectory() as directory:
        scratch = Path(directory)
        mir = scratch / "pool.mir"
        subprocess.run(["cargo", "+" + args.toolchain, "rustc", "--locked", "--features", "parallel",
                        "--lib", "--", "-C", "panic=unwind", "--emit=mir=" + str(mir)], cwd=ROOT / "rust", check=True)
        check(mir.read_text(), (ROOT / "rust/src/pool.rs").read_text(), scratch)
    print("Lean checked all guard MIR paths and rejected missing-join and early-return edges.")


if __name__ == "__main__":
    main()
