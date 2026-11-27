#!/usr/bin/env python3
"""Check the pool release-sequence theorem and exercise its edges on actual Rust."""
import argparse
import os
import re
from pathlib import Path
import runpy
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
POOL = Path("src/pool.rs")
TEST = "pool::tests::borrowed_jobs_cross_dispatchers_after_unwind"
# Each mutant removes a specific synchronizes-with edge. Never alter the checkout.
MUTATIONS = {
    "publish without release": (
        "slot.state.swap(WORK_PENDING, Ordering::AcqRel)",
        "slot.state.swap(WORK_PENDING, Ordering::Relaxed)",
    ),
    "poll without acquire": (
        "let s = slot.state.load(Ordering::Acquire);",
        "let s = slot.state.load(Ordering::Relaxed);",
    ),
    "retire without release": (
        "pool.remaining.fetch_sub(2, Ordering::SeqCst)",
        "pool.remaining.fetch_sub(2, Ordering::Relaxed)",
    ),
    "join without acquire": (
        "let state = self.pool.remaining.load(Ordering::Acquire);",
        "let state = self.pool.remaining.load(Ordering::Relaxed);",
    ),
    "release ownership without release": (
        "self.pool.busy.store(false, Ordering::Release);",
        "self.pool.busy.store(false, Ordering::Relaxed);",
    ),
    "claim ownership without acquire": (
        ".compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed)",
        ".compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)",
    ),
}


def miri(crate, toolchain, alias, seed):
    flags = f"-Zmiri-num-cpus=4 -Zmiri-preemption-rate=0.5 -Zmiri-seed={seed}"
    if alias == "tree":
        flags += " -Zmiri-tree-borrows"
    return subprocess.run(
        ["cargo", "+" + toolchain, "miri", "test", "--locked", "--features", "parallel",
         "--lib", TEST, "--", "--exact"],
        cwd=crate, env={**os.environ, "MIRIFLAGS": flags},
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, timeout=180,
    )


def check_cleanup_graph(mir):
    """Walk owned dispatch MIR, including rustc's unwind cleanup blocks."""
    body = mir.split("\nfn dispatch(", 1)[1].split("\n}\n", 1)[0]
    guard = re.search(r"debug _guard => (_\d+);", body)[1]
    blocks = dict(re.findall(r"    (bb\d+)(?: \(cleanup\))?: \{(.*?)\n    \}", body, re.S))
    [start] = [name for name, code in blocks.items() if f"{guard} = move " in code and "as Some" in code]
    pending = [(start, False)]
    visited = set()
    exits = set()
    caller_paths = set()
    while pending:
        name, dropped = pending.pop()
        if (name, dropped) in visited:
            continue
        visited.add((name, dropped))
        code = blocks[name]
        if f"drop({guard})" in code:
            if dropped:
                raise ValueError("second drop on an owned dispatch path")
            dropped = True
        if "<F as Fn<()>>::call" in code:
            if dropped or not re.search(r"<F as Fn<\(\)>>::call\(copy _4, const \(\)\)", code):
                raise ValueError("caller closure did not retain its borrow")
            caller_paths.add(name)
        if "const pool::WORK_PENDING" in code and dropped:
            raise ValueError("job published after dropping its guard")
        for exit_kind in ("return;", "resume;", "unwind continue"):
            if exit_kind in code:
                if not dropped:
                    raise ValueError(f"owned dispatch bypasses guard on {exit_kind} in {name}")
                exits.add(exit_kind)
        targets = re.findall(r"\b(bb\d+)\b", code)
        if not targets and not any(k in code for k in ("return;", "resume;", "unreachable;", "terminate(")):
            raise ValueError(f"unrecognized terminal block {name}")
        pending.extend((target, dropped) for target in targets)
    if len(caller_paths) != 1 or not {"return;", "resume;"} <= exits:
        raise ValueError("missing normal or unwind dispatch path")
    return guard


def compiler_checks(crate, toolchain, source):
    mir_file = crate.parent / "dispatch.mir"
    subprocess.run(["cargo", "+" + toolchain, "rustc", "--locked", "--features", "parallel", "--lib", "--",
                    "-C", "panic=unwind", "--emit=mir=" + str(mir_file)], cwd=crate, check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    mir = mir_file.read_text()
    runpy.run_path(str(ROOT / "scripts/check-pool-guard.py"))["check"](mir, source, crate.parent)
    guard = check_cleanup_graph(mir)
    # Remove just the destructor call from each exit's MIR, preserving its
    # normal successor. Both a normal bypass and a cleanup bypass must fail.
    start = mir.index("\nfn dispatch(")
    end = mir.index("\n}\n", start)
    fragment = mir[start:end]
    drops = list(re.finditer(rf"drop\({guard}\) -> \[return: (bb\d+), unwind [^\]]+\];", fragment))
    if len(drops) != 2:
        raise ValueError("expected one normal and one unwind guard destructor")
    for drop in drops:
        broken = fragment[:drop.start()] + f"goto -> {drop[1]};" + fragment[drop.end():]
        try:
            check_cleanup_graph(mir[:start] + broken + mir[end:])
        except ValueError as error:
            if "bypasses guard" not in str(error):
                raise
        else:
            raise ValueError("missing-drop mutant survived")

    # The guard's borrow must outlive its Drop even though it carries no raw
    # closure pointer of its own. Rustc should reject the premature move.
    probe = """
fn prematurely_drop_borrow(pool: &Pool) {
    let payload = alloc::vec![2u8; 4];
    let job = move || { std::hint::black_box(&payload); };
    let guard = PoolGuard::claim(pool, 1, false, &job);
    drop(job);
    drop(guard);
}
"""
    path = crate / POOL
    args = ["cargo", "+" + toolchain, "check", "--locked", "--features", "parallel", "--lib"]
    path.write_text(source + probe)
    rejected = subprocess.run(args, cwd=crate, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    if not rejected.returncode or "error[E0505]" not in rejected.stdout:
        raise ValueError(f"expected scoped move rejection: {rejected.stdout}")
    changed = source.replace("f: &'a F,", "f: &F,")
    if changed == source:
        raise ValueError("missing borrow binder")
    path.write_text(changed + probe)
    subprocess.run(args, cwd=crate, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)
    path.write_text(source)
    print("Rustc checked guard lifetime and normal/unwind MIR cleanup; negative controls passed", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", default="nightly-2026-09-17")
    args = parser.parse_args()
    facade = runpy.run_path(str(ROOT / "scripts/check-platform-facade.py"))
    facade["run"](["lake", "build", "Parallel.PoolGuard"], ROOT / "lean-hw")
    facade["audit_theorems"]("Parallel.PoolBorrow", [
        "ParallelPool.Borrow.busy_predecessor", "ParallelPool.Borrow.park_recheck",
        "ParallelPool.Borrow.spurious_recheck",
        "ParallelPool.Borrow.coherent_slot_source", "ParallelPool.Borrow.coherent_counter_source",
        "ParallelPool.Borrow.terminal_counter_source",
        "ParallelPool.Borrow.joined", "ParallelPool.Borrow.borrow_lifetime", "ParallelPool.Borrow.nonempty_reuse",
        "ParallelPool.Borrow.reuse", "ParallelPool.Borrow.job_cell_race_free",
    ])
    with tempfile.TemporaryDirectory() as temp:
        crate = Path(temp) / "rust"
        shutil.copytree(ROOT / "rust", crate, ignore=shutil.ignore_patterns("target", "*.llbc"))
        src = (crate / POOL).read_text()
        compiler_checks(crate, args.toolchain, src)
        for alias in ("stacked", "tree"):
            for seed in (0, 1):
                result = miri(crate, args.toolchain, alias, seed)
                if result.returncode or "1 passed" not in result.stdout:
                    raise RuntimeError(f"{alias} seed {seed}: {result.stdout}")
            print(f"Production borrowed-job test passed under {alias} borrows", flush=True)
        for name, (original, changed) in MUTATIONS.items():
            if src.count(original) != 1:
                raise ValueError(f"production operation changed: {name}")
            (crate / POOL).write_text(src.replace(original, changed))
            result = miri(crate, args.toolchain, "stacked", 0)
            if result.returncode == 0 or "Undefined Behavior: Data race" not in result.stdout:
                raise RuntimeError(f"{name}: expected Miri data-race report, got:\n{result.stdout}")
            print(f"Miri detected a data race: {name}", flush=True)


if __name__ == "__main__":
    main()
