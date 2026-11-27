#!/usr/bin/env python3
"""Enumerate finite pool event projections in herdtools7's RC11 model."""
import argparse
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SUITE = ROOT / "scripts/parallel-proof/pool"
# Each C atomic event is copied from the corresponding operation on the Rust
# fast path. job and used are relaxed observation markers: observing stale
# values indicates a missing happens-before edge without introducing C data races.
BINDINGS = {
    "atomic_store_explicit(remaining, 2,": "pool.remaining.store(n_workers*2,Ordering::Relaxed)",
    "atomic_exchange_explicit(slot, 2,": "slot.state.swap(WORK_PENDING,Ordering::AcqRel)",
    "atomic_load_explicit(remaining,": "self.pool.remaining.load(Ordering::Acquire)",
    "atomic_store_explicit(busy, 0,": "self.pool.busy.store(false,Ordering::Release)",
    "atomic_load_explicit(slot,": "slot.state.load(Ordering::Acquire)",
    "atomic_store_explicit(slot, 0,": "slot.state.store(IDLE_SPIN,Ordering::Release)",
    "atomic_fetch_sub_explicit(remaining, 2,": "pool.remaining.fetch_sub(2,Ordering::SeqCst)",
    "atomic_fetch_or_explicit(remaining, 1,": "pool.remaining.fetch_or(1,Ordering::Relaxed)",
    "atomic_compare_exchange_strong_explicit(busy, expected, 1,":
        ".compare_exchange(false,true,Ordering::Acquire,Ordering::Relaxed)",
}
ORDER = {"Relaxed": "relaxed", "Release": "release", "Acquire": "acquire",
         "AcqRel": "acq_rel", "SeqCst": "seq_cst"}

SUCCESSES = {
    "reuse": "1:first=1 /\\ 1:second=2 /\\ 2:seen=1",
    "reset-publish": "1:value=1 /\\ 0:join=0 /\\ 0:done=1",
    "panic-release-sequence": "0:old=4 /\\ 1:before=2 /\\ 1:old=3 /\\ 2:join=1 /\\ 2:a=1 /\\ 2:b=1",
}
MUTANTS = {
    "reuse": [
        ("atomic_store_explicit(busy, 0, memory_order_release)", "atomic_store_explicit(busy, 0, memory_order_relaxed)"),
        ("atomic_store_explicit(slot, 0, memory_order_release);", ""),
    ],
    "reset-publish": [
        ("atomic_store_explicit(remaining, 2, memory_order_relaxed);", ""),
        ("atomic_exchange_explicit(slot, 2, memory_order_acq_rel)", "atomic_exchange_explicit(slot, 2, memory_order_relaxed)"),
    ],
    "panic-release-sequence": [
        ("atomic_load_explicit(remaining, memory_order_acquire)", "atomic_load_explicit(remaining, memory_order_relaxed)"),
    ],
}


def run(binary, libdir, path, content, want):
    path.write_text(content)
    args = [binary] + (["-I", libdir] if libdir else []) + ["-model", "rc11.cat", str(path)]
    output = subprocess.run(args, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=120).stdout
    if not re.search(r"^Observation \w+ " + want + r" \d+ \d+$", output, re.M):
        raise ValueError(f"expected {want} for {path.name}\n{output}")


def signing_phase(binary, libdir, folder):
    # Relaxed observation markers isolate the edge contributed by the phase
    # protocol. Production OnceLock operations have additional guarantees.
    rust = re.sub(r"//[^\n]*|\s+", "", (ROOT / "rust/src/slh/parallel.rs").read_text())
    sites = ["ifphase1_done.fetch_add(1,Ordering::AcqRel)+1==total_phase1{",
             "let_=roots_cell.set(roots);", "phase2_state.store(PHASE2_READY,Ordering::Release);",
             "letst=phase2_state.load(Ordering::Acquire);ifst==PHASE2_READY{break;}",
             'letroots=roots_cell.get().expect("rootsready");']
    if any(rust.count(site) != 1 for site in sites) or [rust.index(s) for s in sites] != sorted(rust.index(s) for s in sites):
        raise ValueError("review phase-one reduction and phase-two publication order")
    path = folder / "signing-phase.litmus"
    model = (SUITE / path.name).read_text()
    run(binary, libdir, path, model, "Never")
    good = r"exists (0:first=0 /\ 1:last=1 /\ 1:reduced=1 /\ 2:seen=1 /\ 2:input=1)"
    run(binary, libdir, path, model.split("exists (")[0] + good + "\n", "Sometimes")
    for line in ("first = atomic_fetch_add_explicit(done, 1, memory_order_acq_rel)",
                 "last = atomic_fetch_add_explicit(done, 1, memory_order_acq_rel)",
                 "atomic_store_explicit(ready, 1, memory_order_release)",
                 "atomic_load_explicit(ready, memory_order_acquire)"):
        if model.count(line) != 1:
            raise ValueError(f"missing phase event {line}")
        mutant = re.sub(r"memory_order_\w+", "memory_order_relaxed", line)
        run(binary, libdir, path, model.replace(line, mutant), "Sometimes")
    print("signing phases: stale reads excluded, successful path and four weakened-order controls witnessed", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--herd", default="herd7", help="herdtools7 executable (tested on 7.58)")
    parser.add_argument("--libdir", help="model directory for an uninstalled build")
    args = parser.parse_args()
    rust = re.sub(r"//[^\n]*|\s+", "", (ROOT / "rust/src/pool.rs").read_text().split("#[cfg(test)]")[0])
    seen = set()
    with tempfile.TemporaryDirectory() as tmp:
        runpy.run_path(str(ROOT / "scripts/check-parallel-once-publish.py"))["check"](args.herd, args.libdir, Path(tmp), run)
        signing_phase(args.herd, args.libdir, Path(tmp))
        for name, positive in SUCCESSES.items():
            base = (SUITE / (name + ".litmus")).read_text()
            for event in re.findall(r"atomic_\w+_explicit\([^);]+\)", base):
                if event.startswith(("atomic_store_explicit(job,", "atomic_load_explicit(job,",
                                     "atomic_store_explicit(used", "atomic_load_explicit(used")):
                    if not event.endswith("memory_order_relaxed)"):
                        raise ValueError(f"observation marker provides synchronization: {event}")
                    continue
                [start] = [key for key in BINDINGS if event.startswith(key)]
                site = BINDINGS[start]
                orders = [ORDER[i] for i in re.findall(r"Ordering::(\w+)", site)]
                if site not in rust or orders != re.findall(r"memory_order_(\w+)", event):
                    raise ValueError(f"atomic order differs from production: {event}")
                seen.add(start)
            path = Path(tmp) / (name + ".litmus")
            run(args.herd, args.libdir, path, base, "Never")
            run(args.herd, args.libdir, path, base.split("exists (")[0] + f"exists ({positive})\n", "Sometimes")
            for before, after in MUTANTS[name]:
                if base.count(before) != 1:
                    raise ValueError(f"ambiguous mutant: {before}")
                run(args.herd, args.libdir, path, base.replace(before, after), "Sometimes")
            print(f"{name}: forbidden outcomes excluded, successful path and negative controls witnessed", flush=True)
    if seen != BINDINGS.keys():
        raise ValueError("unexercised production atomic bindings")


if __name__ == "__main__":
    main()
