#!/usr/bin/env python3
"""Replay cached signing with symbolic inputs and prove exact slot ownership for each sorted plan."""
import json
import os
import re
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(here / "parallel-proof"))
import signer

facade = runpy.run_path(str(here / "check-platform-facade.py"))
lean = facade["LEAN"]
base = facade["ROOT"]
slot = re.compile(r"\b(xmss|fors)_slots\[([^\]]+)\](\s*\.set\()")


def recording_probe():
    probe = signer.probe_source((base / "rust/src/cache.rs").read_text())
    for name in ("sha2", "shake"):
        mark = f"mod {name} {{"
        start = probe.index(mark, probe.index("mod cached {"))
        begin_original = probe.index("let cached_layers =",start)
        probe = probe[:begin_original]+"let initial_position = (tree,leaf);\n"+probe[begin_original:]
        # The generated module contains nested functions. Locate the ticket loop itself.
        begin = probe.index("let next = AtomicUsize::new(0);", start)
        join = probe.index("crate::pool::execute(active_workers, true, &fill);", begin)
        worker = probe[begin:join]
        edits = 0
        def record(match):
            nonlocal edits
            edits += 1
            family, index, write = match.groups()
            offset = "xmss_count" if family == "fors" else "0"
            return f"{family}_slots[{{ let slot = {index}; ledger.lock().unwrap()[id].push({offset}+slot); slot }}]{write}"
        worker = slot.sub(record, worker)
        if edits != (4 if name == "sha2" else 7):
            raise ValueError(f"review all {name} cached worker writes ({edits})")
        group = "1" if name == "sha2" else "group_w"
        start_ledger = "let ledger = std::sync::Mutex::new(vec![Vec::<usize>::new();jobs.len()]);\n"
        emit = f'\nprintln!("PLAN {name} {{}} {{}} {{}} {{}} {{}} {{}} {{:?}}", N,p.d,cached_layers,{group},xmss_count,fors_total_nodes,ledger.into_inner().unwrap());'
        seed = "seed" if name == "sha2" else "pk_seed"
        emit += f"\ncrate::check_cached_slots(p,md,sk_seed,{seed},fors_adrs,initial_position.0,initial_position.1,cached_layers,&xmss_slots,&fors_slots);"
        stop = join + len("crate::pool::execute(active_workers, true, &fill);")
        probe = probe[:begin]+start_ledger+worker+probe[join:stop]+emit+probe[stop:]
    return probe + (here / "parallel-proof/cached-slot-values.rs").read_text()


def certificates():
    plans = {}
    template = recording_probe()
    with tempfile.TemporaryDirectory() as tmp:
        binary = Path(tmp) / "ownership"
        src = binary.with_suffix(".rs")
        for width in (3, 8):
            src.write_text(template.replace("PROOF_WIDTH", str(width)))
            subprocess.run(["rustc", "--edition=2021", "--cfg", "proof_simd", "-O", "-C", "overflow-checks=yes",
                            "-Awarnings", src, "-o", binary], check=True)
            lines = subprocess.check_output([binary], text=True).splitlines()
            for line in lines:
                if not line.startswith("PLAN "):
                    continue
                _, name, n, d, layers, group, xmss, fors, encoded = line.split(" ", 8)
                key = (name, int(n), int(d), int(layers), int(group))
                geometry = (int(xmss)+int(fors), json.loads(encoded))
                if plans.setdefault(key, geometry) != geometry:
                    raise ValueError(f"job ownership changed with execution order: {key}")
    expected = {(name, n, d, layers, group) for name in ("sha2","shake")
                for n,d in ((16,7),(16,22),(24,7),(24,22),(32,8),(32,17)) for layers in (1,2)
                for group in ((1,) if name=="sha2" else (1,3,8))}
    if set(plans) != expected:
        raise ValueError(f"incomplete source plan coverage: {set(plans)^expected}")
    return plans


if __name__ == "__main__":
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"), str(Path.home()/".cargo/bin"), os.environ["PATH"]])
    facade["run"](["lake", "build", "Parallel.CacheAssembly"], lean)
    checked = certificates()
    # Definitional reduction in the Lean kernel checks each certificate. No native_decide axiom.
    for key, (total, jobs) in checked.items():
        name, n, layers, cached, _ = key
        bits = {16:128,24:192,32:256}[n]
        variant = "s" if layers in (7,8) else "f"
        hit = "some d2" if cached == 2 else "none"
        p = f"Spec.{name}_{bits}{variant}"
        program = f"""import Parallel.CacheAssembly
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def jobs : List (List Nat) := {json.dumps(jobs)}
private theorem ownership : jobs.flatten.Perm (List.range {total}) := List.isPerm_iff.mp (by rfl)
example (d2 : List Spec.Bytes) : jobs.flatten.Perm (List.range
    (ParallelCached.activeLayers {p} ({hit})*{p}.hp + {p}.k*(1+{p}.a))) := ownership
example {{V : Type}} (compute : Nat → Nat → V) {{t todo cells}}
    (run : ParallelCached.Run jobs.length (ParallelCached.planWrites jobs compute) t todo cells)
    (issued : t≤jobs.length) : ∃ out, ParallelCached.Completion jobs.length (ParallelCached.planWrites jobs compute)
      t todo cells out ∧ ∀ s, (∃ v, out s=some v) ↔ s<{total} :=
  ParallelCached.plan_completion jobs {total} compute ownership run issued
"""
        result = subprocess.run(["lake","env","lean","--stdin"], cwd=lean, input=program, text=True, capture_output=True)
        if result.returncode:
            raise ValueError(f"Lean rejected slot ownership for {key}: {result.stdout}{result.stderr}")
    facade["audit_theorems"]("Parallel.CacheCompletion", ["ParallelCached.can_join","ParallelCached.plan_completion"])
    facade["audit_theorems"]("Parallel.CacheAssembly", ["ParallelCached.joined_value", "ParallelCached.assemble_fips"])
    print(f"Lean checked exact slot ownership and worker completion for {len(checked)} production job plans")
