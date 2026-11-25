#!/usr/bin/env python3
"""Kernel-check physical ownership of every uncached signer's phase-one ledger."""
import json
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
import signer

def main():
    facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"), str(Path.home()/".cargo/bin"), os.environ["PATH"]])
    facade["run"](["lake", "build", "Parallel.MaximalCoverage", "Parallel.TicketProjection"], facade["LEAN"])
    template = signer.probe_source((facade["ROOT"] / "rust/src/cache.rs").read_text())
    with tempfile.TemporaryDirectory() as tmp:
        src = Path(tmp, "sign.rs")
        exe = src.with_suffix("")
        for width in (3, 8):
            src.write_text(template.replace("PROOF_WIDTH", str(width)))
            subprocess.run(["rustc", "--edition=2021", "--cfg", "proof_simd", "-O", "-C",
                            "overflow-checks=yes", "-Awarnings", src, "-o", exe], check=True)
            replay = subprocess.check_output([exe], text=True, env={**os.environ, "RUST_PQ_SIGNING_CERTIFICATE":"1"})
            ledgers = [s for s in replay.splitlines() if s.startswith("LEDGER ")]
            ranges = [line.split()[1:] for line in replay.splitlines() if line.startswith("CELL_RANGES ")]
            if len(ledgers) != 12 or len(ranges) != len(ledgers):
                raise ValueError(f"expected six parameter geometries with SIMD on and off, got {len(ledgers)}")
            for idx, line in enumerate(ledgers):
                _, lanes, total, fields = line.split(" ",3)
                jobs, reducer = map(json.loads, fields.split("|"))
                if int(lanes) != width:
                    raise ValueError("unexpected width")
                offset, leaves, direct, split = map(int, ranges[idx])
                if offset + leaves + direct + split != int(total):
                    raise ValueError("source table sizes and ticket counts disagree")
                case = ("128s", "128f", "192s", "192f", "256s", "256f")[idx//2]
                hosts = ("ParallelLinuxArmAPI",) if width == 3 else ("ParallelAppleAPI", "ParallelX86API")
                proof = f"""import Parallel.MaximalPublic
import Parallel.SigningSchedules
import Parallel.TicketProjection
set_option linter.defProp false
set_option maxRecDepth 200000
set_option maxHeartbeats 0
private def jobs : List (List Nat) := {jobs}
private def leafFields (j : Nat) := jobs[j]!.filterMap fun k =>
  if {offset} ≤ k ∧ k < {offset + leaves} then some (k-{offset}) else none
private theorem leafCover : ((List.range jobs.length).flatMap leafFields).Perm (List.range {leaves}) :=
  List.isPerm_iff.mp (by rfl)
example {{issued : Nat}} {{done : List Nat}} (trace : ParallelSigning.Trace jobs.length issued [] done)
    (exhausted : jobs.length < issued) :
    ParallelSigning.Trace {leaves} ({leaves}+1) [] (done.flatMap leafFields) :=
  ParallelSigning.projected_trace trace exhausted leafFields leafCover
private def reducer : List Nat := {reducer}
private def slots := jobs.flatten ++ reducer
private theorem geometry : slots.Perm (List.range {int(total)}) := List.isPerm_iff.mp (by rfl)
private theorem unique : jobs.flatten.Nodup := (List.nodup_append.mp (geometry.nodup_iff.mpr List.nodup_range)).1
example {{V : Type}} (value : Nat → V) (a b : ParallelFused.Schedules.Completion
    (ParallelCached.Tickets.valued jobs value)) : a.state.cells = b.state.cells :=
  ParallelFused.Schedules.sameCells (ParallelFused.Schedules.valued_unique jobs value unique) a b
example : jobs.length + jobs.length < 2^32 := by decide
open slhdsa.MaximalWorker
private def physicalJobs := ParallelCached.Tickets.valued jobs (fun _ => ())
private def p := slhdsa.sets.shake_{case}.params.PARAMS
private abbrev numForest := p.k.val*(p.a.val+1)
private abbrev numChunks := (slhdsa.ParallelRawChunks.slots p.hp.val (p.d.val*p.hp.val)).length
private abbrev numLeaves := p.d.val-1
private theorem nf : numForest={direct} := by decide +kernel
private theorem nx : numChunks={offset} := by decide +kernel
private theorem nl : numLeaves={leaves} := by decide +kernel
private def physicalPlan : PhasePlan numForest numChunks numLeaves where
  jobs := physicalJobs
  reducer := reducer
  unique := ParallelFused.Schedules.valued_unique jobs _ unique
  forestCover := by rw [nf,nx,nl];exact List.isPerm_iff.mp (by rfl)
  chunkCover := by rw [nx];exact List.isPerm_iff.mp (by rfl)
  leafCover := by rw [nx,nl];exact List.isPerm_iff.mp (by rfl)
private def session (first : MaxRun physicalJobs) (second : MaxRun (single p.d.val).jobs)
    (same : first.workers=second.workers) : For p := ⟨physicalPlan,first,second,same⟩
private def initialSession : StartFor p := untouched physicalPlan 1 (by decide)
  (lt_of_lt_of_le (by decide : physicalPlan.jobs.length+1<2^32)
    (Nat.pow_le_pow_right (by decide) System.Platform.le_numBits))
  (lt_of_lt_of_le (by decide +kernel : (single p.d.val).jobs.length+1<2^32)
    (Nat.pow_le_pow_right (by decide) System.Platform.le_numBits))

"""
                for host in hosts:
                    extra = " true" if host == "ParallelAppleAPI" else ""
                    # Apple exposes both public SHA3 feature decisions through its boolean parameter.
                    prefix = f"{host}.shake_{case}.roundtrip"
                    proof += (f"private def live{host} (a : MaxRun physicalJobs) (b : MaxRun (single p.d.val).jobs) := "
                              f"fun (same : a.workers=b.workers) => MaximalSigning.{prefix}{extra} (session a b same)\n"
                              f"private def start{host} := PrefixSigning.{prefix}{extra} initialSession\n")
                subprocess.run(["lake","env","lean","--stdin"], input=proof, text=True, cwd=facade["LEAN"], check=True)
                print(f"width {width}, plan {idx+1}: {len(jobs)} sorted tickets, {total} physical slots", flush=True)
    operations = ("slh_sign_internal", "slh_sign", "sign", "sign_deterministic", "roundtrip")
    theorem_roots = [f"{level}.{host}.shake_{bits}{speed}.{op}{suffix}"
        for level in ("MaximalSigning", "PrefixSigning")
        for host in ("ParallelAppleAPI", "ParallelX86API", "ParallelLinuxArmAPI")
        for bits in (128, 192, 256) for speed in ("s", "f") for op in operations
        for suffix in ("" if host == "ParallelLinuxArmAPI" or op == "roundtrip" else "_spec",)]
    facade["audit_theorems"]("Parallel.MaximalPublic", theorem_roots + ["slhdsa.MaximalWorker." + theorem for theorem in
        ("History.extend", "order_complete", "last_finisher", "fuel_bound", "Session.orders", "InitialRun.can_complete", "Beginning.extends", "MaxRun.counter_fits")])
    enabled = [f"{level}.{host}.shake_{bits}{speed}.worker_returns"
        for level in ("MaximalSigning", "PrefixSigning")
        for host in ("ParallelAppleAPI", "ParallelX86API", "ParallelLinuxArmAPI")
        for bits in (128, 192, 256) for speed in ("s", "f")]
    facade["audit_theorems"]("Parallel.MaximalEnabled", enabled + ["slhdsa.MaximalWorker.Session.publication"])
    facade["audit_theorems"]("Parallel.QueueOrder", ["ParallelFused.LastFinisher.cell_at_last", "ParallelFused.LastFinisher.reordered_cells"])
    facade["audit_theorems"]("Parallel.TicketProjection", ["ParallelSigning.projected_trace"])
    facade["audit_theorems"]("Parallel.SigningSchedules", ["ParallelFused.Schedules.signature_independent"])

    facade["audit_theorems"]("Parallel.LastFinisher", [
        f"ParallelFused.LastFinisher.{name}" for name in
        ("reference_cells", "visibility", "can_finish", "signature_at_last")])

if __name__ == "__main__":
    main()
