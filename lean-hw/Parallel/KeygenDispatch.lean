import Parallel.KeygenHost
import Parallel.KeygenPlan

open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelKeygenHost
noncomputable section

def projectedPlan (isX86 : Bool) (p : params.Params) (threads : Usize) :=
  if isX86 then ParallelKeygenPlan.X86.slh.parallel.proof_keygen_plan p threads
  else ParallelKeygenPlan.Arm.slh.parallel.proof_keygen_plan p threads

/-- Bind the Rust plan's actual Option result to the fetch/compute/merge worker.
The denied plan returns None; the accepted plan returns the joined top root. -/
theorem worker_from_plan {S} (e : Engine S) {N : Usize} (p : params.Params) (P : Spec.Params)
    (sameHeight : P.hp=p.hp.val) (height : P.hp≤9) (okSeed : S N → Prop) (nodes : NodeCorrect e P okSeed)
    (isX86 : Bool) (threads : Usize) (pool : PoolOutcome) (sk : Array U8 N) (seed : S N)
    (hs : okSeed seed) (a : address.Adrs) (top : Array U8 N)
    (correct : bytes top.val=Spec.xmssNode P (bytes sk.val) 0 P.hp (e.seedBytes seed) (adrsS a)) :
    projectedPlan isX86 p threads ⦃ plan =>
      ParallelKeygenPlan.result plan = ParallelKeygenPlan.value isX86 p threads ∧
      worker e P isX86 threads.val pool sk seed a = ok (plan.map (fun _ => top)) ⦄ := by
  have plan : projectedPlan isX86 p threads ⦃ out => ParallelKeygenPlan.result out = ParallelKeygenPlan.value isX86 p threads ⦄ := by
    cases isX86
    · exact ParallelKeygenPlan.arm p threads (sameHeight ▸ height)
    · exact ParallelKeygenPlan.x86 p threads (sameHeight ▸ height)
  apply WP.spec_mono plan
  intro out shape
  refine ⟨shape,?_⟩
  rw [worker_value e P okSeed height nodes isX86 threads.val pool sk seed hs a top correct,sameHeight]
  unfold ParallelKeygenPlan.value at shape
  split at shape <;> cases out <;> simp_all [ParallelKeygenPlan.result]

/-- Fetches include one out-of-range observation per participating invocation.
Even on a 32-bit usize the Standard's largest plan cannot wrap its counter. -/
theorem fetch_safe (isX86 : Bool) (height threads : Nat) (pool : PoolOutcome) (small : height≤9)
    (compute : Nat → Spec.Bytes) {st} :
    let n := ParallelKeygen.count isX86 height
    let workers := participants pool (min threads n)
    ParallelCached.Tickets.Reach (ParallelKeygen.jobs n compute) workers st →
      st.counter<2^32 ∧ (st.counter<n ↔ st.issued<n) := by
  intro n workers run
  have cap : n≤512 := (ParallelKeygen.geometry isX86 height small).2.1
  have pos : 0<n := Nat.pow_pos (by decide)
  have bound : workers ≤ n := by dsimp [workers,participants]; split <;> omega
  have fits : (ParallelKeygen.jobs n compute).length+workers<2^32 := by simp [ParallelKeygen.jobs]; omega
  simpa [ParallelKeygen.jobs] using ParallelCached.Tickets.fetch_bound run fits
end
end slhdsa.ParallelKeygenHost
