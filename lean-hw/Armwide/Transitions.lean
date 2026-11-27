import Armwide.TransitionProgram
import Armwide.Kernel
import Mathlib.Data.Nat.BinaryRec

namespace slhdsa.Armwide.Transitions
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- One through four active lanes. Four selects the full-loop compaction after refill. -/
abbrev Count := Fin 4
def width (q : Count) := q.val + 1
private def mask (n : Nat) (f : Nat → Bool) : Fin (2^n) :=
  match n with
  | 0 => ⟨0, by decide⟩
  | k+1 =>
    let rest := mask k (fun i => f (i+1))
    ⟨Nat.bit (f 0) rest.val, by
      have h := rest.isLt
      cases e : f 0 <;> simp [Nat.bit, pow_succ] <;> omega⟩

private theorem mask_bit (n : Nat) (f : Nat → Bool) (i : Nat) (h : i < n) :
    (mask n f).val.testBit i = f i := by
  induction n generalizing f i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => exact Nat.testBit_bit_zero ..
    | succ i => rw [mask, Nat.testBit_bit_succ]; exact ih _ _ (by omega)

private def trace (q : Count) (live phases : Fin (2^(width q))) : Snapshot :=
  let start := #[0,4,20,84][q.val]!
  snapshots[serial[start + live.val * 2^(width q) + phases.val]!]!

def blueprint (q : Count) (live phases : Nat → Bool) : Snapshot :=
  let tail := width q < 4
  { kept := ((List.range (width q)).filter live).map fun i =>
      ⟨i, i+4, if tail && phases i then 12 else i+8, i, i,
       if tail && !phases i then 1 else 0, i, if tail then 1 else 0,
       if tail then 0 else (phases i).toNat⟩
    writes := if tail then ((List.range (width q)).filter fun i => !live i).map (fun i => ⟨i,i,i+4⟩) else [] }

private theorem trace_correct : ∀ (q : Count) (live phases : Fin (2^(width q))),
    trace q live phases = blueprint q live.val.testBit phases.val.testBit := by decide

/-- Runtime decisions arise from arbitrary counters and phase flags. -/
def actual (q : Count) (keep isPrf : Nat → Bool) : Snapshot :=
  trace q (mask (width q) keep) (mask (width q) isPrf)

theorem active_step (q : Count) (keep isPrf : Nat → Bool) :
    actual q keep isPrf = blueprint q keep isPrf := by
  rw [actual, trace_correct]
  have liveEq : (List.range (width q)).filter (mask (width q) keep).val.testBit =
      (List.range (width q)).filter keep := by
    apply List.filter_congr
    intro i h
    rw [mask_bit _ _ i (List.mem_range.mp h)]
  have deadEq : (List.range (width q)).filter (fun i => !(mask (width q) keep).val.testBit i) =
      (List.range (width q)).filter (fun i => !keep i) := by
    apply List.filter_congr
    intro i h
    rw [mask_bit _ _ i (List.mem_range.mp h)]
  simp only [blueprint,liveEq,deadEq,Snapshot.mk.injEq,and_true]
  apply List.map_congr_left
  intro i hi
  rw [mask_bit _ _ i (List.mem_range.mp (List.mem_filter.mp hi).1)]

end slhdsa.Armwide.Transitions
