import PQ.Interactive.QromBridgeEval

/-! Scope of the path-cost hypothesis used in the SHAKE forgery bounds.
The input to a machine can select its program by an arbitrary Lean function.
The `pure` constructor therefore suffices to embed any deterministic map
of the public input with zero weighted cost, including on a quantum workspace. -/

namespace PQ.Interactive

open OracleComp OracleSpec

/-- Every deterministic input/output map can be returned with zero path
budget for any weights on the instructions of the oracle computation. -/
theorem wCount_pure_input_map {ι X Y : Type} {sp : OracleSpec ι}
    (w : ι → ℕ) (f : X → Y) (x : X) :
    WCount w (pure (f x) : OracleComp sp Y) 0 := wCount_pure ..

/-- A semantic work measure on deterministic functions that is bounded by
every path budget of their pure embedding assigns zero work to every function. -/
theorem pure_embedding_work_iff {ι X Y : Type} {sp : OracleSpec ι}
    (w : ι → ℕ) (work : (X → Y) → ℕ) :
    (∀ (f : X → Y) (q : ℕ),
      (∀ x, WCount w (pure (f x) : OracleComp sp Y) q) → work f ≤ q) ↔
    ∀ f, work f = 0 := by
  constructor
  · intro sound f
    exact Nat.eq_zero_of_le_zero (sound f 0 (wCount_pure_input_map w f))
  · intro zero f q _
    simp [zero f]

end PQ.Interactive

#print axioms PQ.Interactive.wCount_pure_input_map
#print axioms PQ.Interactive.pure_embedding_work_iff
