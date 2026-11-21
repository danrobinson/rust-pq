import PQ.QROM.Hybrid
import PQ.QROM.Preimage

/-!
# Preimage resistance of a random function against quantum query programs

Program-level forms of `PQ.QROM.preimage_uniform_le` and `PQ.QROM.preimage_planted_le`: the
adversary is any family of VCVio quantum query programs (one per challenge) making at most `q`
oracle calls on every path; `out` decodes its classical output.
-/

open ENNReal Quantum

universe u v w

namespace PQ.QROM

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- **Preimage resistance in the QROM, uniform target.** `H ← (X → Y)`, `y ← Y`; the program
`x y`, started in `ρ y`, makes at most `q` quantum queries to `H` and outputs `out y p`.
`Pr[H (out) = y] ≤ (2q+1)² / |Y|`. -/
theorem preimage_uniform_program_le (I : L.Interp)
    (x : Y → QuantumComp L (qromSpec X Y) W A) (ρ : Y → SubState A) (q : ℕ)
    (hx : ∀ y, QueryBounded (x y) q) (out : Y → (Σ u, W u) → X) :
    ∑ H : X → Y, ∑ y : Y,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card Y : ℝ≥0∞)⁻¹) *
          qprob I H (x y) (ρ y) (fun p ↦ H (out y p) = y) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞) :=
  preimage_uniform_le (fun y ↦ HybridModel.ofProgram I (x y) (ρ y) q (hx y) (out y)) fun _ ↦ id

/-- **Preimage resistance in the QROM, target `H x*` for a hidden uniform `x*`.**
`Pr[H (out) = H x*] ≤ (2q+1)² (1/|Y| + 1/|X|)`. -/
theorem preimage_planted_program_le (I : L.Interp)
    (x : Y → QuantumComp L (qromSpec X Y) W A) (ρ : Y → SubState A) (q : ℕ)
    (hx : ∀ y, QueryBounded (x y) q) (out : Y → (Σ u, W u) → X) :
    ∑ H : X → Y, ∑ xs : X,
        ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹ * (Fintype.card X : ℝ≥0∞)⁻¹) *
          qprob I H (x (H xs)) (ρ (H xs)) (fun p ↦ H (out (H xs) p) = H xs) ≤
      (2 * (q : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card Y : ℝ≥0∞)⁻¹ + (Fintype.card X : ℝ≥0∞)⁻¹) :=
  preimage_planted_le (fun y ↦ HybridModel.ofProgram I (x y) (ρ y) q (hx y) (out y)) fun _ ↦ id

end PQ.QROM

#print axioms PQ.QROM.preimage_uniform_program_le
#print axioms PQ.QROM.preimage_planted_program_le
