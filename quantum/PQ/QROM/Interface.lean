import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# The interface between the quantum hybrid argument and the game analyses

`PQ.QROM.HybridModel X Y Leaf q` records the only facts about a fixed `q`-query quantum algorithm
that the game analyses in `PQ/QROM` use:

* `prob H E`: the probability that the algorithm, with quantum access to `H : X → Y`, ends in a
  leaf satisfying `E`;
* `mass G k`: the total query mass the run against `G` puts on the input `k` (summed over calls);
* the two-sided square-root hybrid bound between any two functions, charged to the masses of ONE
  of the two runs on the points where the functions differ (Bennett–Bernstein–Brassard–Vazirani).

The fields are hypotheses bundled in a structure, not axioms: `PQ/QROM/Hybrid.lean` constructs a
`HybridModel` from every VCVio quantum query program (`HybridModel.ofProgram`), so every theorem
stated for an arbitrary `HybridModel` holds for all such programs.  The bundling only decouples
the (finite, classical) probability calculations from the operator-theoretic proof.
-/

open ENNReal

namespace PQ.QROM

/-- What the game analyses know about a fixed quantum algorithm making at most `q` queries to a
function `X → Y`, with leaves (classical outputs) in `Leaf`. -/
structure HybridModel (X Y Leaf : Type) [Fintype X] [DecidableEq Y] (q : ℕ) where
  /-- Probability of ending in a leaf satisfying `E` when the oracle is `H`. -/
  prob : (X → Y) → (Leaf → Prop) → ℝ≥0∞
  /-- Total query mass of the run against `G` on the query input `k`. -/
  mass : (X → Y) → X → ℝ≥0∞
  /-- Events are monotone. -/
  prob_mono : ∀ (H : X → Y) {E E' : Leaf → Prop}, (∀ p, E p → E' p) → prob H E ≤ prob H E'
  /-- The events `out = k`, for any classical decoding `out` of the leaf, have total probability
  at most one. -/
  prob_sum_le : ∀ (H : X → Y) (out : Leaf → X), ∑ k, prob H (fun p ↦ out p = k) ≤ 1
  /-- Finite subadditivity of the distribution of a classical decoding of the leaf. -/
  prob_sub : ∀ (H : X → Y) (out : Leaf → X) (T : Finset X),
    prob H (fun p ↦ out p ∈ T) ≤ ∑ k ∈ T, prob H (fun p ↦ out p = k)
  /-- At most `q` queries: total mass at most `q`. -/
  mass_sum_le : ∀ G : X → Y, ∑ k, mass G k ≤ q
  /-- Square-root hybrid bound, masses of the run against `G`. -/
  hybrid : ∀ (H G : X → Y) (E : Leaf → Prop),
    prob H E ^ (2⁻¹ : ℝ) ≤ prob G E ^ (2⁻¹ : ℝ) +
      (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k), mass G k) ^ (2⁻¹ : ℝ)
  /-- Square-root hybrid bound, converse direction, same masses. -/
  hybrid' : ∀ (H G : X → Y) (E : Leaf → Prop),
    prob G E ^ (2⁻¹ : ℝ) ≤ prob H E ^ (2⁻¹ : ℝ) +
      (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k), mass G k) ^ (2⁻¹ : ℝ)

namespace HybridModel

variable {X Y Leaf : Type} [Fintype X] [DecidableEq Y] {q : ℕ}

/-- Probabilities are at most one. -/
theorem prob_le_one [Nonempty X] (M : HybridModel X Y Leaf q) (H : X → Y) (E : Leaf → Prop) :
    M.prob H E ≤ 1 := by
  classical
  let k₀ : X := Classical.arbitrary X
  calc M.prob H E ≤ M.prob H (fun _ ↦ k₀ = k₀) := M.prob_mono H fun _ _ ↦ rfl
    _ ≤ ∑ k, M.prob H (fun _ ↦ k₀ = k) :=
        Finset.single_le_sum (f := fun k ↦ M.prob H (fun _ ↦ k₀ = k)) (fun _ _ ↦ zero_le)
          (Finset.mem_univ k₀)
    _ ≤ 1 := M.prob_sum_le H fun _ ↦ k₀

end HybridModel

end PQ.QROM
