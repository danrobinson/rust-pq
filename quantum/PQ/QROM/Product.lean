import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Logic.Equiv.Prod

/-!
# Coordinatewise change of variables for sums over function spaces (engine E3)

Sums over `τ : X → T` are (unnormalised) expectations over independent coordinates.  If two
weights `a`, `b` on one coordinate have the same push-forward under the coordinate maps `c`, `c'`,
they can be exchanged under any sum that sees the coordinate `x₀` only through `c`/`c'`.

* `sum_mul_comp_eq`: the one-coordinate statement.
* `sum_coord_change`: general form (the rest of the summand may depend on the other coordinates
  of `τ` arbitrarily).
* `sum_comp_coord_change`: the form `∑ τ, a (τ x₀) * Φ (c ∘ τ) = ∑ τ, b (τ x₀) * Φ (c ∘ τ)`.
* `sum_fst_comp`: marginalising an unused independent second component.
-/

open ENNReal Finset

namespace PQ.QROM

section

variable {T Z : Type} [Fintype T] [DecidableEq Z]

/-- One coordinate: weights with the same push-forward integrate functions of the image
equally. -/
theorem sum_mul_comp_eq (c c' : T → Z) (a b : T → ℝ≥0∞)
    (h : ∀ z, ∑ t with c t = z, a t = ∑ t with c' t = z, b t) (Ψ : Z → ℝ≥0∞) :
    ∑ t, a t * Ψ (c t) = ∑ t, b t * Ψ (c' t) := by
  have key : ∀ (c : T → Z) (a : T → ℝ≥0∞) (U : Finset Z), (∀ t, c t ∈ U) →
      ∑ t, a t * Ψ (c t) = ∑ z ∈ U, (∑ t with c t = z, a t) * Ψ z := by
    intro c a U hU
    rw [← Finset.sum_fiberwise_of_maps_to (t := U) (g := c) fun t _ ↦ hU t]
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [(Finset.mem_filter.1 ht).2]
  rw [key c a (univ.image c ∪ univ.image c') fun t ↦
      Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    key c' b (univ.image c ∪ univ.image c') fun t ↦
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))]
  exact Finset.sum_congr rfl fun z _ ↦ by rw [h z]

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **E3, general form.** In a sum over `τ : X → T`, a weight `a (τ x₀)` together with a
dependence on `τ x₀` through `c (τ x₀)` only can be exchanged for `b (τ x₀)` and `c' (τ x₀)` when
`a` under `c` and `b` under `c'` have the same push-forward.  `hΦ` says that `Φ z τ` does not
depend on the coordinate `x₀` of `τ`. -/
theorem sum_coord_change (x₀ : X) (c c' : T → Z) (a b : T → ℝ≥0∞)
    (h : ∀ z, ∑ t with c t = z, a t = ∑ t with c' t = z, b t) (Φ : Z → (X → T) → ℝ≥0∞)
    (hΦ : ∀ z τ t, Φ z (Function.update τ x₀ t) = Φ z τ) :
    ∑ τ : X → T, a (τ x₀) * Φ (c (τ x₀)) τ = ∑ τ : X → T, b (τ x₀) * Φ (c' (τ x₀)) τ := by
  have hupd : ∀ (t t₁ : T) (ρ : {j // j ≠ x₀} → T),
      (Equiv.funSplitAt x₀ T).symm (t, ρ) =
        Function.update ((Equiv.funSplitAt x₀ T).symm (t₁, ρ)) x₀ t := by
    intro t t₁ ρ
    funext j
    by_cases hj : j = x₀
    · subst hj; simp [Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hat : ∀ (t : T) (ρ : {j // j ≠ x₀} → T), (Equiv.funSplitAt x₀ T).symm (t, ρ) x₀ = t := by
    intro t ρ; simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [← Equiv.sum_comp (Equiv.funSplitAt x₀ T).symm, ← Equiv.sum_comp (Equiv.funSplitAt x₀ T).symm,
    Fintype.sum_prod_type_right, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun ρ _ ↦ ?_
  simp only [hat]
  rcases isEmpty_or_nonempty T with hT | ⟨⟨t₁⟩⟩
  · simp
  · have hΨ : ∀ z t, Φ z ((Equiv.funSplitAt x₀ T).symm (t, ρ)) =
        Φ z ((Equiv.funSplitAt x₀ T).symm (t₁, ρ)) := fun z t ↦ by rw [hupd t t₁ ρ, hΦ]
    simp only [hΨ]
    exact sum_mul_comp_eq c c' a b h fun z ↦ Φ z ((Equiv.funSplitAt x₀ T).symm (t₁, ρ))

/-- **E3.** Product change of variables: under a sum over `τ : X → T` that sees `τ` only through
`c ∘ τ`, a weight on the coordinate `x₀` can be replaced by any weight with the same push-forward
under `c`. -/
theorem sum_comp_coord_change (x₀ : X) (c : T → Z) (a b : T → ℝ≥0∞)
    (h : ∀ z, ∑ t with c t = z, a t = ∑ t with c t = z, b t) (Φ : (X → Z) → ℝ≥0∞) :
    ∑ τ : X → T, a (τ x₀) * Φ (c ∘ τ) = ∑ τ : X → T, b (τ x₀) * Φ (c ∘ τ) := by
  have hupd : ∀ τ : X → T, Function.update (c ∘ τ) x₀ (c (τ x₀)) = c ∘ τ := fun τ ↦
    Function.update_eq_self x₀ (c ∘ τ)
  have := sum_coord_change x₀ c c a b h (fun z τ ↦ Φ (Function.update (c ∘ τ) x₀ z)) (by
    intro z τ t
    congr 1
    funext j
    by_cases hj : j = x₀
    · subst hj; simp
    · simp [Function.update, hj])
  simpa only [hupd] using this

end

/-- Marginalising an unused second component of every coordinate. -/
theorem sum_fst_comp {X A B : Type} [Fintype X] [DecidableEq X] [Fintype A] [Fintype B]
    (F : (X → A) → ℝ≥0∞) :
    ∑ τ : X → A × B, F (fun k ↦ (τ k).1) = Fintype.card (X → B) * ∑ H : X → A, F H := by
  rw [← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow X (fun _ ↦ A) (fun _ ↦ B)).symm, Fintype.sum_prod_type]
  simp [Equiv.arrowProdEquivProdArrow, Finset.mul_sum]

end PQ.QROM

#print axioms PQ.QROM.sum_coord_change
#print axioms PQ.QROM.sum_comp_coord_change
#print axioms PQ.QROM.sum_fst_comp
