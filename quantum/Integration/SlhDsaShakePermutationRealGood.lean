import Integration.SlhDsaShakePermutationMass
import Integration.SlhDsaShakePermutationExtensions

/-! Concrete quantum probability bound for loss of the salted sponge's
real database invariant. The computation may query both mask directions
coherently with arbitrary contractions on the surrounding work registers. -/
namespace Reduction.ShakePermutation
open Classical Quantum OracleSpec Matrix ENNReal Tails

private theorem half_count {R C : Type} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]
    (D : Database (Tagged R) C) (d : Bool) : (Graph.support (half D d)).card ≤ D.size := by
  apply Finset.card_le_card_of_injOn (fun r => (d,r))
  · intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Graph.mem_support (half D d) r).mp hr⟩
  · intro r _ s _ he
    exact congrArg Prod.snd he

private theorem half_update_same {R C : Type} [DecidableEq R]
    (D : Database (Tagged R) C) (d : Bool) (r : R) (u : C) :
    half (Function.update D (d,r) (some u)) d = Function.update (half D d) r (some u) := by
  funext s
  by_cases hs : s = r <;> simp [half,Function.update,hs]

private theorem half_update_other {R C : Type} [DecidableEq R]
    (D : Database (Tagged R) C) (d : Bool) (r : R) (u : C) :
    half (Function.update D (d,r) (some u)) (!d) = half D (!d) := by
  funext s
  simp [half,Function.update]

private theorem extension_count (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    (t : Nat) (D : Database (Tagged Rate) Capacity) (x : Tagged Rate)
    (ht : D.size < t) (hg : goodLabel (layout π) D = true) :
    (Finset.univ.filter fun u : Capacity => goodLabel (layout π) (Function.update D x (some u)) = false).card ≤ extensionBudget t := by
  classical
  have hL := (half_count D false).trans ht.le
  have hR := (half_count D true).trans ht.le
  simp only [goodLabel,decide_eq_true_eq] at hg
  rcases x with ⟨d,r⟩
  cases d with
  | false =>
    have hh (u : Capacity) : half (Function.update D (false,r) (some u)) true = half D true :=
      half_update_other D false r u
    simpa only [badLeft,goodLabel,hh,half_update_same,decide_eq_false_iff_not] using
      badLeft_card π hp he (half D false) (half D true) hg t hL hR r
  | true =>
    have hh (u : Capacity) : half (Function.update D (true,r) (some u)) false = half D false :=
      half_update_other D true r u
    simpa only [badRight,goodLabel,hh,half_update_same,decide_eq_false_iff_not] using
      badRight_card π hp he (half D false) (half D true) hg t hL hR r

theorem real_good_mass (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    {E K : Type} [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]
    {t q : Nat} (a : MaskRun (layout π) E K t q) :
    badMass (layout π) a ≤ 6*(q:ℝ)^2*(extensionBudget t) / 2^512 := by
  let : UniformAnswerMeasure (Tagged Rate →ₒ Capacity) := UniformAnswerMeasure.ofFiniteNonempty _
  have h := badMass_bound (layout π) a (goodLabel_instability (layout π) t (extensionBudget t)
    (fun D x ht _ hg => extension_count π hp he t D x ht hg))
  have hc : Fintype.card Capacity = 2^512 := by
    change Fintype.card (Fin 8 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  rw [hc,Nat.cast_pow,Nat.cast_ofNat] at h
  exact h

private theorem real_good_arithmetic {q t : Nat} (ht : t ≤ 2^45) (hq : q ≤ 2^45) :
    6*(q:ℝ)^2*(extensionBudget t) / 2^512 ≤ (2^280 : ℝ)⁻¹ := by
  have mono : extensionBudget t ≤ extensionBudget (2^45) := by unfold extensionBudget; gcongr
  have hn : 6*(2^45 : Nat)^2*extensionBudget (2^45)*2^280 ≤ 2^512 := by decide +kernel
  rw [← one_div]
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  exact_mod_cast (Nat.mul_le_mul_right (2^280) (Nat.mul_le_mul
    (Nat.mul_le_mul_left 6 (Nat.pow_le_pow_left hq 2)) mono)).trans hn

theorem real_good_mass_benchmark (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    {E K : Type} [Fintype E] [Fintype K] [DecidableEq E] [DecidableEq K]
    {t q : Nat} (ht : t ≤ 2^45) (hq : q ≤ 2^45) (a : MaskRun (layout π) E K t q) :
    badMass (layout π) a ≤ (2^280 : ℝ)⁻¹ := by
  exact le_trans (real_good_mass π hp he a) (real_good_arithmetic ht hq)

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.real_good_mass
#print axioms Reduction.ShakePermutation.real_good_mass_benchmark
