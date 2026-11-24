import Integration.SlhDsaShakePermutationSparseBuckets

/-! Failure of a simultaneous transposition on a sparse one-block domain. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical
noncomputable section
set_option exponentiation.threshold 2048
variable {J X : Type} [Fintype J] [DecidableEq J] [Fintype X]
abbrev Witness (J : Type) := Bool × J × J

def hit (old : J → X) (z : Witness J) (t : J → X) :=
  if z.1 then z.2.1 ≠ z.2.2 ∧ t z.2.1 = t z.2.2 else t z.2.1 = old z.2.2

private theorem hit_count (old : J → X) (z : Witness J) :
    Fintype.card {t : J → X // hit old z t} * Fintype.card X ≤ Fintype.card (J → X) := by
  classical
  rw [← Fintype.card_prod]
  let pack (v : {t // hit old z t} × X) := Function.update v.1.val z.2.1 v.2
  apply Fintype.card_le_of_injective pack
  rintro ⟨⟨t,ht⟩,a⟩ ⟨⟨s,hs⟩,b⟩ eq
  change Function.update t z.2.1 a = Function.update s z.2.1 b at eq
  apply Prod.ext _ (by simpa only [Function.update_self] using congrFun eq z.2.1)
  apply Subtype.ext; funext j
  change t j = s j
  by_cases same : j = z.2.1
  · subst j
    unfold hit at ht hs
    by_cases b : z.1 = true
    · simp only [b,ite_true] at ht hs
      have rest := congrFun eq z.2.2
      simp only [Function.update_of_ne ht.1.symm] at rest
      exact ht.2.trans (rest.trans hs.2.symm)
    · simp only [ite_eq_right b] at ht hs
      exact ht.trans hs.symm
  · simpa only [Function.update_of_ne same] using congrFun eq j

def labels (old t : J → X) : Bool × J → X := fun z => if z.1 then t z.2 else old z.2

omit [Fintype J] [DecidableEq J] [Fintype X] in
private theorem cert (old t : J → X) (inj : Function.Injective old) (bad : ¬Function.Injective (labels old t)) :
    ∃ z : Witness J, hit old z t := by
  unfold Function.Injective at bad
  push Not at bad
  obtain ⟨⟨b,i⟩,⟨d,j⟩,eq,ne⟩ := bad
  cases b <;> cases d
  · exact False.elim (ne (Prod.ext rfl (inj eq)))
  · exact ⟨(false,j,i),eq.symm⟩
  · exact ⟨(false,i,j),eq⟩
  · exact ⟨(true,i,j),fun h => ne (Prod.ext rfl h),eq⟩

theorem fail_count (old : J → X) (inj : Function.Injective old) :
    Fintype.card {t : J → X // ¬Function.Injective (labels old t)} * Fintype.card X ≤
      2*(Fintype.card J)^2 * Fintype.card (J → X) := by
  classical
  let record (t : {t : J → X // ¬Function.Injective (labels old t)}) : Σ z : Witness J, {t // hit old z t} :=
    ⟨(cert old t.val inj t.property).choose,t.val,(cert old t.val inj t.property).choose_spec⟩
  have hi : Function.Injective record := fun _ _ eq => Subtype.ext
    (congrArg (fun s : Σ z : Witness J, {t // hit old z t} => s.2.val) eq)
  have h := Nat.mul_le_mul_right (Fintype.card X) (Fintype.card_le_of_injective _ hi)
  rw [Fintype.card_sigma,Finset.sum_mul] at h
  have out := h.trans (Finset.sum_le_sum fun z _ => hit_count old z)
  simpa only [Witness,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_prod,
    Fintype.card_bool,pow_two,mul_assoc] using out

/-- Probability of a conflicting full image is at most 2^-63 for an entire
formatted domain with at most 2^768 rows. -/
theorem fail_risk (old : J → X) (inj : Function.Injective old) (jcap : Fintype.card J ≤ 2^768)
    (words : Fintype.card X = 2^1600) :
    Fintype.card {t : J → X // ¬Function.Injective (labels old t)} * 2^63 ≤ Fintype.card (J → X) := by
  have h := fail_count old inj
  rw [words] at h
  have hi : 2*(Fintype.card J)^2 * Fintype.card (J → X) ≤ (2*(2^768)^2) * Fintype.card (J → X) := by gcongr
  have eq : (2:ℕ)^1600 = 2^63 * (2*(2^768)^2) := by decide +kernel
  rw [eq,← Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right (h.trans (hi.trans_eq (Nat.mul_comm ..))) (by positivity)

theorem fail_nat (old : J → X) (inj : Function.Injective old) (jcap : Fintype.card J ≤ 2^768)
    (words : Fintype.card X = 2^1600) :
    Nat.card {t : J → X // ¬Function.Injective (labels old t)} * 2^63 ≤ Nat.card (J → X) := by
  classical
  simpa only [Nat.card_eq_fintype_card] using fail_risk old inj jcap words

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.fail_risk
