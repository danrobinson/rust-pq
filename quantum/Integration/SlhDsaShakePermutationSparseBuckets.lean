import Integration.SlhDsaShakePermutationSparsePort

/-! Three distinct sparse-domain rows rarely share their private suffix.
The uniform estimate is independent of the ideal output heads. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical SetOracle ENNReal
noncomputable section
variable {J Z : Type} [Fintype J] [Fintype Z] [DecidableEq J] [DecidableEq Z]

private def triple (t : Fin 3 ↪ J) (s : J → Z) := s (t 0) = s (t 1) ∧ s (t 0) = s (t 2)

omit [Fintype Z] [DecidableEq J] in
private theorem exists_triple (s : J → Z) (h : ¬small s) : ∃ t : Fin 3 ↪ J, triple t s := by
  unfold small at h; push Not at h
  obtain ⟨z,large⟩ := h
  let a := (Fin.castLEEmb (show 3 ≤ Fintype.card (Bucket s z) by omega)).trans
    (Fintype.equivFin (Bucket s z)).symm.toEmbedding
  exact ⟨a.trans (Function.Embedding.subtype _), (a 0).property.trans (a 1).property.symm,
    (a 0).property.trans (a 2).property.symm⟩

omit [DecidableEq Z] in
private theorem triple_count (t : Fin 3 ↪ J) :
    Fintype.card {s : J → Z // triple t s} * (Fintype.card Z)^2 ≤ Fintype.card (J → Z) := by
  classical
  have n01 : t 0 ≠ t 1 := t.injective.ne (by decide)
  have n02 : t 0 ≠ t 2 := t.injective.ne (by decide)
  have n12 : t 1 ≠ t 2 := t.injective.ne (by decide)
  let pack (z : {s : J → Z // triple t s} × (Z × Z)) :=
    Function.update (Function.update z.1.val (t 1) z.2.1) (t 2) z.2.2
  rw [pow_two,← Fintype.card_prod,← Fintype.card_prod]
  apply Fintype.card_le_of_injective pack
  rintro ⟨⟨s,hs⟩,u,v⟩ ⟨⟨s',hs'⟩,u',v'⟩ eq
  change Function.update (Function.update s (t 1) u) (t 2) v =
    Function.update (Function.update s' (t 1) u') (t 2) v' at eq
  have zero := congrFun eq (t 0)
  have one := congrFun eq (t 1)
  have two := congrFun eq (t 2)
  simp only [Function.update_of_ne n01,Function.update_of_ne n02] at zero
  simp only [Function.update_of_ne n12,Function.update_self] at one
  simp only [Function.update_self] at two
  apply Prod.ext _ (Prod.ext one two)
  apply Subtype.ext; funext j
  change s j = s' j
  by_cases h1 : j = t 1
  · rw [h1,← hs.1,← hs'.1,zero]
  by_cases h2 : j = t 2
  · rw [h2,← hs.2,← hs'.2,zero]
  simpa only [Function.update_of_ne h1,Function.update_of_ne h2] using congrFun eq j

theorem bucket_count :
    Fintype.card {s : J → Z // ¬small s} * (Fintype.card Z)^2 ≤
      (Fintype.card J)^3 * Fintype.card (J → Z) := by
  classical
  let encode (s : {s : J → Z // ¬small s}) : Σ t : Fin 3 ↪ J, {s : J → Z // triple t s} :=
    ⟨(exists_triple s.val s.property).choose,s.val,(exists_triple s.val s.property).choose_spec⟩
  have inj : Function.Injective encode := fun _ _ eq => Subtype.ext
    (congrArg (fun z : Σ t : Fin 3 ↪ J, {s : J → Z // triple t s} => z.2.val) eq)
  have h := Nat.mul_le_mul_right ((Fintype.card Z)^2) (Fintype.card_le_of_injective _ inj)
  rw [Fintype.card_sigma,Finset.sum_mul] at h
  have r := h.trans (Finset.sum_le_sum (fun t _ => triple_count (Z := Z) t))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_embedding_eq,Fintype.card_fin] at r
  exact r.trans (Nat.mul_le_mul_right _ (Nat.descFactorial_le_pow _ _))

/-- For the largest fixed-seed one- or two-node row domain, bounded by 768
bits, the probability of a suffix bucket of size three is at most 2^-384. -/
theorem bucket_risk (jcap : Fintype.card J ≤ 2^768) (zcap : 2^1344 ≤ Fintype.card Z) :
    Fintype.card {s : J → Z // ¬small s} * 2^384 ≤ Fintype.card (J → Z) := by
  let B := Fintype.card {s : J → Z // ¬small s}
  have h := bucket_count (J := J) (Z := Z)
  have lo : B * ((2^1344)^2) ≤ B * (Fintype.card Z)^2 := by gcongr
  have hi : (Fintype.card J)^3 * Fintype.card (J → Z) ≤ (2^768)^3 * Fintype.card (J → Z) := by gcongr
  have eq : (2^1344)^2 = (2:ℕ)^384 * (2^768)^3 := by
    rw [← pow_mul,← pow_mul,← pow_add]
  rw [eq,← Nat.mul_assoc] at lo
  exact Nat.le_of_mul_le_mul_right ((lo.trans h).trans (hi.trans_eq (Nat.mul_comm ..))) (by positivity)

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.bucket_risk
