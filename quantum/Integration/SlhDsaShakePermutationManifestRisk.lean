import Integration.SlhDsaShakePermutationManifestCount

/-! Uniform permutation failure probability for an entire fixed prefix tree. -/
namespace Reduction.ShakePermutation.Manifest
open Classical
set_option maxRecDepth 10000
set_option exponentiation.threshold 2048

private theorem falling (C n : ℕ) (hn : n ≤ C) :
    C ^ (n + 1) ≤ C * (C-1).descFactorial n + n^2 * C^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := Nat.mul_le_mul_right C (ih (by omega))
    have small : (C-1).descFactorial n ≤ C^n :=
      (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (by omega) n)
    have rest : C-1-n + (n+1) = C := by omega
    have split : C * (C - 1).descFactorial n * C =
       C * ((C-1-n) * (C-1).descFactorial n) + C * (n+1) * (C-1).descFactorial n := by
      conv_lhs => arg 2; rw [← rest]
      ring
    rw [Nat.add_mul,split] at ih
    rw [pow_succ (n := n+1),Nat.descFactorial_succ]
    apply ih.trans
    calc
      _ ≤ C * ((C - 1 - n) * (C-1).descFactorial n) +
        (C * (n+1) * C^n) + n^2 * C^n * C :=
          Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ small) _) _
      _ ≤ _ := by rw [pow_succ C n]; nlinarith only [Nat.zero_le (n * (C ^ n * C))]

private theorem lanes (n : ℕ) : Fintype.card (Fin n → UInt64) = (2^64)^n := by
  rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]

set_option allowUnsafeReducibility true in
attribute [local irreducible] Fintype.card Nat.card

private theorem counting (C R n P G : ℕ) (hr : 0 < R) (hc : 0 < C) (hn : n ≤ C)
    (hm : (C-1).descFactorial n * R^n * P ≤ (C*R).descFactorial n * G) :
    C*(P-G) ≤ n^2*P := by
  have er : 0 < R^n := Nat.pow_pos hr
  have hraw : (C-1).descFactorial n * P ≤ C^n * G := by
    apply Nat.le_of_mul_le_mul_right _ er
    have hh := hm.trans (Nat.mul_le_mul_right G (Nat.descFactorial_le_pow (C*R) n))
    rw [mul_pow] at hh
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have ec : 0 < C^n := Nat.pow_pos hc
  have final : C*P ≤ C*G + n^2*P := by
    apply Nat.le_of_mul_le_mul_left _ ec
    have hf := Nat.mul_le_mul_right P (falling C n hn)
    rw [pow_succ,Nat.add_mul] at hf
    calc
      _ = C^n * C * P := by ring
      _ ≤ _ := hf
      _ ≤ C * (C^n * G) + n^2 * C^n * P := by
        rw [Nat.mul_assoc C]
        exact Nat.add_le_add_right (Nat.mul_le_mul_left C hraw) _
      _ = _ := by ring
  rw [Nat.mul_sub]
  omega

private theorem cap_card : Fintype.card Capacity = 2^512 :=
  (lanes 8).trans ((pow_mul 2 64 8).symm.trans (by rfl))

private theorem rate_card : Fintype.card Rate = 2^1088 :=
  (lanes 17).trans ((pow_mul 2 64 17).symm.trans (by rfl))

private theorem word_card : Fintype.card Words = (2^512)*(2^1088) :=
  (lanes 25).trans ((pow_mul 2 64 25).symm.trans (pow_add 2 512 1088))

private theorem card_without {A : Type} [Fintype A] [DecidableEq A] (x : A) :
    Fintype.card {z : A // z ≠ x} = Fintype.card A - 1 := by
  rw [Fintype.card_subtype_compl]; simp

private theorem left_card {I : Type} [Fintype I] :
    Nat.card (Caps I × (I → Rate)) =
      ((2^512)-1).descFactorial (Fintype.card I) * (2^1088)^(Fintype.card I) := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_prod,Fintype.card_fun,rate_card]
  unfold Caps
  rw [Fintype.card_embedding_eq,card_without,cap_card]

private theorem right_card {I : Type} [Fintype I] :
    Nat.card (I ↪ Words) = ((2^512)*(2^1088)).descFactorial (Fintype.card I) := by
  rw [Nat.card_eq_fintype_card,Fintype.card_embedding_eq,word_card]

theorem count_to_risk {I : Type} [Fintype I] (ok : Permutation → Prop)
    (hn : Nat.card I ≤ 2^512) (hm : Nat.card (Caps I × (I → Rate)) * Nat.card Permutation ≤
      Nat.card (I ↪ Words) * Nat.card {π : Permutation // ok π}) :
    2^512 * Nat.card {π : Permutation // ¬ ok π} ≤ (Nat.card I)^2 * Nat.card Permutation := by
  classical
  rw [left_card,right_card] at hm
  simp only [Nat.card_eq_fintype_card,Fintype.card_subtype_compl] at hm hn ⊢
  exact counting _ _ _ _ _ (Nat.pow_pos (by decide : 0 < 2)) (Nat.pow_pos (by decide : 0 < 2)) hn hm

/-- Probability of any zero or repeated prefix capacity is at most n²/2^512.
The entire tree, including the values of all input blocks, is fixed before
the uniform permutation is drawn. -/
theorem missing_count {I : Type} [Fintype I] (t : Tree I) (hn : Nat.card I ≤ 2^512) :
    2^512 * Nat.card {π : Permutation // ¬ good t π} ≤
      (Nat.card I)^2 * Nat.card Permutation :=
  count_to_risk (good t) hn (good_count t)

end Reduction.ShakePermutation.Manifest
#print axioms Reduction.ShakePermutation.Manifest.missing_count
