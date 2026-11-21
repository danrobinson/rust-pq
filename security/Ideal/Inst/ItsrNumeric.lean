import Ideal.Inst.Itsr128

/-!
# A proven numeric bound on the ITSR coverage sum

`reuseSum h a k n` (the bound of `Ideal.itsr_bound_128s`) is at most

`n · (2^-a)^k · ∏_{i < k} (i + n / 2^h)`   (`reuseSum_le_prod`):

dropping the "coverer ≠ target" filter, the sum over assignments `f : Fin k → Fin n` of
`x ^ |image f|` is built one coordinate at a time; a new coordinate either repeats one of the at
most `i` values already used or contributes a factor `x` for one of `n` values.

Numbers at `(h, a, k) = (63, 12, 14)`:
* `n ≤ 7·2^63` (covers `q = qs = 2^64`, `n = q + 2(qs+1)`): `reuseSum ≤ 2^-50`;
* `n ≤ 2^61` (covers `q = 2^60`, `qs = 2^40`): `reuseSum ≤ 2^-72`;
* `n ≤ 2^41` (covers `q = 2^40`, `qs = 2^20`): `reuseSum ≤ 2^-112`.
These are upper bounds, not tight (the product over-counts the Stirling numbers).
-/

open ENNReal

namespace Ideal

/-- Sum over assignments of `x ^ |image|`. -/
noncomputable def imgSum (x : ℝ≥0∞) (k n : ℕ) : ℝ≥0∞ :=
  ∑ f : Fin k → Fin n, x ^ (Finset.univ.image f).card

theorem image_cons {k n : ℕ} (v : Fin n) (f : Fin k → Fin n) :
    Finset.univ.image (Fin.cons v f : Fin (k + 1) → Fin n) =
      insert v (Finset.univ.image f) := by
  ext w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · left; simp
    · right; exact ⟨j, by simp⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨0, by simp⟩
    · exact ⟨j.succ, by simp⟩

theorem imgSum_succ_le (x : ℝ≥0∞) (hx : x ≤ 1) (k n : ℕ) :
    imgSum x (k + 1) n ≤ ((k : ℝ≥0∞) + n * x) * imgSum x k n := by
  unfold imgSum
  rw [← (Fin.consEquiv fun _ : Fin (k + 1) => Fin n).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_le_sum fun f _ => ?_
  have hterm : ∀ v : Fin n,
      x ^ (Finset.univ.image (Fin.cons v f : Fin (k + 1) → Fin n)).card ≤
        ((if v ∈ Finset.univ.image f then 1 else 0) + x) * x ^ (Finset.univ.image f).card := by
    intro v
    rw [image_cons]
    by_cases hv : v ∈ Finset.univ.image f
    · rw [Finset.insert_eq_of_mem hv, if_pos hv]
      calc x ^ (Finset.univ.image f).card = 1 * x ^ (Finset.univ.image f).card := (one_mul _).symm
        _ ≤ _ := by gcongr; exact le_self_add
    · rw [Finset.card_insert_of_notMem hv, if_neg hv, zero_add, pow_succ, mul_comm]
  calc ∑ v : Fin n, x ^ (Finset.univ.image
          ((Fin.consEquiv fun _ : Fin (k + 1) => Fin n) (v, f))).card
      ≤ ∑ v : Fin n, ((if v ∈ Finset.univ.image f then (1 : ℝ≥0∞) else 0) + x) *
          x ^ (Finset.univ.image f).card := Finset.sum_le_sum fun v _ => hterm v
    _ = (((Finset.univ.image f).card : ℝ≥0∞) + n * x) * x ^ (Finset.univ.image f).card := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        simp
    _ ≤ ((k : ℝ≥0∞) + n * x) * x ^ (Finset.univ.image f).card := by
        gcongr
        calc (Finset.univ.image f).card ≤ (Finset.univ : Finset (Fin k)).card :=
              Finset.card_image_le
          _ = k := by simp

theorem imgSum_le_prod (x : ℝ≥0∞) (hx : x ≤ 1) (k n : ℕ) :
    imgSum x k n ≤ ∏ i ∈ Finset.range k, ((i : ℝ≥0∞) + n * x) := by
  induction k with
  | zero => simp [imgSum]
  | succ k ih =>
    rw [Finset.prod_range_succ, mul_comm]
    exact (imgSum_succ_le x hx k n).trans (by gcongr)

theorem reuseSum_le_prod (h a k n : ℕ) :
    reuseSum h a k n ≤ n * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k *
      ∏ i ∈ Finset.range k, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ h)⁻¹) := by
  have hx : ((2 : ℝ≥0∞) ^ h)⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (one_le_pow_of_one_le' (by norm_num) h)
  unfold reuseSum
  refine (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans ?_
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hE : (n : ℝ≥0∞) * ∑ f : Fin k → Fin n,
        (((2 : ℝ≥0∞) ^ h)⁻¹) ^ (Finset.univ.image f).card * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k
      = n * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k * imgSum (((2 : ℝ≥0∞) ^ h)⁻¹) k n := by
    unfold imgSum; rw [← Finset.sum_mul]; ring
  exact hE.le.trans (mul_le_mul le_rfl (imgSum_le_prod _ hx k n) zero_le zero_le)

theorem natMul_inv_pow_le (A B c : ℕ) (h : A * 2 ^ c ≤ 2 ^ B) :
    (A : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ B)⁻¹ ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := by
  rw [ENNReal.le_inv_iff_mul_le]
  have h' : (A : ℝ≥0∞) * 2 ^ c ≤ 2 ^ B := by exact_mod_cast h
  calc (A : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ B)⁻¹ * 2 ^ c = (A * 2 ^ c) * ((2 : ℝ≥0∞) ^ B)⁻¹ := by ring
    _ ≤ 2 ^ B * ((2 : ℝ≥0∞) ^ B)⁻¹ := mul_le_mul h' le_rfl zero_le zero_le
    _ = 1 := ENNReal.mul_inv_cancel (by positivity) (by simp)

theorem inv12_pow14 : (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 = ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
  rw [← ENNReal.inv_pow, ← pow_mul]

/-- `n ≤ 7·2^63` (e.g. `q = qs = 2^64`, `n = q + 2(qs+1)`): the coverage sum is at most `2^-50`. -/
theorem reuseSum_63_12_14_le_big (n : ℕ) (hn : n ≤ 7 * 2 ^ 63) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ 50)⁻¹ := by
  have hρ : (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ≤ 7 := by
    have h1 : (n : ℝ≥0∞) ≤ 7 * 2 ^ 63 := by exact_mod_cast hn
    calc (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ≤ 7 * 2 ^ 63 * ((2 : ℝ≥0∞) ^ 63)⁻¹ :=
          mul_le_mul h1 le_rfl zero_le zero_le
      _ = 7 := by rw [mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp), mul_one]
  have hP : ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹) ≤
      ((3379030566912000 : ℕ) : ℝ≥0∞) := by
    calc ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹)
        ≤ ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + 7) :=
          Finset.prod_le_prod' (fun i _ => add_le_add le_rfl hρ)
      _ = ((∏ i ∈ Finset.range 14, (i + 7) : ℕ) : ℝ≥0∞) := by push_cast; rfl
      _ = ((3379030566912000 : ℕ) : ℝ≥0∞) := by congr 1
  calc reuseSum 63 12 14 n
      ≤ n * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 *
          ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹) := reuseSum_le_prod _ _ _ _
    _ ≤ n * ((2 : ℝ≥0∞) ^ 168)⁻¹ * ((3379030566912000 : ℕ) : ℝ≥0∞) := by
        rw [inv12_pow14]; exact mul_le_mul le_rfl hP zero_le zero_le
    _ = ((n * 3379030566912000 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by push_cast; ring
    _ ≤ ((2 : ℝ≥0∞) ^ 50)⁻¹ := natMul_inv_pow_le _ _ _ (by
        calc n * 3379030566912000 * 2 ^ 50 ≤ 7 * 2 ^ 63 * 3379030566912000 * 2 ^ 50 := by gcongr
          _ ≤ 2 ^ 168 := by norm_num)

/-- `n ≤ 2^m ≤ 2^63`: the coverage sum is at most `2^-c` whenever `2m + 37 + c ≤ 231`. -/
theorem reuseSum_63_12_14_le_small (n m c : ℕ) (hn : n ≤ 2 ^ m) (hm : m ≤ 63)
    (hc : 2 * m + 37 + c ≤ 231) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := by
  set ρ : ℝ≥0∞ := (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 63)⁻¹ with hρdef
  have hρ : ρ ≤ 1 := by
    have h1 : (n : ℝ≥0∞) ≤ 2 ^ 63 := by
      exact_mod_cast hn.trans (Nat.pow_le_pow_right (by norm_num) hm)
    calc ρ ≤ 2 ^ 63 * ((2 : ℝ≥0∞) ^ 63)⁻¹ := mul_le_mul h1 le_rfl zero_le zero_le
      _ = 1 := ENNReal.mul_inv_cancel (by positivity) (by simp)
  have hP : ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + ρ) ≤ ((87178291200 : ℕ) : ℝ≥0∞) * ρ := by
    rw [Finset.prod_range_succ']
    refine mul_le_mul ?_ (by simp) zero_le zero_le
    calc ∏ i ∈ Finset.range 13, (((i + 1 : ℕ) : ℝ≥0∞) + ρ)
        ≤ ∏ i ∈ Finset.range 13, (((i + 1 : ℕ) : ℝ≥0∞) + 1) :=
          Finset.prod_le_prod' (fun i _ => add_le_add le_rfl hρ)
      _ = ((∏ i ∈ Finset.range 13, (i + 2) : ℕ) : ℝ≥0∞) := by
          push_cast; exact Finset.prod_congr rfl (fun i _ => by ring)
      _ = ((87178291200 : ℕ) : ℝ≥0∞) := by congr 1
  calc reuseSum 63 12 14 n
      ≤ n * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 * ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + ρ) :=
        reuseSum_le_prod _ _ _ _
    _ ≤ n * ((2 : ℝ≥0∞) ^ 168)⁻¹ * (((87178291200 : ℕ) : ℝ≥0∞) * ρ) := by
        rw [inv12_pow14]; exact mul_le_mul le_rfl hP zero_le zero_le
    _ = ((n * n * 87178291200 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 231)⁻¹ := by
        rw [hρdef, show (231 : ℕ) = 168 + 63 from rfl, pow_add,
          ENNReal.mul_inv (by simp) (by simp)]
        push_cast; ring
    _ ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := natMul_inv_pow_le _ _ _ (by
        calc n * n * 87178291200 * 2 ^ c ≤ 2 ^ m * 2 ^ m * 2 ^ 37 * 2 ^ c := by
              gcongr; norm_num
          _ = 2 ^ (2 * m + 37 + c) := by ring
          _ ≤ 2 ^ 231 := Nat.pow_le_pow_right (by norm_num) hc)

/-- `q = qs = 2^64`. -/
theorem reuseSum_q64_qs64 : reuseSum 63 12 14 (2 ^ 64 + 2 * (2 ^ 64 + 1)) ≤ ((2 : ℝ≥0∞) ^ 50)⁻¹ :=
  reuseSum_63_12_14_le_big _ (by norm_num)

/-- `q = 2^60`, `qs = 2^40`. -/
theorem reuseSum_q60_qs40 : reuseSum 63 12 14 (2 ^ 60 + 2 * (2 ^ 40 + 1)) ≤ ((2 : ℝ≥0∞) ^ 72)⁻¹ :=
  reuseSum_63_12_14_le_small _ 61 72 (by norm_num) (by norm_num) (by norm_num)

/-- `q = 2^40`, `qs = 2^20`. -/
theorem reuseSum_q40_qs20 :
    reuseSum 63 12 14 (2 ^ 40 + 2 * (2 ^ 20 + 1)) ≤ ((2 : ℝ≥0∞) ^ 112)⁻¹ :=
  reuseSum_63_12_14_le_small _ 41 112 (by norm_num) (by norm_num) (by norm_num)

end Ideal

#print axioms Ideal.reuseSum_le_prod
#print axioms Ideal.reuseSum_q64_qs64
#print axioms Ideal.reuseSum_q60_qs40
#print axioms Ideal.reuseSum_q40_qs20
