import Integration.SlhDsaComposedClosed

/-!
# Numeric evaluation of the closed composed bound

NOT part of the default target; compiled like the other `Integration/*.lean` files.

`Num.composedBoundFinal_num`: `composedBoundFinal (2^40) (2^20) (openCounts128s (2^20)).noPrfMsg
≤ 2^-22`.  Honest arithmetic: the ITSR term is bounded by `(2^-40 + 6·2^-14)²` (cover sum
`≤ 2·2^-168` via `C(s,γ) ≤ s^γ`, Bernoulli `1-(1-t)^γ ≤ γt`, `γ ≤ 2^γ` and a geometric series;
`2q'+1 ≤ 2^43`, `2q' ≤ 6·2^40` for `q' = q + (openCounts128s qs).itsr`), every other of the 27
weighted terms by `2^-37`; total `≤ 36.001·2^-28 + 27·2^-37 < 2^-22` (the ITSR reprogramming term
`(2q'·√(qs/2^128))² ≈ 2^-22.9` dominates; `k = 22` is the best integer exponent from these bounds).

`…_qrom_enc_closed_num`: the closed headlines at `q = 2^40`, `qs = 2^20`: forgery probability
`≤ 2^-22` for every port forger with at most `2^40` port calls and `2^20` signing queries.
-/
open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum Reduction

namespace Reduction.Num

theorem one_sub_one_sub_pow_le (t : ℝ≥0∞) (_ht : t ≤ 1) (γ : ℕ) :
    1 - (1 - t) ^ γ ≤ γ * t := by
  induction γ with
  | zero => simp
  | succ n ih =>
    have hu : (1 - t) ^ n ≤ 1 := pow_le_one₀ zero_le tsub_le_self
    have hne : (1 - t) ^ n ≠ ⊤ := ne_top_of_le_ne_top one_ne_top hu
    rw [pow_succ, ENNReal.mul_sub (fun _ _ ↦ hne), mul_one]
    calc 1 - ((1 - t) ^ n - (1 - t) ^ n * t) ≤ 1 - (1 - t) ^ n + (1 - t) ^ n * t :=
          tsub_tsub_le_tsub_add
      _ ≤ n * t + 1 * t := add_le_add ih (mul_le_mul' hu le_rfl)
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * t := by push_cast; ring

/-- The cover sum of `epsItsr` is at most `2 t^k` once `s p 2^k ≤ 1/2`. -/
theorem cover_sum_le (s k : ℕ) (p t : ℝ≥0∞) (ht : t ≤ 1)
    (hr : (s : ℝ≥0∞) * p * 2 ^ k ≤ 2⁻¹) :
    ∑ γ ∈ Finset.range (s + 1),
        (s.choose γ : ℝ≥0∞) * p ^ γ * (1 - p) ^ (s - γ) * (1 - (1 - t) ^ γ) ^ k ≤
      2 * t ^ k := by
  have hterm : ∀ γ, (s.choose γ : ℝ≥0∞) * p ^ γ * (1 - p) ^ (s - γ) * (1 - (1 - t) ^ γ) ^ k ≤
      (2⁻¹) ^ γ * t ^ k := by
    intro γ
    have h1 : (s.choose γ : ℝ≥0∞) ≤ (s : ℝ≥0∞) ^ γ := by exact_mod_cast Nat.choose_le_pow s γ
    have h2 : (1 - p) ^ (s - γ) ≤ 1 := pow_le_one₀ zero_le tsub_le_self
    have h3 : (1 - (1 - t) ^ γ) ^ k ≤ ((2 : ℝ≥0∞) ^ k) ^ γ * t ^ k := by
      calc (1 - (1 - t) ^ γ) ^ k ≤ ((γ : ℝ≥0∞) * t) ^ k :=
            pow_le_pow_left₀ zero_le (one_sub_one_sub_pow_le t ht γ) k
        _ ≤ ((2 : ℝ≥0∞) ^ γ * t) ^ k := by
            gcongr
            exact_mod_cast (Nat.lt_two_pow_self).le
        _ = ((2 : ℝ≥0∞) ^ k) ^ γ * t ^ k := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm γ k]
    calc (s.choose γ : ℝ≥0∞) * p ^ γ * (1 - p) ^ (s - γ) * (1 - (1 - t) ^ γ) ^ k
        ≤ (s : ℝ≥0∞) ^ γ * p ^ γ * 1 * (((2 : ℝ≥0∞) ^ k) ^ γ * t ^ k) := by gcongr
      _ = ((s : ℝ≥0∞) * p * 2 ^ k) ^ γ * t ^ k := by rw [mul_one, mul_pow, mul_pow]; ring
      _ ≤ (2⁻¹) ^ γ * t ^ k := by gcongr
  calc _ ≤ ∑ γ ∈ Finset.range (s + 1), (2⁻¹ : ℝ≥0∞) ^ γ * t ^ k := Finset.sum_le_sum fun γ _ ↦ hterm γ
    _ = (∑ γ ∈ Finset.range (s + 1), (2⁻¹ : ℝ≥0∞) ^ γ) * t ^ k := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑' γ : ℕ, (2⁻¹ : ℝ≥0∞) ^ γ) * t ^ k := by
        gcongr
        exact ENNReal.sum_le_tsum _
    _ = 2 * t ^ k := by rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]

theorem two_pow_mul_inv (a b : ℕ) (h : a ≤ b) :
    (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ b)⁻¹ = ((2 : ℝ≥0∞) ^ (b - a))⁻¹ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, pow_add, ENNReal.mul_inv (Or.inl (by positivity))
    (Or.inl (by simp)), ← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp), one_mul]

theorem inv_two_pow_le (a b : ℕ) (h : a ≤ b) : ((2 : ℝ≥0∞) ^ b)⁻¹ ≤ ((2 : ℝ≥0∞) ^ a)⁻¹ :=
  ENNReal.inv_le_inv.2 (pow_le_pow_right₀ one_le_two h)

theorem inv_two_pow_pow (a k : ℕ) : (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k = ((2 : ℝ≥0∞) ^ (a * k))⁻¹ := by
  rw [ENNReal.inv_pow, ← pow_mul, ENNReal.inv_pow]

theorem sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ (2⁻¹ : ℝ) = x := by
  simpa using ENNReal.pow_rpow_inv_natCast (n := 2) two_ne_zero x

theorem inv_two_pow_eq (n : ℕ) : ((2 : ℝ≥0∞) ^ n)⁻¹ = ENNReal.ofReal ((2 ^ n : ℝ)⁻¹) := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
    ENNReal.ofReal_ofNat]


/-- The ITSR term once `s = 2^20`, `2q+1 ≤ 2^43`, `2q ≤ 6·2^40` (SHA2-128s tree shape). -/
theorem epsItsr_num (P : SLHDSA.Params) (hh : P.h = 63) (ha : P.a = 12) (hk : P.k = 14)
    (q s : ℕ) (hs : s = 2 ^ 20) (hq1 : 2 * q + 1 ≤ 2 ^ 43) (hq2 : 2 * q ≤ 6 * 2 ^ 40) :
    epsItsr P q s ≤ (((2 : ℝ≥0∞) ^ 40)⁻¹ + 6 * ((2 : ℝ≥0∞) ^ 14)⁻¹) ^ 2 := by
  have hC := cover_sum_le s 14 (((2 : ℝ≥0∞) ^ 63)⁻¹) (((2 : ℝ≥0∞) ^ 12)⁻¹)
    (ENNReal.inv_le_one.2 (one_le_pow₀ one_le_two)) (by
      rw [hs]
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      rw [mul_right_comm, ← pow_add, two_pow_mul_inv _ _ (by norm_num)]
      simpa using inv_two_pow_le 1 29 (by norm_num))
  have hX : 2 * (q : ℝ≥0∞) + 1 ≤ 2 ^ 43 := by exact_mod_cast hq1
  have h2q : 2 * (q : ℝ≥0∞) ≤ 6 * 2 ^ 40 := by exact_mod_cast hq2
  have hA : (2 * (q : ℝ≥0∞) + 1) ^ 2 *
      (∑ γ ∈ Finset.range (s + 1),
        (s.choose γ : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ 63)⁻¹) ^ γ *
          (1 - ((2 : ℝ≥0∞) ^ 63)⁻¹) ^ (s - γ) *
          (1 - (1 - ((2 : ℝ≥0∞) ^ 12)⁻¹) ^ γ) ^ 14) ≤ (((2 : ℝ≥0∞) ^ 40)⁻¹) ^ 2 := by
    calc _ ≤ ((2 : ℝ≥0∞) ^ 43) ^ 2 * (2 * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14) := by gcongr
      _ = (2 : ℝ≥0∞) ^ 87 * ((2 : ℝ≥0∞) ^ 168)⁻¹ := by
          rw [inv_two_pow_pow, ← mul_assoc, ← pow_mul, ← pow_succ]
      _ = ((2 : ℝ≥0∞) ^ 81)⁻¹ := two_pow_mul_inv _ _ (by norm_num)
      _ ≤ ((2 : ℝ≥0∞) ^ 80)⁻¹ := inv_two_pow_le _ _ (by norm_num)
      _ = (((2 : ℝ≥0∞) ^ 40)⁻¹) ^ 2 := by rw [inv_two_pow_pow]
  have hS : (s : ℝ≥0∞) * N128⁻¹ = (((2 : ℝ≥0∞) ^ 54)⁻¹) ^ 2 := by
    rw [N128, inv_two_pow_pow, hs]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact two_pow_mul_inv _ _ (by norm_num)
  unfold epsItsr
  rw [hh, ha, hk, hS, sq_rpow_half]
  refine pow_le_pow_left₀ zero_le (add_le_add ?_ ?_) 2
  · exact (ENNReal.rpow_le_rpow hA (by norm_num)).trans (le_of_eq (sq_rpow_half _))
  · calc 2 * (q : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 54)⁻¹
        ≤ 6 * 2 ^ 40 * ((2 : ℝ≥0∞) ^ 54)⁻¹ := by gcongr
      _ = 6 * ((2 : ℝ≥0∞) ^ 14)⁻¹ := by rw [mul_assoc, two_pow_mul_inv _ _ (by norm_num)]


/-- One term of the composed bound: at most `2^-37`. -/
noncomputable abbrev E37 : ℝ≥0∞ := ENNReal.ofReal ((2 ^ 37 : ℝ)⁻¹)

theorem epsTcr0_le_E (n : ℕ) (h : (2 * (n : ℝ) + 1) ^ 2 / 2 ^ 128 ≤ (2 ^ 37 : ℝ)⁻¹) :
    epsTcr0 n ≤ E37 := by
  rw [epsTcr0_eq]; exact ENNReal.ofReal_le_ofReal h

theorem epsPre0_le_E (n : ℕ) (h : (2 * (n : ℝ) + 1) ^ 2 / 2 ^ 128 ≤ (2 ^ 37 : ℝ)⁻¹) :
    epsPre0 n ≤ 2 * E37 := by
  have e : epsPre0 n = 2 * epsTcr0 n := by
    unfold epsPre0 epsTcr0
    rw [div_eq_mul_inv]
    ring
  rw [e]
  exact mul_le_mul' le_rfl (epsTcr0_le_E n h)

/-- **Numeric evaluation of the composed bound** at `q = 2^40` forger queries and `qs = 2^20`
signatures, at the counts `(openCounts128s qs).noPrfMsg` of the closed headline: `≤ 2^-22`. -/
theorem composedBoundFinal_num :
    composedBoundFinal (2 ^ 40) (2 ^ 20) (openCounts128s (2 ^ 20)).noPrfMsg ≤
      ((2 : ℝ≥0∞) ^ 22)⁻¹ := by
  have hw : ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) = 14 := by
    have : Link.vp.params.w - 2 = 14 := rfl
    rw [this]; norm_num
  have hI := epsItsr_num Link.vp.params rfl rfl rfl (2 ^ 40 + (269824 + 2 ^ 20 * 2007385)) (2 ^ 20)
    rfl (by norm_num) (by norm_num)
  have hJ : (((2 : ℝ≥0∞) ^ 40)⁻¹ + 6 * ((2 : ℝ≥0∞) ^ 14)⁻¹) ^ 2 =
      ENNReal.ofReal ((((2 : ℝ) ^ 40)⁻¹ + 6 * ((2 : ℝ) ^ 14)⁻¹) ^ 2) := by
    rw [inv_two_pow_eq, inv_two_pow_eq, ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  unfold composedBoundFinal
  rw [hw]
  simp only [RedCounts.noPrfMsg, openCounts128s]
  calc _ ≤ E37 + E37 + ENNReal.ofReal ((((2 : ℝ) ^ 40)⁻¹ + 6 * ((2 : ℝ) ^ 14)⁻¹) ^ 2) +
        (E37 + 3 * E37) + (E37 + E37 + E37 + E37) + 14 * E37 + 2 * E37 + E37 := by
        gcongr
        · unfold epsPrf; exact ENNReal.ofReal_le_ofReal (by norm_num)
        · unfold epsPrf; exact ENNReal.ofReal_le_ofReal (by norm_num)
        · exact hI.trans (le_of_eq hJ)
        · unfold epsDsprTight; exact ENNReal.ofReal_le_ofReal (by norm_num)
        · exact epsTcr0_le_E _ (by norm_num)
        · exact epsTcr0_le_E _ (by norm_num)
        · exact epsTcr0_le_E _ (by norm_num)
        · exact epsTcr0_le_E _ (by norm_num)
        · exact epsTcr0_le_E _ (by norm_num)
        · unfold epsUdTight; exact ENNReal.ofReal_le_ofReal (by norm_num)
        · exact epsPre0_le_E _ (by norm_num)
        · exact epsTcr0_le_E _ (by norm_num)
    _ = ENNReal.ofReal ((((2 : ℝ) ^ 40)⁻¹ + 6 * ((2 : ℝ) ^ 14)⁻¹) ^ 2) + 27 * E37 := by ring
    _ = ENNReal.ofReal ((((2 : ℝ) ^ 40)⁻¹ + 6 * ((2 : ℝ) ^ 14)⁻¹) ^ 2 +
          27 * (2 ^ 37 : ℝ)⁻¹) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
          ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal ((2 ^ 22 : ℝ)⁻¹) := ENNReal.ofReal_le_ofReal (by norm_num)
    _ = ((2 : ℝ≥0∞) ^ 22)⁻¹ := (inv_two_pow_eq 22).symm

end Reduction.Num

namespace Reduction

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- **SUF-CMA at `2^40` quantum hash queries and `2^20` signatures: forgery probability
`≤ 2^-22`.** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed_num
    (F : PortForger (EncX c) EncY E)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2 ^ 40))
    (hqs : ∀ pk, CountBound isSign (F.main pk) (2 ^ 20))
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      ((2 : ℝ≥0∞) ^ 22)⁻¹ :=
  (slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed c optRand₀ pkSeedDist₀ F _ _
    hq hqs hcap htl).trans Num.composedBoundFinal_num

/-- **EUF-CMA at `2^40` quantum hash queries and `2^20` signatures: forgery probability
`≤ 2^-22`.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed_num
    (F : PortForger (EncX c) EncY E)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2 ^ 40))
    (hqs : ∀ pk, CountBound isSign (F.main pk) (2 ^ 20))
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      ((2 : ℝ≥0∞) ^ 22)⁻¹ :=
  (slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed c optRand₀ pkSeedDist₀ F _ _
    hq hqs hcap htl).trans Num.composedBoundFinal_num

end Reduction

#print axioms Reduction.Num.cover_sum_le
#print axioms Reduction.Num.epsItsr_num
#print axioms Reduction.Num.composedBoundFinal_num
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc_closed_num
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc_closed_num
