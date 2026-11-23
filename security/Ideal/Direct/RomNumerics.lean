import Ideal.Direct.RomCompose

/-!
# Numerics of the ROM route (`status/DIRECT.md` §10)

* `wTCB_le_simple`: `weightedTargetCoverBound h a k qs qw w ≤
  Σ_{r ≤ k} r^k (qs+1)^r / r! · 2^{-h r} 2^{-a k}` whenever `qw · w ≤ 1` (surjections counted
  as all maps, `C(n, j) ≤ n^j / j!`, binomial theorem).
* `securityBound_mono`, `epsHop_mono`: monotonicity in the budgets.
* `epsRom_2_20`, `epsRom_2_40`, `epsRom_2_64`: the bound of the route at
  `(qf ≤ 2^60, qs ≤ 2^20)`, `(2^64, 2^40)`, `(2^64, 2^64)`, messages `≤ 2^26` bytes:
  `2^-67 + 2^-107`, `2^-63 + 2^-87`, `2^-63 + 2^-64 + 2^-66`.
* `suf_rom_2_20`, …: the point bounds on `sufI` **under the hop** (`MDHopSuf`).
* `epsRom_lt_tight8_2_20`, …: these are strictly below the proved tight8 point bounds
  `2^-77 + 2^-132 + 2^-63`, `2^-63 + 2^-94 + 2^-59`, `2^-45 + 2^-46 + 2^-39`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal
open KeyedHash.Covering

namespace Ideal.Direct.Rom

open Ideal.Realize

/-! ## The weighted coverage bound, simplified -/

section Cover

variable (h a k : ℕ)

theorem card_surj_le (r : ℕ) :
    ((Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card : ℝ≥0∞) ≤
      ((r ^ k : ℕ) : ℝ≥0∞) := by
  have := Finset.card_filter_le (Finset.univ : Finset (Fin k → Fin r))
    (fun s => Function.Surjective s)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at this
  exact_mod_cast this

theorem binom_reflect (qs r : ℕ) :
    (qs + 1) ^ r = ∑ j ∈ Finset.range (r + 1), r.choose j * qs ^ (r - j) := by
  rw [add_pow]
  simp only [one_pow, mul_one]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : r + 1 - 1 - j = r - j := by omega
  rw [e, Nat.choose_symm hj']
  simp [mul_comm]

theorem term_le (qs qw r j : ℕ) (hj : j ≤ r) :
    r.factorial * (qs.choose (r - j) * qw.choose j) ≤ r.choose j * qs ^ (r - j) * qw ^ j := by
  have hf := Nat.choose_mul_factorial_mul_factorial hj
  have h1 : (r - j).factorial * qs.choose (r - j) ≤ qs ^ (r - j) := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow _ _
  have h2 : j.factorial * qw.choose j ≤ qw ^ j := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]; exact Nat.descFactorial_le_pow _ _
  calc r.factorial * (qs.choose (r - j) * qw.choose j)
      = r.choose j * ((r - j).factorial * qs.choose (r - j)) * (j.factorial * qw.choose j) := by
        rw [← hf]; ring
    _ ≤ r.choose j * qs ^ (r - j) * qw ^ j := by gcongr

/-- `r! · Σ_j C(qs, r-j) C(qw, j) w^j ≤ (qs + 1)^r` when `qw · w ≤ 1`. -/
theorem fact_mul_sum_le (qs qw r : ℕ) (w : ℝ≥0∞) (hw : (qw : ℝ≥0∞) * w ≤ 1) :
    (r.factorial : ℝ≥0∞) * ∑ j ∈ Finset.range (r + 1),
        ((qs.choose (r - j) * qw.choose j : ℕ) : ℝ≥0∞) * w ^ j ≤ ((qs + 1) ^ r : ℕ) := by
  rw [Finset.mul_sum, binom_reflect, Nat.cast_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have ht : ((r.factorial * (qs.choose (r - j) * qw.choose j) : ℕ) : ℝ≥0∞) ≤
      ((r.choose j * qs ^ (r - j) : ℕ) : ℝ≥0∞) * (qw : ℝ≥0∞) ^ j := by
    have := term_le qs qw r j hj'
    exact_mod_cast this
  calc (r.factorial : ℝ≥0∞) * (((qs.choose (r - j) * qw.choose j : ℕ) : ℝ≥0∞) * w ^ j)
      = ((r.factorial * (qs.choose (r - j) * qw.choose j) : ℕ) : ℝ≥0∞) * w ^ j := by
        push_cast; ring
    _ ≤ ((r.choose j * qs ^ (r - j) : ℕ) : ℝ≥0∞) * (qw : ℝ≥0∞) ^ j * w ^ j := by gcongr
    _ = ((r.choose j * qs ^ (r - j) : ℕ) : ℝ≥0∞) * ((qw : ℝ≥0∞) * w) ^ j := by
        rw [mul_pow, mul_assoc]
    _ ≤ ((r.choose j * qs ^ (r - j) : ℕ) : ℝ≥0∞) * 1 := by
        gcongr; exact pow_le_one₀ zero_le hw
    _ = _ := mul_one _

/-- **The weighted coverage bound, simplified**: surjections counted as all maps and
`C(n, j) ≤ n^j / j!`, when the weighted positions have total weight `qw · w ≤ 1`. -/
theorem wTCB_le_simple (qs qw : ℕ) (w : ℝ≥0∞) (hw : (qw : ℝ≥0∞) * w ≤ 1) :
    weightedTargetCoverBound h a k qs qw w ≤
      ∑ r ∈ Finset.range (k + 1), ((r ^ k * (qs + 1) ^ r : ℕ) : ℝ≥0∞) / (r.factorial : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k) := by
  unfold weightedTargetCoverBound
  refine Finset.sum_le_sum fun r _ => ?_
  set c := (((2 : ℝ≥0∞) ^ h)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ a)⁻¹) ^ k
  set sj := ((Finset.univ.filter fun s : Fin k → Fin r => Function.Surjective s).card : ℕ)
  have hsum : ∑ j ∈ Finset.range (r + 1),
      ((qs.choose (r - j) * qw.choose j * sj : ℕ) : ℝ≥0∞) * w ^ j * c =
      (sj : ℝ≥0∞) * c * ∑ j ∈ Finset.range (r + 1),
        ((qs.choose (r - j) * qw.choose j : ℕ) : ℝ≥0∞) * w ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [hsum]
  have hfac : (r.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have hfac' : (r.factorial : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hS : ∑ j ∈ Finset.range (r + 1), ((qs.choose (r - j) * qw.choose j : ℕ) : ℝ≥0∞) * w ^ j ≤
      ((qs + 1) ^ r : ℕ) / (r.factorial : ℝ≥0∞) := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl hfac) (Or.inl hfac'), mul_comm]
    exact fact_mul_sum_le qs qw r w hw
  calc (sj : ℝ≥0∞) * c * ∑ j ∈ Finset.range (r + 1),
        ((qs.choose (r - j) * qw.choose j : ℕ) : ℝ≥0∞) * w ^ j
      ≤ ((r ^ k : ℕ) : ℝ≥0∞) * c * (((qs + 1) ^ r : ℕ) / (r.factorial : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast card_surj_le k r
    _ = ((r ^ k * (qs + 1) ^ r : ℕ) : ℝ≥0∞) / (r.factorial : ℝ≥0∞) * c := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; push_cast; ring

end Cover

/-! ## Fractions with power-of-two denominators -/

section Frac

theorem two_pow_ne_zero' (e : ℕ) : ((2 : ℝ≥0∞) ^ e) ≠ 0 := pow_ne_zero _ two_ne_zero
theorem two_pow_ne_top' (e : ℕ) : ((2 : ℝ≥0∞) ^ e) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top

/-- Moving a fraction to the denominator `2^D`. -/
theorem frac_toD (n e D : ℕ) (he : e ≤ D) :
    (n : ℝ≥0∞) / 2 ^ e = ((n * 2 ^ (D - e) : ℕ) : ℝ≥0∞) / 2 ^ D := by
  have hD : (2 : ℝ≥0∞) ^ D = 2 ^ e * 2 ^ (D - e) := by rw [← pow_add, Nat.add_sub_cancel' he]
  rw [hD, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_div_mul_right _ _ (two_pow_ne_zero' _) (two_pow_ne_top' _)]

theorem inv_toD (e D : ℕ) (he : e ≤ D) :
    ((2 : ℝ≥0∞) ^ e)⁻¹ = ((2 ^ (D - e) : ℕ) : ℝ≥0∞) / 2 ^ D := by
  rw [← one_div, ← Nat.cast_one, frac_toD 1 e D he, one_mul]

theorem frac_add (m n D : ℕ) :
    (m : ℝ≥0∞) / 2 ^ D + (n : ℝ≥0∞) / 2 ^ D = ((m + n : ℕ) : ℝ≥0∞) / 2 ^ D := by
  rw [Nat.cast_add, ENNReal.add_div]

theorem frac_mono {m n D : ℕ} (h : m ≤ n) : (m : ℝ≥0∞) / 2 ^ D ≤ (n : ℝ≥0∞) / 2 ^ D := by
  gcongr

/-- A fraction `A / B` is at most `n / 2^E` when `A · 2^E ≤ n · B`. -/
theorem frac_le_of {A B n E : ℕ} (hB : 0 < B) (h : A * 2 ^ E ≤ n * B) :
    (A : ℝ≥0∞) / B ≤ (n : ℝ≥0∞) / 2 ^ E := by
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by exact_mod_cast hB.ne'
  have hBt : (B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [ENNReal.div_le_iff hB0 hBt, ENNReal.div_eq_inv_mul, mul_assoc, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero' E)) (Or.inl (two_pow_ne_top' E))]
  have : ((A * 2 ^ E : ℕ) : ℝ≥0∞) ≤ ((n * B : ℕ) : ℝ≥0∞) := by exact_mod_cast h
  simpa [mul_comm, mul_left_comm, mul_assoc] using this

end Frac

/-! ## The coverage term at SLH-DSA-SHA2-128s -/

section Cover128

/-- The `r`-th numerator over the common denominator `2^1050`: an upper rounding of
`r^14 (qs+1)^r · 2^{63(14-r)} / r!`. -/
def nr (qs r : ℕ) : ℕ := r ^ 14 * (qs + 1) ^ r * 2 ^ (63 * (14 - r)) / r.factorial + 1

theorem cover_term_le (qs r : ℕ) (hr : r ≤ 14) :
    ((r ^ 14 * (qs + 1) ^ r : ℕ) : ℝ≥0∞) / (r.factorial : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ 63)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14) ≤
      (nr qs r : ℝ≥0∞) / 2 ^ 1050 := by
  have hB : 0 < r.factorial * 2 ^ (63 * r + 168) := by positivity
  have hc : (((2 : ℝ≥0∞) ^ 63)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 =
      ((2 : ℝ≥0∞) ^ (63 * r + 168))⁻¹ := by
    rw [show 63 * r + 168 = 63 * r + 12 * 14 by rfl, pow_add,
      ENNReal.mul_inv (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top' _)), pow_mul,
      pow_mul, ← ENNReal.inv_pow, ← ENNReal.inv_pow]
  have hf0 : (r.factorial : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.factorial_pos r).ne'
  have e1 : ((r ^ 14 * (qs + 1) ^ r : ℕ) : ℝ≥0∞) / (r.factorial : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ 63)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14) =
      ((r ^ 14 * (qs + 1) ^ r : ℕ) : ℝ≥0∞) / ((r.factorial * 2 ^ (63 * r + 168) : ℕ) : ℝ≥0∞) := by
    rw [hc, div_eq_mul_inv, div_eq_mul_inv]
    push_cast
    rw [ENNReal.mul_inv (Or.inl hf0) (Or.inl (ENNReal.natCast_ne_top _))]
    ring
  rw [e1]
  refine frac_le_of hB ?_
  set A := r ^ 14 * (qs + 1) ^ r
  have hsplit : 2 ^ 1050 = 2 ^ (63 * (14 - r)) * 2 ^ (63 * r + 168) := by
    rw [← pow_add]; congr 1; omega
  have hm : A * 2 ^ (63 * (14 - r)) ≤ nr qs r * r.factorial := by
    have := Nat.lt_div_mul_add (a := A * 2 ^ (63 * (14 - r))) (Nat.factorial_pos r)
    unfold nr; rw [add_mul, one_mul]; exact this.le
  calc A * 2 ^ 1050 = A * 2 ^ (63 * (14 - r)) * 2 ^ (63 * r + 168) := by rw [hsplit]; ring
    _ ≤ nr qs r * r.factorial * 2 ^ (63 * r + 168) := Nat.mul_le_mul_right _ hm
    _ = nr qs r * (r.factorial * 2 ^ (63 * r + 168)) := by ring

/-- **The coverage term at SLH-DSA-SHA2-128s**, for `qh · qs ≤ 2^128`:
`wTCB(63, 12, 14; qs, qh, qs/2^128) ≤ (Σ_{r ≤ 14} nr qs r) / 2^1050`. -/
theorem wTCB_128s_le (qs qh : ℕ) (hw : qh * qs ≤ 2 ^ 128) :
    weightedTargetCoverBound Link.vp.params.h Link.vp.params.a Link.vp.params.k qs qh
        ((qs : ℝ≥0∞) / ((256 ^ 16 : ℕ) : ℝ≥0∞)) ≤
      ((∑ r ∈ Finset.range 15, nr qs r : ℕ) : ℝ≥0∞) / 2 ^ 1050 := by
  have hw' : (qh : ℝ≥0∞) * ((qs : ℝ≥0∞) / ((256 ^ 16 : ℕ) : ℝ≥0∞)) ≤ 1 := by
    rw [← mul_div_assoc, ENNReal.div_le_iff (by norm_num) (ENNReal.natCast_ne_top _), one_mul]
    exact_mod_cast hw.trans (by norm_num)
  refine (wTCB_le_simple _ _ _ qs qh _ hw').trans ?_
  change ∑ r ∈ Finset.range (14 + 1), ((r ^ 14 * (qs + 1) ^ r : ℕ) : ℝ≥0∞) / (r.factorial : ℝ≥0∞) *
        ((((2 : ℝ≥0∞) ^ 63)⁻¹) ^ r * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14) ≤ _
  rw [Nat.cast_sum, ENNReal.div_eq_inv_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  rw [← ENNReal.div_eq_inv_mul]
  exact cover_term_le qs r (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))

theorem nr_mono {qs Qs : ℕ} (h : qs ≤ Qs) (r : ℕ) : nr qs r ≤ nr Qs r := by
  unfold nr
  gcongr

end Cover128

/-! ## The bound of the route at a point -/

section Point

/-- The cell count at the caps. -/
def QCap (Qf Qs : ℕ) : ℕ := Qf + (Qs + 1) * (2 ^ 25 + 2 * 2 ^ 20) + 2 * (17920 + Qs * 182784)

theorem QAll_le {qf qs ℓ Qf Qs : ℕ} (hf : qf ≤ Qf) (hs : qs ≤ Qs) (hℓ : ℓ ≤ 2 ^ 26) :
    QAll qf qs ℓ ≤ QCap Qf Qs := by
  have h1 : (ℓ + 56) / 64 ≤ 2 ^ 20 := by
    have := Nat.div_le_div_right (c := 64) (Nat.add_le_add_right hℓ 56)
    have h2 : (2 ^ 26 + 56) / 64 = 2 ^ 20 := by norm_num
    omega
  unfold QAll QcAll QCap
  rw [Prf.qOPrf_128s]
  gcongr

/-- The numerator of the route's bound over `2^1050` at the caps `(Qf, Qs)`, messages of at most
`2^26` bytes. -/
def numRom (Qf Qs : ℕ) : ℕ :=
  (Qf + 1) * (∑ r ∈ Finset.range 15, nr Qs r) + (2 * Qf + 7858) * 2 ^ 922 +
    (QCap Qf Qs + 1) ^ 2 * 2 ^ 796 + Qs * 2 ^ 922

/-- **The bound of the route at a point**, as one fraction over `2^1050`. -/
theorem epsRom_le_num {qf qs ℓ Qf Qs : ℕ} (hf : qf ≤ Qf) (hs : qs ≤ Qs) (hℓ : ℓ ≤ 2 ^ 26)
    (hw : Qf * Qs ≤ 2 ^ 128) :
    epsRom qf qs ℓ ≤ (numRom Qf Qs : ℝ≥0∞) / 2 ^ 1050 := by
  have hw' : qf * qs ≤ 2 ^ 128 := (Nat.mul_le_mul hf hs).trans hw
  have hV : GeneralScheme.verifyInternalQueryBound Link.vp.params = 3929 := by decide
  -- the coverage term
  have hcov : ((qf : ℝ≥0∞) + 1) * weightedTargetCoverBound Link.vp.params.h Link.vp.params.a
      Link.vp.params.k qs qf ((qs : ℝ≥0∞) / ((256 ^ 16 : ℕ) : ℝ≥0∞)) ≤
      (((Qf + 1) * ∑ r ∈ Finset.range 15, nr Qs r : ℕ) : ℝ≥0∞) / 2 ^ 1050 := by
    calc _ ≤ ((qf : ℝ≥0∞) + 1) * (((∑ r ∈ Finset.range 15, nr qs r : ℕ) : ℝ≥0∞) / 2 ^ 1050) := by
          gcongr; exact wTCB_128s_le qs qf hw'
      _ ≤ ((Qf : ℝ≥0∞) + 1) * (((∑ r ∈ Finset.range 15, nr Qs r : ℕ) : ℝ≥0∞) / 2 ^ 1050) := by
          gcongr
          exact nr_mono hs _
      _ = _ := by rw [← mul_div_assoc]; push_cast; ring_nf
  -- the linear term
  have hlin : ((2 : ℕ) * (qf : ℝ≥0∞) + (((1 + 1) * GeneralScheme.verifyInternalQueryBound
      Link.vp.params : ℕ) : ℝ≥0∞)) * ((256 ^ 16 : ℕ) : ℝ≥0∞)⁻¹ ≤
      (((2 * Qf + 7858) * 2 ^ 922 : ℕ) : ℝ≥0∞) / 2 ^ 1050 := by
    have e : ((256 ^ 16 : ℕ) : ℝ≥0∞) = 2 ^ 128 := by norm_num
    have hn : ((2 : ℕ) * (qf : ℝ≥0∞) + (((1 + 1) * GeneralScheme.verifyInternalQueryBound
        Link.vp.params : ℕ) : ℝ≥0∞)) ≤ ((2 * Qf + 7858 : ℕ) : ℝ≥0∞) := by
      rw [hV]
      have : 2 * qf + (1 + 1) * 3929 ≤ 2 * Qf + 7858 := by omega
      exact_mod_cast this
    rw [← frac_toD _ 128 1050 (by norm_num), ← div_eq_mul_inv, e]
    gcongr
  -- the hop
  have hhop : epsHop qf qs ℓ ≤ (((QCap Qf Qs + 1) ^ 2 * 2 ^ 796 : ℕ) : ℝ≥0∞) / 2 ^ 1050 +
      ((Qs * 2 ^ 922 : ℕ) : ℝ≥0∞) / 2 ^ 1050 := by
    unfold epsHop
    rw [← frac_toD _ 254 1050 (by norm_num), ← frac_toD _ 128 1050 (by norm_num)]
    have hQ := QAll_le hf hs hℓ
    gcongr
  unfold epsRom securityBound
  refine (add_le_add (add_le_add hcov hlin) hhop).trans (le_of_eq ?_)
  unfold numRom
  simp only [Nat.cast_add, ENNReal.add_div]
  ring

set_option exponentiation.threshold 1200 in
theorem num_2_20 : numRom (2 ^ 60) (2 ^ 20) ≤ 2 ^ 983 + 2 ^ 943 := by
  unfold numRom QCap nr
  norm_num [Finset.sum_range_succ, Nat.factorial]

set_option exponentiation.threshold 1200 in
theorem num_2_40 : numRom (2 ^ 64) (2 ^ 40) ≤ 2 ^ 987 + 2 ^ 963 := by
  unfold numRom QCap nr
  norm_num [Finset.sum_range_succ, Nat.factorial]

set_option exponentiation.threshold 1200 in
theorem num_2_64 : numRom (2 ^ 64) (2 ^ 64) ≤ 2 ^ 987 + 2 ^ 986 + 2 ^ 984 := by
  unfold numRom QCap nr
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem frac_pow_two (e D : ℕ) (he : e ≤ D) :
    ((2 ^ (D - e) : ℕ) : ℝ≥0∞) / 2 ^ D = ((2 : ℝ≥0∞) ^ e)⁻¹ := (inv_toD e D he).symm

/-- **The route's bound at `qf ≤ 2^60`, `qs ≤ 2^20`**, messages `≤ 2^26` bytes:
`2^-67 + 2^-107`. -/
theorem epsRom_2_20 {qf qs ℓ : ℕ} (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    epsRom qf qs ℓ ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ := by
  refine (epsRom_le_num hf hs hℓ (by norm_num)).trans ?_
  rw [← frac_pow_two 67 1050 (by norm_num), ← frac_pow_two 107 1050 (by norm_num), frac_add]
  exact frac_mono (num_2_20.trans (by norm_num))

/-- **The route's bound at `qf ≤ 2^64`, `qs ≤ 2^40`**: `2^-63 + 2^-87`. -/
theorem epsRom_2_40 {qf qs ℓ : ℕ} (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    epsRom qf qs ℓ ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ := by
  refine (epsRom_le_num hf hs hℓ (by norm_num)).trans ?_
  rw [← frac_pow_two 63 1050 (by norm_num), ← frac_pow_two 87 1050 (by norm_num), frac_add]
  exact frac_mono (num_2_40.trans (by norm_num))

/-- **The route's bound at `qf ≤ 2^64`, `qs ≤ 2^64`**: `2^-63 + 2^-64 + 2^-66`. -/
theorem epsRom_2_64 {qf qs ℓ : ℕ} (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    epsRom qf qs ℓ ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ := by
  refine (epsRom_le_num hf hs hℓ (by norm_num)).trans ?_
  rw [← frac_pow_two 63 1050 (by norm_num), ← frac_pow_two 64 1050 (by norm_num),
    ← frac_pow_two 66 1050 (by norm_num), frac_add, frac_add]
  exact frac_mono (num_2_64.trans (by norm_num))

end Point

/-! ## Comparison with tight8 -/

section Compare

set_option exponentiation.threshold 1200

theorem frac_lt {m n D : ℕ} (h : m < n) : (m : ℝ≥0∞) / 2 ^ D < (n : ℝ≥0∞) / 2 ^ D :=
  ENNReal.div_lt_div_right (two_pow_ne_zero' D) (two_pow_ne_top' D) (by exact_mod_cast h)

/-- At P20 the route's bound is below tight8's `2^-77 + 2^-132 + 2^-63`. -/
theorem rom_lt_tight8_2_20 :
    ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ <
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ := by
  rw [← frac_pow_two 67 1050 (by norm_num), ← frac_pow_two 107 1050 (by norm_num),
    ← frac_pow_two 77 1050 (by norm_num), ← frac_pow_two 132 1050 (by norm_num),
    ← frac_pow_two 63 1050 (by norm_num), frac_add, frac_add, frac_add]
  exact frac_lt (by norm_num)

/-- At P40 the route's bound is below tight8's `2^-63 + 2^-94 + 2^-59`. -/
theorem rom_lt_tight8_2_40 :
    ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ <
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ := by
  rw [← frac_pow_two 63 1050 (by norm_num), ← frac_pow_two 87 1050 (by norm_num),
    ← frac_pow_two 94 1050 (by norm_num), ← frac_pow_two 59 1050 (by norm_num),
    frac_add, frac_add, frac_add]
  exact frac_lt (by norm_num)

/-- At P64 the route's bound is below tight8's `2^-45 + 2^-46 + 2^-39`. -/
theorem rom_lt_tight8_2_64 :
    ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ <
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ := by
  rw [← frac_pow_two 63 1050 (by norm_num), ← frac_pow_two 64 1050 (by norm_num),
    ← frac_pow_two 66 1050 (by norm_num), ← frac_pow_two 45 1050 (by norm_num),
    ← frac_pow_two 46 1050 (by norm_num), ← frac_pow_two 39 1050 (by norm_num),
    frac_add, frac_add, frac_add, frac_add]
  exact frac_lt (by norm_num)

end Compare

/-! ## Point bounds on `sufI` / `eufI` / `sufP` / `eufP`, under the hop -/

section Headline

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
include hqf hqs hlong hout

/-- SUF under the hop, `qf ≤ 2^60`, `qs ≤ 2^20`, messages `≤ 2^26` bytes: `2^-67 + 2^-107`. -/
theorem suf_rom_2_20 (hop : MDHopSuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  (suf_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_20 hf hs hℓ)

/-- SUF under the hop, `qf ≤ 2^64`, `qs ≤ 2^40`: `2^-63 + 2^-87`. -/
theorem suf_rom_2_40 (hop : MDHopSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  (suf_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_40 hf hs hℓ)

/-- SUF under the hop, `qf ≤ 2^64`, `qs ≤ 2^64`: `2^-63 + 2^-64 + 2^-66`. -/
theorem suf_rom_2_64 (hop : MDHopSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  (suf_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_64 hf hs hℓ)

/-- EUF under the hop, `qf ≤ 2^60`, `qs ≤ 2^20`. -/
theorem euf_rom_2_20 (hop : MDHopEuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  (euf_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_20 hf hs hℓ)

/-- EUF under the hop, `qf ≤ 2^64`, `qs ≤ 2^40`. -/
theorem euf_rom_2_40 (hop : MDHopEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  (euf_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_40 hf hs hℓ)

/-- EUF under the hop, `qf ≤ 2^64`, `qs ≤ 2^64`. -/
theorem euf_rom_2_64 (hop : MDHopEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  (euf_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_64 hf hs hℓ)

end Headline

section HeadlinePure

variable (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
include hqf hqs hlong hout

/-- SUF of the external pure interface under the hop, `qf ≤ 2^60`, `qs ≤ 2^20`, message parts
`≤ 2^26 - 257` bytes: `2^-67 + 2^-107` (the game of `suf_ideal_pure_closed_tight8_2_20`). -/
theorem sufP_rom_2_20 (hop : MDHopSuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  (sufP_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_20 hf hs hℓ)

/-- SUF of the external pure interface under the hop, `qf ≤ 2^64`, `qs ≤ 2^40`. -/
theorem sufP_rom_2_40 (hop : MDHopSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  (sufP_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_40 hf hs hℓ)

/-- SUF of the external pure interface under the hop, `qf ≤ 2^64`, `qs ≤ 2^64`. -/
theorem sufP_rom_2_64 (hop : MDHopSuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  (sufP_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_64 hf hs hℓ)

/-- EUF of the external pure interface under the hop, `qf ≤ 2^60`, `qs ≤ 2^20`. -/
theorem eufP_rom_2_20 (hop : MDHopEuf) (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 67)⁻¹ + ((2 : ℝ≥0∞) ^ 107)⁻¹ :=
  (eufP_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_20 hf hs hℓ)

/-- EUF of the external pure interface under the hop, `qf ≤ 2^64`, `qs ≤ 2^40`. -/
theorem eufP_rom_2_40 (hop : MDHopEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 87)⁻¹ :=
  (eufP_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_40 hf hs hℓ)

/-- EUF of the external pure interface under the hop, `qf ≤ 2^64`, `qs ≤ 2^64`. -/
theorem eufP_rom_2_64 (hop : MDHopEuf) (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64)
    (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 64)⁻¹ + ((2 : ℝ≥0∞) ^ 66)⁻¹ :=
  (eufP_rom_of_hop hop S oR hqf hqs hlong hout).trans (epsRom_2_64 hf hs hℓ)

end HeadlinePure

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.wTCB_le_simple
#print axioms Ideal.Direct.Rom.epsRom_le_num
#print axioms Ideal.Direct.Rom.epsRom_2_20
#print axioms Ideal.Direct.Rom.epsRom_2_40
#print axioms Ideal.Direct.Rom.epsRom_2_64
#print axioms Ideal.Direct.Rom.rom_lt_tight8_2_20
#print axioms Ideal.Direct.Rom.rom_lt_tight8_2_40
#print axioms Ideal.Direct.Rom.rom_lt_tight8_2_64
#print axioms Ideal.Direct.Rom.suf_rom_2_64
#print axioms Ideal.Direct.Rom.sufP_rom_2_64
#print axioms Ideal.Direct.Rom.eufP_rom_2_64
