import Ideal.ComposeItsr

/-!
# Closed numeric forms of the composed ideal-model bound (uniform `PK.seed`, SUF-CMA)

All statements are conditional on realisers (`SufRealizers`, `RealizesItsr`) with the stated query
parameters; `Qc` bounds every realiser's own compression queries, `N = 2^81` its challenge /
collection / PRF-oracle queries, messages have at most `2^26` bytes (`2^20` blocks).

* `suf_closed_2_64_memo`   (q = qs = 2^64, memoising TCR adversaries, `Qc = 2^90`):
  `sufI ≤ 2^-50 + 2^-86 + 2^-31`;
* `suf_closed_2_64_store`  (q = qs = 2^64, answer-storing adversaries, `Qc = 2^68`,
  i.e. `q + 12·(qs + 3929) ≤ 2^68`): `sufI ≤ 2^-50 + 2^-86 + 2^-53`;
* `suf_closed_2_60_2_40`   (q = 2^60, qs = 2^40, `Qc = 2^61`): `sufI ≤ 2^-72 + 2^-133 + 2^-60`;
* `suf_closed_2_40_2_20`   (q = 2^40, qs = 2^20, `Qc = 2^41`): `sufI ≤ 2^-112 + 2^-173 + 2^-79`.

In each line the first two terms are the ITSR term (`reuseSum` and its `Q²/2^256` term), the last
the other eleven games.  For the last line the `2^-79` is the structural term
`polyP … / 2^256 ≈ 36·(22·2^81)²/2^256` (challenger-side chaining-value collisions over the whole
key structure), not a `q/2^128` term.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal KeyedHash

namespace Ideal

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}

theorem num_2_68 :
    (66 * 2 ^ 68 + 40) * 2 ^ 128 + polyP (2 ^ 68) (2 ^ 81) (2 ^ 64) (2 ^ 20) ≤ 2 ^ 203 := by
  unfold polyP; norm_num

theorem num_2_61 :
    (66 * 2 ^ 61 + 40) * 2 ^ 128 + polyP (2 ^ 61) (2 ^ 81) (2 ^ 40) (2 ^ 20) ≤ 2 ^ 196 := by
  unfold polyP; norm_num

theorem num_2_41 :
    (66 * 2 ^ 41 + 40) * 2 ^ 128 + polyP (2 ^ 41) (2 ^ 81) (2 ^ 20) (2 ^ 20) ≤ 2 ^ 177 := by
  unfold polyP; norm_num

/-- Answer-storing reduction adversaries (`Qc = 2^68`): the eleven non-ITSR games contribute at
most `2^-53`. -/
theorem suf_ideal_bound_2_68 {εI : ℝ≥0∞}
    (hI : itsrSufI S optRand ($ᵗ (Bytes 16)) ≤ εI)
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 68) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ 53)⁻¹ :=
  suf_ideal_bound_pow hI R h (by norm_num) 53 203 rfl num_2_68

/- SUPERSEDED (see `Ideal/ComposeFinal.lean`).  The four `suf_closed_*` theorems below are true
as stated but their hypotheses are not met by the Reduction's adversaries: `RealizesItsr … q …`
charges every compression query of `bItsrL` (≈ qs·2^21 hash evaluations of its own), and the caps
`R.Le (2^68)`, `(2^61)`, `(2^41)` are below the phase-two hashing of `bTcrArM`, `bOpenPreS`, ….
Use `suf_final`, `suf_final_2_60_2_20`, `suf_final_2_80_2_40`, `suf_final_2_90_2_64`. -/
theorem suf_closed_2_64_memo
    (RI : RealizesItsr (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 64) (2 ^ 64) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 90) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 86)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  suf_ideal_bound_2_90 (itsrSufI_le_2_64 S optRand _ RI) R h

theorem suf_closed_2_64_store
    (RI : RealizesItsr (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 64) (2 ^ 64) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 68) (2 ^ 81) (2 ^ 64) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 86)⁻¹ + ((2 : ℝ≥0∞) ^ 53)⁻¹ :=
  suf_ideal_bound_2_68 (itsrSufI_le_2_64 S optRand _ RI) R h

theorem suf_closed_2_60_2_40
    (RI : RealizesItsr (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 60) (2 ^ 40) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 61) (2 ^ 81) (2 ^ 40) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 72)⁻¹ + ((2 : ℝ≥0∞) ^ 133)⁻¹ + ((2 : ℝ≥0∞) ^ 60)⁻¹ :=
  suf_ideal_bound_pow
    ((itsrSufI_le S optRand _ RI).trans
      (add_le_add reuseSum_q60_qs40 (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 60 196 rfl num_2_61

theorem suf_closed_2_40_2_20
    (RI : RealizesItsr (fun g => Reduction.Lazy.bItsrL (S.typedS optRand ($ᵗ (Bytes 16)) g))
      (2 ^ 40) (2 ^ 20) (2 ^ 26))
    (R : SufRealizers S optRand ($ᵗ (Bytes 16)))
    (h : R.Le (2 ^ 41) (2 ^ 81) (2 ^ 20) (2 ^ 20)) :
    sufI S optRand ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 112)⁻¹ + ((2 : ℝ≥0∞) ^ 173)⁻¹ + ((2 : ℝ≥0∞) ^ 79)⁻¹ :=
  suf_ideal_bound_pow
    ((itsrSufI_le S optRand _ RI).trans
      (add_le_add reuseSum_q40_qs20 (natMul_inv_pow_le _ _ _ (by norm_num))))
    R h (by norm_num) 79 177 rfl num_2_41

end Ideal

#print axioms Ideal.suf_closed_2_64_memo
#print axioms Ideal.suf_closed_2_64_store
#print axioms Ideal.suf_closed_2_60_2_40
#print axioms Ideal.suf_closed_2_40_2_20
