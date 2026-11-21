import Ideal.Realize.FinalCore
import Ideal.Realize.WotsRealizers

/-!
# The composed ideal-compression bound for SLH-DSA-SHA2-128s: forger caps only

All twelve realisers are discharged: `sufRealizersU` / `eufRealizersU` are the bundles
`SufRealizers S (optRandU oR) ($ᵗ (Bytes 16))` / `EufRealizers …` built from the agents'
realisers (PRF, PRF_msg, FORS DSPR/TCR, class TCR ×4, WOTS UD/PRE/TCR); the ITSR realiser is
`Itsr.realizesItsrS/E`.  `sufRealizersU_le`: `R.Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)`.

Headlines (hypotheses: the forger makes at most `qf` compression queries, at most `qs` signing
queries, never signs a message of more than `ℓ` bytes, outputs a message of at most `ℓ` bytes):
* `suf_ideal_closed`, `euf_ideal_closed`: the general bound, under `QcAll qf qs ℓ ≤ 2^126`;
* `suf_ideal_closed_2_20`, `_2_40`, `_2_64` (and `euf_…`): closed numeric points.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

theorem QcW_le_QcAll (qf qs ℓ : ℕ) : Wots.QcW qf qs ℓ ≤ QcAll qf qs ℓ := by
  unfold Wots.QcW QcAll
  have : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  nlinarith [Nat.zero_le qs, Nat.zero_le ((ℓ + 56) / 64)]

theorem NW_le_NAll (qs : ℕ) : Wots.NW ≤ NAll qs :=
  (by unfold Wots.NW; norm_num : Wots.NW ≤ 2 ^ 81).trans (two81_le_NAll qs)

theorem pU_le_all (qf qs ℓ : ℕ) : (Wots.pU qf qs ℓ).Le (QcAll qf qs ℓ) (NAll qs) :=
  P5Le_mono (Wots.pU_le qf qs ℓ) (QcW_le_QcAll qf qs ℓ) (NW_le_NAll qs)
theorem pP_le_all (qf qs ℓ : ℕ) : (Wots.pP qf qs ℓ).Le (QcAll qf qs ℓ) (NAll qs) :=
  P5Le_mono (Wots.pP_le qf qs ℓ) (QcW_le_QcAll qf qs ℓ) (NW_le_NAll qs)
theorem pW_le_all (qf qs ℓ : ℕ) : (Wots.pW qf qs ℓ).Le (QcAll qf qs ℓ) (NAll qs) :=
  P5Le_mono (Wots.pW_le qf qs ℓ) (QcW_le_QcAll qf qs ℓ) (NW_le_NAll qs)

section Bundles

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- **The eleven SUF realisers.** -/
noncomputable def sufRealizersU : SufRealizers S (optRandU oR) ($ᵗ (Bytes 16)) :=
  sufRealizersW S oR hqf hqs hlong hout
    (Wots.realizesUd (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPre (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcr (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)

/-- **The eleven EUF realisers.** -/
noncomputable def eufRealizersU : EufRealizers S (optRandU oR) ($ᵗ (Bytes 16)) :=
  eufRealizersW S oR hqf hqs hlong hout
    (Wots.realizesUdE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPreE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcrE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)

theorem sufRealizersU_le :
    (sufRealizersU S oR hqf hqs hlong hout).Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) :=
  sufRealizersW_le S oR hqf hqs hlong hout _ _ _ (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ)

theorem eufRealizersU_le :
    (eufRealizersU S oR hqf hqs hlong hout).Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) :=
  eufRealizersW_le S oR hqf hqs hlong hout _ _ _ (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ)

end Bundles

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only.** -/
theorem suf_ideal_closed (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 :=
  suf_ideal_closed_W S oR hqf hqs hlong hout
    (Wots.realizesUd (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPre (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcr (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hQ

/-- **EUF-CMA analogue.** -/
theorem euf_ideal_closed (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 :=
  euf_ideal_closed_W S oR hqf hqs hlong hout
    (Wots.realizesUdE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPreE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcrE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hQ

/-- SUF at `qs ≤ 2^20` signatures, `qf + 2^46 ≤ 2^60` compression queries, messages `≤ 2^26` bytes: `2^-70 + 2^-128 + 2^-61`. -/
theorem suf_ideal_closed_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  suf_closed_2_60_W S oR hqf hqs hlong hout
    (Wots.realizesUd (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPre (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcr (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hf hs hℓ

/-- EUF at `qs ≤ 2^20` signatures, `qf + 2^46 ≤ 2^60` compression queries, messages `≤ 2^26` bytes: `2^-70 + 2^-128 + 2^-61`. -/
theorem euf_ideal_closed_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  euf_closed_2_60_W S oR hqf hqs hlong hout
    (Wots.realizesUdE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPreE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcrE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hf hs hℓ

/-- SUF at `qs ≤ 2^40`, `qf ≤ 2^64`, messages `≤ 2^26` bytes: `2^-50 + 2^-88 + 2^-41`. -/
theorem suf_ideal_closed_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  suf_closed_2_80_W S oR hqf hqs hlong hout
    (Wots.realizesUd (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPre (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcr (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hf hs hℓ

/-- EUF at `qs ≤ 2^40`, `qf ≤ 2^64`, messages `≤ 2^26` bytes: `2^-50 + 2^-88 + 2^-41`. -/
theorem euf_ideal_closed_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  euf_closed_2_80_W S oR hqf hqs hlong hout
    (Wots.realizesUdE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPreE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcrE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hf hs hℓ

/-- SUF at `qs ≤ 2^64`, `qf ≤ 2^64`, messages `≤ 2^26` bytes: `2^-44 + 2^-43 + 2^-31`. -/
theorem suf_ideal_closed_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  suf_closed_2_90_W S oR hqf hqs hlong hout
    (Wots.realizesUd (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPre (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcr (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hf hs hℓ

/-- EUF at `qs ≤ 2^64`, `qf ≤ 2^64`, messages `≤ 2^26` bytes: `2^-44 + 2^-43 + 2^-31`. -/
theorem euf_ideal_closed_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  euf_closed_2_90_W S oR hqf hqs hlong hout
    (Wots.realizesUdE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesPreE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (Wots.realizesWotsTcrE (S := S) (oR := oR) (pkSeedDist := $ᵗ (Bytes 16)) hqf hqs hlong hout)
    (pU_le_all qf qs ℓ) (pP_le_all qf qs ℓ) (pW_le_all qf qs ℓ) hf hs hℓ

end Ideal

#print axioms Ideal.sufRealizersU
#print axioms Ideal.eufRealizersU
#print axioms Ideal.sufRealizersU_le
#print axioms Ideal.eufRealizersU_le
#print axioms Ideal.suf_ideal_closed
#print axioms Ideal.euf_ideal_closed
#print axioms Ideal.suf_ideal_closed_2_20
#print axioms Ideal.euf_ideal_closed_2_20
#print axioms Ideal.suf_ideal_closed_2_40
#print axioms Ideal.euf_ideal_closed_2_40
#print axioms Ideal.suf_ideal_closed_2_64
#print axioms Ideal.euf_ideal_closed_2_64
