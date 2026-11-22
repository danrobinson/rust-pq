import Ideal.Realize.FinalTight3
import Ideal.Realize.FinalPure

/-!
# The answer-storing class-TCR ideal-compression bound for the EXTERNAL PURE interface

`suf_ideal_closed_tight3` / `euf_ideal_closed_tight3` and their numeric points
(`Ideal/Realize/FinalTight3.lean`) transferred to forgers against the external pure interface
with context strings (`ForgerP`, `Reduction.pureBytesAlg`), exactly as `FinalPureTight.lean`
transfers `suf_ideal_closed_tight`: `S.toI` is an internal forger with the same `qf`, `qs` and
messages of at most `ℓ + 257` bytes, and `sufP S ≤ sufI S.toI`, `eufP S ≤ eufI S.toI`.

* `suf_ideal_pure_closed_tight3`, `euf_ideal_pure_closed_tight3`: the general bound at message
  length `ℓ + 257`, under `QcAll qf qs (ℓ + 257) ≤ 2^126`;
* `…_tight3_2_20` (`qf ≤ 2^60`), `…_tight3_2_40`, `…_tight3_2_64`, with `ℓ + 257 ≤ 2^26`:
  `2^-77 + 2^-132 + 2^-63`, `2^-63 + 2^-94 + (2^-59 + 2^-62)`, `2^-45 + 2^-46 + (2^-37 + 2^-44)`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

/-- **SUF-CMA of the external pure interface, answer-storing class-TCR form**: `suf_ideal_closed_tight3` at message
length `ℓ + 257`. -/
theorem suf_ideal_pure_closed_tight3 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hQ : QcAll qf qs (ℓ + 257) ≤ 2 ^ 126) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
        ((QlinT3 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_tight3 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hQ)

/-- **EUF-CMA of the external pure interface, answer-storing class-TCR form**: `euf_ideal_closed_tight3` at message
length `ℓ + 257`. -/
theorem euf_ideal_pure_closed_tight3 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hQ : QcAll qf qs (ℓ + 257) ≤ 2 ^ 126) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
        ((QlinT3 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_tight3 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hQ)

/-- SUF (external pure), answer-storing class-TCR, at `qs ≤ 2^20`, `qf ≤ 2^60`, message parts `≤ 2^26 - 257` bytes:
`2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_pure_closed_tight3_2_20 (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_tight3_2_20 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- EUF (external pure), answer-storing class-TCR, at `qs ≤ 2^20`, `qf ≤ 2^60`, message parts `≤ 2^26 - 257` bytes:
`2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_pure_closed_tight3_2_20 (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_tight3_2_20 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- SUF (external pure), answer-storing class-TCR, at `qs ≤ 2^40`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes:
`2^-63 + 2^-94 + (2^-59 + 2^-62)`. -/
theorem suf_ideal_pure_closed_tight3_2_40 (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + (((2 : ℝ≥0∞) ^ 59)⁻¹ + ((2 : ℝ≥0∞) ^ 62)⁻¹) :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_tight3_2_40 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- EUF (external pure), answer-storing class-TCR, at `qs ≤ 2^40`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes:
`2^-63 + 2^-94 + (2^-59 + 2^-62)`. -/
theorem euf_ideal_pure_closed_tight3_2_40 (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + (((2 : ℝ≥0∞) ^ 59)⁻¹ + ((2 : ℝ≥0∞) ^ 62)⁻¹) :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_tight3_2_40 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- SUF (external pure), answer-storing class-TCR, at `qs ≤ 2^64`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes:
`2^-45 + 2^-46 + (2^-37 + 2^-44)`. -/
theorem suf_ideal_pure_closed_tight3_2_64 (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 37)⁻¹ + ((2 : ℝ≥0∞) ^ 44)⁻¹) :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_tight3_2_64 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- EUF (external pure), answer-storing class-TCR, at `qs ≤ 2^64`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes:
`2^-45 + 2^-46 + (2^-37 + 2^-44)`. -/
theorem euf_ideal_pure_closed_tight3_2_64 (S : ForgerP)
    (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 37)⁻¹ + ((2 : ℝ≥0∞) ^ 44)⁻¹) :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_tight3_2_64 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

end Ideal

#print axioms Ideal.suf_ideal_pure_closed_tight3
#print axioms Ideal.suf_ideal_pure_closed_tight3_2_20
#print axioms Ideal.suf_ideal_pure_closed_tight3_2_40
#print axioms Ideal.suf_ideal_pure_closed_tight3_2_64
#print axioms Ideal.euf_ideal_pure_closed_tight3
#print axioms Ideal.euf_ideal_pure_closed_tight3_2_20
#print axioms Ideal.euf_ideal_pure_closed_tight3_2_40
#print axioms Ideal.euf_ideal_pure_closed_tight3_2_64
