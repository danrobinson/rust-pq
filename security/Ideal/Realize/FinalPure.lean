import Ideal.Realize.PureForger

/-!
# The ideal-compression bound for the EXTERNAL PURE interface of SLH-DSA-SHA2-128s

`Ideal.suf_ideal_closed` / `euf_ideal_closed` (`Ideal/Realize/Final.lean`) bound forgers against
the internal interface (FIPS 205 Alg. 18–20).  Here the same bounds are stated for forgers
against the external pure interface with context strings (Alg. 21/22/24, the byte-level scheme
`Reduction.pureBytesAlg`): an ideal-model forger `S : ForgerP` receives the public-key bytes, may
query the compression table, and has a signing oracle on `(message, context)` pairs (answered by
`none` for a context longer than 255 bytes); it wins if it outputs a `(message, context)` pair and
signature bytes that `byteVerifyPure` accepts and that are fresh (SUF: the pair `((M, ctx), sig)`
was never returned; EUF: the pair `(M, ctx)` was never submitted).

Hypotheses (as for the internal theorems): at most `qf` compression queries, at most `qs`
signing queries, every signing query has a message part of at most `ℓ` bytes (the context is
not restricted; one longer than 255 bytes is answered by `none`), and the output message part
has at most `ℓ` bytes.

Proof: `S.toI` (`Ideal/Realize/PureForger.lean`) is an internal forger with the same `qf`, `qs`
whose signed and output messages have at most `ℓ + 257` bytes, and `sufP S ≤ sufI S.toI`,
`eufP S ≤ eufI S.toI`; the bounds are the internal ones at message length `ℓ + 257`.

* `suf_ideal_pure_closed`, `euf_ideal_pure_closed`: general bound, under
  `QcAll qf qs (ℓ + 257) ≤ 2^126`;
* `…_2_20`, `…_2_40`, `…_2_64`: the numeric points of the internal theorems, with the message
  bound `ℓ + 257 ≤ 2^26`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

/-- **SUF-CMA of the external pure interface of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only.**  The bound is that of `suf_ideal_closed` at message length `ℓ + 257`. -/
theorem suf_ideal_pure_closed (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hQ : QcAll qf qs (ℓ + 257) ≤ 2 ^ 126) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
        ((66 * QcAll qf qs (ℓ + 257) + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hQ)

/-- **EUF-CMA analogue** (a forgery is on a `(message, context)` pair never submitted). -/
theorem euf_ideal_pure_closed (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hQ : QcAll qf qs (ℓ + 257) ≤ 2 ^ 126) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
        ((66 * QcAll qf qs (ℓ + 257) + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hQ)

/-- SUF (external pure) at `qs ≤ 2^20` signatures, `qf + 2^46 ≤ 2^60` compression queries, message parts `≤ 2^26 - 257` bytes: `2^-70 + 2^-128 + 2^-61`. -/
theorem suf_ideal_pure_closed_2_20 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_2_20 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- EUF (external pure) at `qs ≤ 2^20` signatures, `qf + 2^46 ≤ 2^60` compression queries, message parts `≤ 2^26 - 257` bytes: `2^-70 + 2^-128 + 2^-61`. -/
theorem euf_ideal_pure_closed_2_20 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_2_20 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- SUF (external pure) at `qs ≤ 2^40`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes: `2^-50 + 2^-88 + 2^-41`. -/
theorem suf_ideal_pure_closed_2_40 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_2_40 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- EUF (external pure) at `qs ≤ 2^40`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes: `2^-50 + 2^-88 + 2^-41`. -/
theorem euf_ideal_pure_closed_2_40 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_2_40 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- SUF (external pure) at `qs ≤ 2^64`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes: `2^-44 + 2^-43 + 2^-31`. -/
theorem suf_ideal_pure_closed_2_64 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  (sufP_le_sufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (suf_ideal_closed_2_64 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

/-- EUF (external pure) at `qs ≤ 2^64`, `qf ≤ 2^64`, message parts `≤ 2^26 - 257` bytes: `2^-44 + 2^-43 + 2^-31`. -/
theorem euf_ideal_pure_closed_2_64 (S : ForgerP) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ + 257 ≤ 2 ^ 26) :
    eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  (eufP_le_eufI S (optRandU oR) ($ᵗ (Bytes 16))).trans
    (euf_ideal_closed_2_64 S.toI oR (fun pk => toI_port S pk (hqf pk)) (fun pk => toI_sign S pk (hqs pk))
    (fun pk => toI_long S pk (hlong pk)) (fun pk => toI_out S pk (hout pk)) hf hs hℓ)

end Ideal

#print axioms Ideal.suf_ideal_pure_closed
#print axioms Ideal.suf_ideal_pure_closed_2_20
#print axioms Ideal.suf_ideal_pure_closed_2_40
#print axioms Ideal.suf_ideal_pure_closed_2_64
#print axioms Ideal.euf_ideal_pure_closed
#print axioms Ideal.euf_ideal_pure_closed_2_20
#print axioms Ideal.euf_ideal_pure_closed_2_40
#print axioms Ideal.euf_ideal_pure_closed_2_64
