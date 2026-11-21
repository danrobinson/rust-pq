import Ideal.RustFinalClosed
import Ideal.Realize.FinalPure
import E2E.Bytes

/-!
# The ideal-compression bound for the external pure interface, attached to the Rust code

`Ideal.rust_ideal_security_closed_pure` is `Ideal.rust_ideal_security_closed` for the Rust
crate's public API — `slh_sign` / `slh_verify`, FIPS 205 Algorithms 22/24 with context strings —
and the byte-level external pure scheme `Reduction.pureBytesAlg`.  At a table-independent
`opt_rand` sampler `oR`:

1. (**real code, real SHA-256**) `E2E.PureBytesEndToEnd`: `pureBytesAlg` at `Link.prims` is
   "sample, then apply `byteKeygen` / `byteSignPure` / `byteVerifyPure`", the Rust
   `slh_keygen_internal`, `slh_sign`, `slh_verify` never panic and are pointwise equal to these
   functions (under the `Room` bound), and the scheme is complete for contexts of at most 255
   bytes;
2. (**link**) the byte-level external scheme at the generic primitives over the real compression
   table is that scheme;
3. (**IDEAL-MODEL scheme only**) for a uniformly random compression table: every external forger
   (`ForgerP`) making at most `qf` compression queries and `qs` signing queries, on messages of
   at most `ℓ` bytes (contexts not counted), and outputting a message of at most `ℓ` bytes, has
   table-averaged SUF-CMA (and EUF-CMA) advantage at most the bounds of
   `rust_ideal_security_closed` at message length `ℓ + 257`.

Conjunct 3 says nothing about the real compression function.
-/

namespace Ideal

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims)
open Reduction (codec128s byteKeygen byteSignPure byteVerifyPure pureBytesAlg)
open E2E
open Ideal.Realize

/-- **At the table of the real compression function the byte-level external scheme is the real
one.** -/
theorem pureBytesAlg_realCF
    (optRand : ∀ c : CompressFn, PublicKeyCore (primsG c).core → ProbComp (primsG c).Y)
    (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.pureBytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF)
        (optRand (liftC realCF)) pkSeedDist =
      Reduction.pureBytesAlg Link.vp Link.prims Reduction.codec128s
        (optRand VCVio.Algorithms.Sha2.compress) pkSeedDist :=
  congrArg (fun c => Reduction.pureBytesAlg Link.vp (primsG c) (codecC c) (optRand c) pkSeedDist)
    liftC_realCF

theorem rust_ideal_security_closed_pure (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    E2E.PureBytesEndToEnd (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)) ∧
    (Reduction.pureBytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF)
        ($ᵗ (Bytes 16)) =
      Reduction.pureBytesAlg Link.vp Link.prims Reduction.codec128s
        (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))) ∧
    (∀ (S : ForgerP) (qf qs ℓ : ℕ),
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQP i = true) qf) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQP i = true) qs) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQP ℓ i = true) 0) →
      (∀ pk, ∀ z ∈ support (S.main pk), z.1.1.length ≤ ℓ) →
      (QcAll qf qs (ℓ + 257) ≤ 2 ^ 126 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((66 * QcAll qf qs (ℓ + 257) + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 ∧
        eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((66 * QcAll qf qs (ℓ + 257) + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf + 2 ^ 46 ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹)) :=
  ⟨E2E.pure_bytes_end_to_end _ _,
    pureBytesAlg_realCF (fun _ pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)),
    fun S _ _ _ hqf hqs hlong hout =>
      ⟨fun hQ => ⟨suf_ideal_pure_closed S oR hqf hqs hlong hout hQ,
          euf_ideal_pure_closed S oR hqf hqs hlong hout hQ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_2_20 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_2_20 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_2_40 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_2_40 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_2_64 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_2_64 S oR hqf hqs hlong hout hf hs hℓ⟩⟩⟩

end Ideal

#print axioms Ideal.pureBytesAlg_realCF
#print axioms Ideal.rust_ideal_security_closed_pure
