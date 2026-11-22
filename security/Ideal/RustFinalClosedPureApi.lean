import Ideal.RustFinalClosedPure
import E2E.Api

/-!
# The ideal-compression bound for the external pure interface, attached to the crate's `api`

`Ideal.api_ideal_security_closed_pure` is `Ideal.rust_ideal_security_closed_pure` with conjunct 1
about the interface module: `E2E.ApiPureBytesEndToEnd` (`api.keygen` on the three blocks of its
seed string, `api.sign`, `api.sign_deterministic`, `api.verify` never panic and are pointwise
equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure`) in place of `E2E.PureBytesEndToEnd`.
Conjuncts 2 and 3 are those of `rust_ideal_security_closed_pure`, unchanged; conjunct 3 is about
the IDEAL-MODEL scheme only and says nothing about the real compression function.
-/

namespace Ideal

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims)
open Reduction (codec128s byteKeygen byteSignPure byteVerifyPure pureBytesAlg)
open E2E
open Ideal.Realize

theorem api_ideal_security_closed_pure (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    E2E.ApiPureBytesEndToEnd (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)) ∧
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
  ⟨E2E.api_pure_bytes_end_to_end _ _, (rust_ideal_security_closed_pure oR).2⟩

end Ideal

#print axioms Ideal.api_ideal_security_closed_pure
