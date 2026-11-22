import Ideal.RustFinalClosedPureApi
import Ideal.Realize.FinalPureTight8

/-!
# The answer-storing class-TCR, per-arity FORS/WOTS, per-signature message-block ideal-compression bounds attached to the Rust code and to the crate's `api`

The three Rust-level statements `rust_ideal_security_closed`, `rust_ideal_security_closed_pure`
and `api_ideal_security_closed_pure` with conjunct 3 replaced by the bounds of
`Ideal/Realize/FinalTight8.lean` and `Ideal/Realize/FinalPureTight8.lean` (shape marking in the
`PRF` and `PRF_msg` games, answer-storing class-TCR realisers, per-arity counts in the FORS-leaf
and WOTS-chain realisers, message blocks counted per signing query, the SM-UD and single-block SM-TCR realisers' message blocks uncharged):

* `rust_ideal_security_closed_tight8` (internal interface, `slh_*_internal`);
* `rust_ideal_security_closed_pure_tight8` (external pure interface, `slh_sign` / `slh_verify`);
* `api_ideal_security_closed_pure_tight8` (the interface module `api`).

Conjuncts 1 and 2 are those of the untightened statements, unchanged.  Conjunct 3 is about the
IDEAL-MODEL scheme only (uniformly random compression table) and says nothing about the real
compression function.  For every forger it gives the general bound (coefficient
`QlinT8 qf qs ℓ`) and the three points `2^-77 + 2^-132 + 2^-63` (`qf ≤ 2^60`, `qs ≤ 2^20`),
`2^-63 + 2^-94 + 2^-59` (`qf ≤ 2^64`, `qs ≤ 2^40`), `2^-45 + 2^-46 + 2^-39` (`qf ≤ 2^64`,
`qs ≤ 2^64`), messages of at most `2^26` bytes (external interface: message parts of at most
`2^26 - 257` bytes).
-/

namespace Ideal

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims)
open Reduction (codec128s byteKeygen byteSign byteVerify bytesAlg byteSignPure byteVerifyPure
  pureBytesAlg)
open E2E
open Ideal.Realize

/-- `rust_ideal_security_closed` with conjunct 3 the answer-storing class-TCR, per-arity FORS/WOTS, per-signature message-block bounds of `FinalTight8.lean`. -/
theorem rust_ideal_security_closed_tight8 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 152 →
        ∃ sig, slhdsa.slh.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign vp prims codec128s (wire m.val) (wire sk.val) (node addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
        slhdsa.slh.slh_verify_internal m sig pk =
          ok (byteVerify vp prims codec128s (wire m.val) (wire sig.val) (wire pk.val)))) ∧
    (Reduction.bytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF)
        ($ᵗ (Bytes 16)) =
      Reduction.bytesAlg Link.vp Link.prims Reduction.codec128s
        (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))) ∧
    (∀ (S : ForgerI) (qf qs ℓ : ℕ),
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List SLHDSA.Byte) i = true) qf) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List SLHDSA.Byte) i = true) qs) →
      (∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List SLHDSA.Byte) ℓ i = true) 0) →
      (∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ) →
      (QcAll qf qs ℓ ≤ 2 ^ 126 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
            ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ∧
        eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
            ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹)) :=
  ⟨(rust_ideal_security_closed oR).1, (rust_ideal_security_closed oR).2.1,
    fun S _ _ _ hqf hqs hlong hout =>
      ⟨fun hQ => ⟨suf_ideal_closed_tight8 S oR hqf hqs hlong hout hQ,
          euf_ideal_closed_tight8 S oR hqf hqs hlong hout hQ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ⟩⟩⟩

/-- `rust_ideal_security_closed_pure` with conjunct 3 the answer-storing class-TCR, per-arity FORS/WOTS, per-signature message-block bounds of `FinalTight8.lean`. -/
theorem rust_ideal_security_closed_pure_tight8 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
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
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 ∧
        eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹)) :=
  ⟨(rust_ideal_security_closed_pure oR).1, (rust_ideal_security_closed_pure oR).2.1,
    fun S _ _ _ hqf hqs hlong hout =>
      ⟨fun hQ => ⟨suf_ideal_pure_closed_tight8 S oR hqf hqs hlong hout hQ,
          euf_ideal_pure_closed_tight8 S oR hqf hqs hlong hout hQ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_tight8_2_20 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_tight8_2_40 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_pure_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_pure_closed_tight8_2_64 S oR hqf hqs hlong hout hf hs hℓ⟩⟩⟩

/-- `api_ideal_security_closed_pure` with conjunct 3 the answer-storing class-TCR, per-arity FORS/WOTS, per-signature message-block bounds of `FinalTight8.lean`. -/
theorem api_ideal_security_closed_pure_tight8 (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
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
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256 ∧
        eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc (ℓ + 257)) qs (ℓ + 257) +
            ((QlinT8 qf qs (ℓ + 257) : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP8 (QcAll qf qs (ℓ + 257)) (NAll qs) qs (ellB (ℓ + 257)) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ + 257 ≤ 2 ^ 26 →
        sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹ ∧
          eufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 39)⁻¹)) :=
  ⟨(api_ideal_security_closed_pure oR).1, (rust_ideal_security_closed_pure_tight8 oR).2⟩

end Ideal

#print axioms Ideal.rust_ideal_security_closed_tight8
#print axioms Ideal.rust_ideal_security_closed_pure_tight8
#print axioms Ideal.api_ideal_security_closed_pure_tight8
