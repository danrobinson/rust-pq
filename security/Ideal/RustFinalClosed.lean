import Ideal.RustFinal
import Ideal.Realize.Final

/-!
# The ideal-compression bound attached to the Rust code, with NO realiser hypotheses

`Ideal.rust_ideal_security_closed` is `Ideal.rust_ideal_security_final` with conjunct 3 stated
for every forger in terms of the FORGER's own budgets only (`Ideal.suf_ideal_closed`,
`Ideal.suf_ideal_closed_2_20/_2_40/_2_64`, and the EUF analogues), at a table-independent
`opt_rand` sampler `oR` (the FIPS choices `fun s _ => pure s` and `fun _ _ => $ᵗ (Bytes 16)` are
of this form):

1. (**real code, real SHA-256**) the Rust functions compute `byteKeygen`, `byteSign`,
   `byteVerify` at `Link.prims`;
2. (**link**) the byte-level scheme at the generic primitives over the real compression table is
   that scheme;
3. (**IDEAL-MODEL scheme only**) for a uniformly random compression table: every forger making at
   most `qf` compression queries and `qs` signing queries, on messages of at most `ℓ` bytes,
   has table-averaged SUF-CMA (and EUF-CMA) advantage at most the stated numbers.

Conjunct 3 says nothing about the real compression function.
-/

namespace Ideal

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims)
open Reduction (codec128s byteKeygen byteSign byteVerify bytesAlg)
open E2E
open Ideal.Realize

theorem rust_ideal_security_closed (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) :
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
            ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ∧
        eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
          epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
            ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
            (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256) ∧
      (qf + 2 ^ 46 ≤ 2 ^ 60 → qs ≤ 2 ^ 20 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 40 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹) ∧
      (qf ≤ 2 ^ 64 → qs ≤ 2 ^ 64 → ℓ ≤ 2 ^ 26 →
        sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ ∧
          eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹)) :=
  ⟨(rust_ideal_security_final fun _ pk => oR pk.pkSeed pk.pkRoot).1,
    bytesAlg_realCF (fun _ pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16)),
    fun S _ _ _ hqf hqs hlong hout =>
      ⟨fun hQ => ⟨suf_ideal_closed S oR hqf hqs hlong hout hQ,
          euf_ideal_closed S oR hqf hqs hlong hout hQ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_2_20 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_2_20 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_2_40 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_2_40 S oR hqf hqs hlong hout hf hs hℓ⟩,
        fun hf hs hℓ => ⟨suf_ideal_closed_2_64 S oR hqf hqs hlong hout hf hs hℓ,
          euf_ideal_closed_2_64 S oR hqf hqs hlong hout hf hs hℓ⟩⟩⟩

end Ideal

#print axioms Ideal.rust_ideal_security_closed
