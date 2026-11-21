import Ideal.ComposeFinal
import Ideal.Rust

/-!
# The ideal-compression bound attached to the Rust code, with the repaired ITSR leg

`Ideal.rust_ideal_security_final` is `Ideal.rust_ideal_security` with its third conjunct replaced
by the closed statements of `Ideal/ComposeFinal.lean`:

1. (**real code, real SHA-256**) the Rust functions compute `byteKeygen`, `byteSign`,
   `byteVerify` at `Link.prims`;
2. (**link**) the byte-level scheme at the generic primitives over the real compression table is
   that scheme;
3. (**IDEAL-MODEL scheme only**) for a uniformly random compression table that the forger may
   query: every forger `S` for which the twelve realisers exist with the stated query parameters
   has table-averaged SUF-CMA advantage at most
   * `epsItsrF … + (66 Qc + 40)/2^128 + polyP …/2^256` in general (`suf_final`),
   * `2^-70 + 2^-128 + 2^-61` at realiser caps `(Qc, qs) = (2^60, 2^20)`,
   * `2^-44 + 2^-43 + 2^-31` at `(Qc, qs) = (2^90, 2^64)` if moreover the ITSR realiser makes at
     most `2^64` raw compression queries with block `cB`.

**The twelve realisers are hypotheses of conjunct 3; none is proved.**  Conjunct 3 says nothing
about the real compression function.
-/

namespace Ideal

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims)
open Reduction (codec128s byteKeygen byteSign byteVerify bytesAlg)
open E2E

theorem rust_ideal_security_final
    (oR : ∀ c : CompressFn, PublicKeyCore (primsG c).core → ProbComp (primsG c).Y) :
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
    (Reduction.bytesAlg Link.vp (primsG (liftC realCF)) (codecG realCF) (oR (liftC realCF))
        ($ᵗ (Bytes 16)) =
      Reduction.bytesAlg Link.vp Link.prims Reduction.codec128s
        (oR VCVio.Algorithms.Sha2.compress) ($ᵗ (Bytes 16))) ∧
    (∀ S : ForgerI,
      (∀ (qP cP q qc Lc qs ℓ : ℕ),
        RealizesItsrF (fun g => Reduction.Lazy.bItsrL
          (S.typedS (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) g)) qP cP q qc Lc qs ℓ →
        ∀ (R : SufRealizers S (fun g => oR (liftC g)) ($ᵗ (Bytes 16))) (Qc N qs' ℓ' : ℕ),
          R.Le Qc N qs' ℓ' → Qc ≤ 2 ^ 126 →
          sufI S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) ≤
            epsItsrF qP cP q qc Lc qs ℓ + ((66 * Qc + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
              (polyP Qc N qs' ℓ' : ℝ≥0∞) / 2 ^ 256) ∧
      (RealizesItsrF (fun g => Reduction.Lazy.bItsrL
          (S.typedS (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) g))
          (2 ^ 60) (2 ^ 60) (2 ^ 60) (2 ^ 42) (2 ^ 21) (2 ^ 20) (2 ^ 26) →
        ∀ R : SufRealizers S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)),
          R.Le (2 ^ 60) (2 ^ 81) (2 ^ 20) (2 ^ 20) →
          sufI S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹) ∧
      (RealizesItsrF (fun g => Reduction.Lazy.bItsrL
          (S.typedS (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) g))
          (2 ^ 64) (2 ^ 65) (2 ^ 90) (2 ^ 85) (2 ^ 21) (2 ^ 64) (2 ^ 26) →
        ∀ R : SufRealizers S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)),
          R.Le (2 ^ 90) (2 ^ 82) (2 ^ 64) (2 ^ 20) →
          sufI S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) ≤
            ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹)) :=
  ⟨(E2E.rust_security (oR VCVio.Algorithms.Sha2.compress) ($ᵗ (Bytes 16))).1,
    bytesAlg_realCF oR ($ᵗ (Bytes 16)),
    fun _ => ⟨fun _ _ _ _ _ _ _ RI R _ _ _ _ h hQ => suf_final RI R h hQ,
      fun RI R h => suf_final_2_60_2_20 RI R h,
      fun RI R h => suf_final_2_90_2_64 RI R h⟩⟩

end Ideal

#print axioms Ideal.rust_ideal_security_final
