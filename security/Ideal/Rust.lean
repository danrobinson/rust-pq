import Ideal.Compose128
import E2E.Headline

/-!
# The ideal-compression bound attached to the Rust code

`Ideal.rust_ideal_security` is a conjunction of three statements.

1. (**about the real code, real SHA-256**) the Rust functions `slh_keygen_internal`,
   `slh_sign_internal`, `slh_verify_internal` compute the byte-level functions `byteKeygen`,
   `byteSign`, `byteVerify` at the primitives `Link.prims` (first conjunct of
   `E2E.rust_security`);
2. (**link**) the byte-level scheme at the generic primitives instantiated with the *real*
   compression table `realCF` (`liftC realCF = VCVio.Algorithms.Sha2.compress`) is the scheme of
   `E2E.rust_security`;
3. (**about the IDEAL-MODEL scheme, not about real SHA-256**) when the compression table is
   uniformly random and the forger has oracle access to it, every forger `S` for which
   realisers with the stated query parameters exist has SUF-CMA advantage (averaged over the
   table) at most `εI + 2^-31`, `εI` any bound on the table-averaged ITSR advantage.

Conjunct 3 says nothing about the real compression function; conjuncts 1–2 only say that the
ideal-model scheme is the Rust code's scheme with the compression function replaced.  The
realisers and `εI` are hypotheses (see `IDEAL_STATUS.md`).
-/

namespace Ideal

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims)
open Reduction (codec128s byteKeygen byteSign byteVerify bytesAlg)
open E2E

theorem rust_ideal_security
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
    (∀ (S : ForgerI) (εI : ℝ≥0∞),
      itsrSufI S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) ≤ εI →
      ∀ R : SufRealizers S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)),
        R.Le (2 ^ 90) (2 ^ 81) (2 ^ 64) (2 ^ 20) →
        sufI S (fun g => oR (liftC g)) ($ᵗ (Bytes 16)) ≤ εI + ((2 : ℝ≥0∞) ^ 31)⁻¹) :=
  ⟨(E2E.rust_security (oR VCVio.Algorithms.Sha2.compress) ($ᵗ (Bytes 16))).1,
    bytesAlg_realCF oR ($ᵗ (Bytes 16)),
    fun _ _ hI R h => suf_ideal_bound_2_90 hI R h⟩

end Ideal

#print axioms Ideal.rust_ideal_security
