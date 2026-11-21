import E2E.Headline
import Reduction.Gen.Resolved

/-!
# End-to-end statements for forgers over a general sampling spec

`E2E.rust_securityG`, `E2E.rust_pure_securityG` (and the `_linear` forms): the statements of
`E2E.rust_security` / `E2E.rust_pure_security` with the forger over `ds + unifSpec` for an
arbitrary sampling spec `ds` (with an `AnswerMeasure` and finite answer types).  Part (a) — the
Rust functions compute `byteKeygen`, `byteSign`, `byteVerify` (resp. the pure variants) — is
literally part (a) of the existing theorems: the Rust attachment does not involve the forger.
Parts (b), (c): SUF/EUF-CMA advantage (VCVio's experiment for the scheme run over
`ds + unifSpec`) `≤` the twelve wrapper-game advantages of the reduction adversaries around the
typed forger family (`Reduction.Gen.betaSufG`, `betaEufG`).
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sp sigBytes pkBytes skBytes)
open Reduction (codec128s bytesAlg pureBytesAlg byteKeygen byteSign byteVerify byteSignPure
  byteVerifyPure)
open Reduction.Gen

variable {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
  [∀ d, Fintype (ds.Range d)]

/-- **Internal interface, forgers over `ds + unifSpec`.** -/
theorem rust_securityG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
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
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (liftAlg ds (bytesAlg vp prims codec128s optRand pkSeedDist)),
      sufAdvG ds S ≤ betaSufG ds optRand pkSeedDist (bytesToTypedSG ds S).main) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (liftAlg ds (bytesAlg vp prims codec128s optRand pkSeedDist)),
      eufAdvG ds A ≤ betaEufG ds optRand pkSeedDist (bytesToTypedG ds A).main :=
  ⟨(rust_security optRand pkSeedDist).1,
    fun S => slhdsa_sha2_128s_bytes_suf_cmaG ds optRand pkSeedDist S,
    fun A => slhdsa_sha2_128s_bytes_euf_cmaG ds optRand pkSeedDist A⟩

/-- **Internal interface, linear form, forgers over `ds + unifSpec`.** -/
theorem rust_security_linearG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (liftAlg ds (bytesAlg vp prims codec128s optRand pkSeedDist)),
      sufAdvG ds S + linIdealSufG ds optRand pkSeedDist (bytesToTypedSG ds S).main ≤
        linRealSufG ds optRand pkSeedDist (bytesToTypedSG ds S).main) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (liftAlg ds (bytesAlg vp prims codec128s optRand pkSeedDist)),
      eufAdvG ds A + linIdealEufG ds optRand pkSeedDist (bytesToTypedG ds A).main ≤
        linRealEufG ds optRand pkSeedDist (bytesToTypedG ds A).main :=
  ⟨fun S => slhdsa_sha2_128s_bytes_suf_cma_linearG ds optRand pkSeedDist S,
    fun A => slhdsa_sha2_128s_bytes_euf_cma_linearG ds optRand pkSeedDist A⟩

/-- **External pure interface, forgers over `ds + unifSpec`.** -/
theorem rust_pure_securityG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.slh.slh_verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      sufAdvG ds S ≤
        betaSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      eufAdvG ds A ≤
        betaEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  ⟨(rust_pure_security optRand pkSeedDist).1,
    fun S => slhdsa_sha2_128s_pure_bytes_suf_cmaG ds optRand pkSeedDist S,
    fun A => slhdsa_sha2_128s_pure_bytes_euf_cmaG ds optRand pkSeedDist A⟩

/-- **External pure interface, linear form, forgers over `ds + unifSpec`.** -/
theorem rust_pure_security_linearG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      sufAdvG ds S +
          linIdealSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main ≤
        linRealSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      eufAdvG ds A +
          linIdealEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main ≤
        linRealEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  ⟨fun S => slhdsa_sha2_128s_pure_bytes_suf_cma_linearG ds optRand pkSeedDist S,
    fun A => slhdsa_sha2_128s_pure_bytes_euf_cma_linearG ds optRand pkSeedDist A⟩

/-- **Resources (internal interface)**: the general-spec resource bundle for the reduction
adversaries around the typed forger family of a byte-level forger with at most `qs` signing
queries. -/
theorem rust_security_resourcesG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary
      (liftAlg ds (bytesAlg vp prims codec128s optRand pkSeedDist))) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesG ds optRand pkSeedDist (bytesToTypedG ds A).main qs
      (Reduction.Resources2.directCounts128s qs) (269824 + qs * 2007385 + 7857) :=
  final_resourcesG_128s ds optRand pkSeedDist _ qs (bytesToTypedG_queryBound ds A qs hA)

end E2E

#print axioms E2E.rust_securityG
#print axioms E2E.rust_security_linearG
#print axioms E2E.rust_pure_securityG
#print axioms E2E.rust_pure_security_linearG
#print axioms E2E.rust_security_resourcesG
