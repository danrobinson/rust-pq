import ME2E.Sha2_128s
import ME2E.Api.Sha2_128s
import Reduction.Gen.Resolved

/-!
# SLH-DSA-SHA2-128s: the end-to-end statements for forgers over a general sampling spec

Port of the single-set tree's `E2E/HeadlineGen.lean` (`E2E.rust_securityG`, `rust_security_linearG`,
`rust_pure_securityG`, `rust_pure_security_linearG`, `rust_security_resourcesG`) and of
`E2E.api_pure_securityG` (its `E2E/Api.lean`; git commit `26aa3d8`) to the six-set tree's
SLH-DSA-SHA2-128s functions `slhdsa.sets.sha2_128s.*`. **128s only**: `Reduction/Gen` is stated at
`Link.vp`, `Link.prims`, `Reduction.codec128s`.

Each statement is the single-set one under these renamings only: Rust names `slhdsa.slh.slh_f` /
`slhdsa.api.f` -> `slhdsa.sets.sha2_128s.slh_f` / `slhdsa.sets.sha2_128s.f`; in part (a), the cores
`byteKeygen vp prims codec128s` etc. -> `byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s)`
(`rfl`-equal, `MIdeal.sha2_128s.vp_eq` …) and `node x` -> `node Sha2Set.s128s x`. The forger types and
the bounds are the single-set text verbatim (`vp`, `prims` are `Link.vp`, `Link.prims`). Part (a) is
part (a) of `ME2E.sha2_128s.rust_security` / `rust_pure_security` / `api_pure_cores`; parts (b), (c)
are `Reduction.Gen`'s 128s theorems, unchanged.

Forgers over `ds + unifSpec`, `ds` any oracle spec with an `AnswerMeasure` and finite answer types;
the right-hand advantages are those of `Reduction.Gen`'s wrapper games (`status/GEN.md`).
-/

namespace ME2E.sha2_128s

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open MLink (Sha2Set)
open MReduction (codec)
open Link (vp prims)
open Reduction (codec128s bytesAlg pureBytesAlg byteKeygen byteSign byteVerify byteSignPure
  byteVerifyPure)
open Reduction.Gen

variable {κ : Type} (ds : OracleSpec.{0, 0} κ) [OracleSpec.AnswerMeasure ds]
  [∀ d, Fintype (ds.Range d)]

/-- **Internal interface, forgers over `ds + unifSpec`.** -/
theorem rust_securityG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 152 →
        ∃ sig, slhdsa.sets.sha2_128s.slh_sign_internal m sk addrnd = ok sig ∧
          wire sig.val = byteSign Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sk.val) (node Sha2Set.s128s addrnd)) ∧
      (∀ (m sig : Slice U8) (pk : Array U8 32#usize), Room m.length 152 →
        slhdsa.sets.sha2_128s.slh_verify_internal m sig pk =
          ok (byteVerify Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire pk.val)))) ∧
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
        ∃ sk pk, slhdsa.sets.sha2_128s.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.sets.sha2_128s.slh_sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val)
              (node Sha2Set.s128s addrnd)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.sets.sha2_128s.slh_verify m sig ctx pk =
          ok (byteVerifyPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire ctx.val)
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

/-- **The interface, external pure scheme, forgers over `ds + unifSpec`.**
`rust_pure_securityG` with part (a) about the interface functions. -/
theorem api_pure_securityG (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ (seeds : Array U8 48#usize) (sk0 : Array U8 64#usize) (pk0 : Array U8 32#usize)
          (sk_seed sk_prf pk_seed : Array U8 16#usize),
        seeds.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val →
        ∃ sk pk, slhdsa.sets.sha2_128s.keygen seeds sk0 pk0 = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (node Sha2Set.s128s sk_seed) (node Sha2Set.s128s sk_prf) (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.sets.sha2_128s.sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val)
              (node Sha2Set.s128s addrnd)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize)
          (sk_seed sk_prf pk_seed pk_root : Array U8 16#usize),
        sk.val = sk_seed.val ++ sk_prf.val ++ pk_seed.val ++ pk_root.val → Room m.length 409 →
        ∃ r, slhdsa.sets.sha2_128s.sign_deterministic m ctx sk = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire ctx.val) (wire sk.val)
              (node Sha2Set.s128s pk_seed)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.sets.sha2_128s.verify m sig ctx pk =
          ok (byteVerifyPure Sha2Set.s128s.vp Sha2Set.s128s.prims (codec Sha2Set.s128s) (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      sufAdvG ds S ≤
        betaSufG ds optRand pkSeedDist (toInternalSG ds (pureBytesToTypedSG ds S)).main) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary
        (liftAlg ds (pureBytesAlg vp prims codec128s optRand pkSeedDist)),
      eufAdvG ds A ≤
        betaEufG ds optRand pkSeedDist (toInternalG ds (pureBytesToTypedG ds A)).main :=
  ⟨api_pure_cores, (rust_pure_securityG ds optRand pkSeedDist).2⟩


end ME2E.sha2_128s

#print axioms ME2E.sha2_128s.rust_securityG
#print axioms ME2E.sha2_128s.rust_security_linearG
#print axioms ME2E.sha2_128s.rust_pure_securityG
#print axioms ME2E.sha2_128s.rust_pure_security_linearG
#print axioms ME2E.sha2_128s.rust_security_resourcesG
#print axioms ME2E.sha2_128s.api_pure_securityG
