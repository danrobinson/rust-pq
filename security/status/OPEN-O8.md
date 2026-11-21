# OPEN-O8 — R5: the external / byte-level wrappers are independent of the hash functions
File: `Reduction/Open/Wrappers.lean` (new; imports `Reduction.Bytes`, `Reduction.Open.WithHash`; compiles
with no error/warning, ~2 min; olean written to `.lake/build/lib/lean/Reduction/Open/Wrappers.olean`).
Namespace `Reduction.Open`. No sorry/axiom/native_decide. No existing file touched. No deviation from the
mandatory formulation; no wrapper computes a digest or verifies — nothing had to be weakened.
Ambient variables: `{vp} {prims : Primitives vp.params} [SampleableType prims.SkSeed]
[SampleableType prims.SkPrf] [DecidableEq prims.Y] {codec : CoreWireCodec vp.params prims.core} {optRand}
{pkSeedDist} (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
(H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m) [Inhabited prims.Y]`.
## Casts (same program `⟨A.main⟩`, like `Open.castForger`; each has a simp lemma `cast*_main : (cast* T H A).main = A.main`)
    castForgerS    : StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist) → StrongUnforgeableAdversary (internalAlg vp (withTH prims T H) optRand pkSeedDist)
    castExt        : ExtForger vp prims optRand pkSeedDist → ExtForger vp (withTH prims T H) optRand pkSeedDist
    castExtS, castBytes, castBytesS, castPureBytes, castPureBytesS : likewise for ExtStrongForger, BytesForger,
      BytesStrongForger, PureBytesForger, PureBytesStrongForger (… prims … → … (withTH prims T H) …)
(the same `codec` is used on both sides: its type mentions only `prims.core`.)
## R5, replacement form (all by `rfl`)
    theorem toInternal_open (A : ExtForger vp prims optRand pkSeedDist) :
        toInternal (castExt T H A) = castForger T H (toInternal A)
    theorem toInternalS_open (A : ExtStrongForger vp prims optRand pkSeedDist) :
        toInternalS (castExtS T H A) = castForgerS T H (toInternalS A)
    theorem bytesToTyped_open (A : BytesForger vp prims codec optRand pkSeedDist) :
        bytesToTyped (castBytes T H A) = castForger T H (bytesToTyped A)
    theorem bytesToTypedS_open (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
        bytesToTypedS (castBytesS T H A) = castForgerS T H (bytesToTypedS A)
    theorem pureBytesToTyped_open (A : PureBytesForger vp prims codec optRand pkSeedDist) :
        pureBytesToTyped (castPureBytes T H A) = castExt T H (pureBytesToTyped A)
    theorem pureBytesToTypedS_open (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
        pureBytesToTypedS (castPureBytesS T H A) = castExtS T H (pureBytesToTypedS A)
Each also as `*_open_main : (W (cast… T H A)).main = (W A).main` (e.g. `toInternal_open_main`).
`toUnforgeableAdversary` (definition `⟨adv.main⟩`): `toUnforgeableAdversary_main : A.toUnforgeableAdversary.main = A.main`,
and `castForgerS_/castExtS_/castBytesS_/castPureBytesS_toUnforgeableAdversary :
(castXS T H A).toUnforgeableAdversary = castX T H A.toUnforgeableAdversary`.
The two forgers of the headline (FINAL3 §1):
    theorem headline_bytes_open (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
        (bytesToTypedS (castBytesS T H S)).toUnforgeableAdversary = castForger T H (bytesToTypedS S).toUnforgeableAdversary
    theorem headline_pureBytes_open (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
        toInternal (pureBytesToTyped (castPureBytesS T H S).toUnforgeableAdversary) =
          castForger T H (toInternal (pureBytesToTyped S.toUnforgeableAdversary))
## "Wrappers make no hash queries": explicit programs
Defined with `{core : CorePrimitives vp.params}` only — no `Primitives` (so no `Thash`/`Hmsg`) is in scope:
    def constSigC (y : core.Y) : GeneralScheme.SignatureCore vp core
    def extProg (y : core.Y) (main : PublicKeyCore core → OracleComp (unifSpec + ((List Byte × List Byte) →ₒ Except External.Error (SignatureCore vp core))) (…))
        (pk : PublicKeyCore core) : OracleComp (unifSpec + (List Byte →ₒ SignatureCore vp core)) (List Byte × SignatureCore vp core) :=
      Guarded.readForgery pureEncode ([], constSigC y) <$> simulateQ (Guarded.signingImpl pureEncode) (main pk)
    def bytesImpl (codec) : QueryImpl (unifSpec + (List Byte →ₒ List Byte)) (OracleComp (unifSpec + (List Byte →ₒ SignatureCore vp core)))
      -- .inl t ↦ query (.inl t);  .inr m ↦ encodeSignature vp codec <$> query (.inr m)
    def bytesProg (codec) (y : core.Y) (main : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte)) (pk) :=
      (fun out => (out.1, ((decodeSignature vp codec out.2).toOption).getD (constSigC y))) <$> simulateQ (bytesImpl codec) (main (encodePublicKey codec pk))
    def encPureSigC, decPureSigC, pureBytesImpl (codec)   -- as bytesImpl, answer encoded by encPureSigC
    def pureBytesProg (codec) (main) (pk) :=
      (fun out => (out.1, (decPureSigC codec out.2).getD (.error (.contextTooLong 0)))) <$> simulateQ (pureBytesImpl codec) (main (encodePublicKey codec pk))
The only oracle queries are those issued by the handlers (`Guarded.signingImpl pureEncode`: forward sampling;
≤ 1 signing query per signing query; `bytesImpl`/`pureBytesImpl`: forward sampling; exactly 1 signing query).
    theorem toInternal_main        : (toInternal A).main        = extProg (core := prims.core) default A.main         -- rfl
    theorem bytesToTyped_main      : (bytesToTyped A).main      = bytesProg (core := prims.core) codec default A.main
    theorem pureBytesToTyped_main  : (pureBytesToTyped A).main  = pureBytesProg (core := prims.core) codec A.main
    toInternalS_main, bytesToTypedS_main, pureBytesToTypedS_main : the same right-hand sides for the S-wrappers
    theorem headline_bytes_main     : (bytesToTypedS S).toUnforgeableAdversary.main = bytesProg (core := prims.core) codec default S.main
    theorem headline_pureBytes_main : (toInternal (pureBytesToTyped S.toUnforgeableAdversary)).main =
        extProg (core := prims.core) default (pureBytesProg (core := prims.core) codec S.main)
## Existing signing-query bounds (`≤ qs`; cited, not re-proved)
Hypothesis/conclusion shape `∀ pk, IsQueryBoundP (X.main pk) (fun i => i.isRight = true) qs`:
`toInternal_queryBound`, `Guarded.reduce_queryBound` (Reduction/External.lean); `toInternalS_queryBound`,
`Guarded.reduceS_queryBound` (Reduction/ExternalSuf.lean); `bytesToTyped_queryBound`, `bytesToTypedS_queryBound`,
`pureBytesToTyped_queryBound`, `pureBytesToTypedS_queryBound`, `toInternal_pureBytesToTyped_queryBound`,
`Coded.reduce_queryBound`, `Coded.reduceS_queryBound` (Reduction/Bytes.lean). By the `*_main` equations they
are bounds for `extProg`/`bytesProg`/`pureBytesProg`. `toUnforgeableAdversary` keeps `main`, hence the bound.
## Not done: all four components (`Open.withHash prims f`)
`PRF`/`PRFmsg` are fields of `prims.core`, and `PublicKeyCore core`, `SignatureCore vp core`,
`CoreWireCodec p core` are indexed by the whole `core`; over `(withHash prims f).core` the wrappers live over a
different (not definitionally equal) oracle spec and key type. A statement needs field-wise bijections for
`PublicKeyCore`/`SignatureCore`, a transported codec, a relabelling of `unifSpec + (M →ₒ S)` programs along
them, and "relabel (wrapper over withHash) = wrapper over prims". Available instead: the `*_main` equations —
the programs take a `CorePrimitives` and use only its carrier types, `default : core.Y` and the codec; that
they do not apply `core.PRF`/`core.PRFmsg` is visible in the definitions but is not a theorem.
## 128s numerals: none (statements are generic in `vp`, `prims`, `codec`; instantiate at `Link.vp`, `Link.prims`, `codec128s`).
## Axioms
`#print axioms` for `toInternal_open`, `toInternalS_open`, `bytesToTyped_open`, `bytesToTypedS_open`,
`pureBytesToTyped_open`, `pureBytesToTypedS_open`, `headline_bytes_open`, `headline_pureBytes_open`, the six
`*_main`, `headline_pureBytes_main`: each `[propext, Classical.choice, Quot.sound]`.
