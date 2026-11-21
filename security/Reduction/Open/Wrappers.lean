/-
Work package OPEN, item R5: the external / byte-level wrappers are independent of the hash
functions.

Wrappers: `toInternal`, `toInternalS` (external pure interface → internal interface),
`bytesToTyped`, `bytesToTypedS`, `pureBytesToTyped`, `pureBytesToTypedS` (wire encodings → typed
interface), and `StrongUnforgeableAdversary.toUnforgeableAdversary`.

Two forms.

1. **Explicit programs** (`extProg`, `bytesProg`, `pureBytesProg`).  They are defined over a
   `core : CorePrimitives vp.params` only — there is no `Primitives` (hence no `Thash`, `Hmsg`)
   in scope of their definitions — and are programs over `unifSpec + signing oracle` that run
   the input program once under an explicit query handler (`Guarded.signingImpl pureEncode`,
   `bytesImpl`, `pureBytesImpl`).  `*_main` : the `main` of each wrapper IS that program at
   `prims.core` (by `rfl`).  Of `core`, the programs use the carrier types, `default : core.Y`
   and the wire codec; they do not apply `PRF`/`PRFmsg` either (visible in the definitions; not
   a theorem, see the remark at the end).

2. **Replacement form** (`*_open`).  For all `T`, `H`: the wrapper built over
   `Open.withTH prims T H` from the same input program equals the one built over `prims`
   (`Open.castForger`-style casts `⟨A.main⟩`; all by `rfl`).

No wrapper computes a message digest or verifies; nothing had to be weakened.
-/
import Reduction.Bytes
import Reduction.Open.WithHash

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false

/-! ## 1. The explicit programs, over `CorePrimitives` only -/

section Programs

variable {vp : ValidatedParams} {core : CorePrimitives vp.params}

/-- `Reduction.constSig` over a `CorePrimitives`: the signature all of whose nodes are `y`. -/
def constSigC (y : core.Y) : GeneralScheme.SignatureCore vp core :=
  ⟨y, Vector.replicate _ ⟨y, Vector.replicate _ y⟩,
    Vector.replicate _ ⟨Vector.replicate _ y, Vector.replicate _ y⟩⟩

/-- **The program of `toInternal` / `toInternalS`.**  Run `main pk` once; sampling queries are
forwarded; a signing query `(M, ctx)` is answered by `.error` if `|ctx| > 255` (no query) and
otherwise by one signing query on `0x00 ‖ |ctx| ‖ ctx ‖ M`; the output is re-read by
`Guarded.readForgery`. -/
def extProg (y : core.Y)
    (main : PublicKeyCore core →
      OracleComp (unifSpec + ((List Byte × List Byte) →ₒ
        Except External.Error (GeneralScheme.SignatureCore vp core)))
        ((List Byte × List Byte) × Except External.Error (GeneralScheme.SignatureCore vp core)))
    (pk : PublicKeyCore core) :
    OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (List Byte × GeneralScheme.SignatureCore vp core) :=
  Guarded.readForgery pureEncode ([], constSigC y) <$>
    simulateQ (Guarded.signingImpl pureEncode) (main pk)

variable (codec : CoreWireCodec vp.params core)

/-- Query handler of `bytesToTyped(S)`: sampling queries forwarded; a signing query `M` is one
typed signing query `M`, the answer encoded. -/
def bytesImpl :
    QueryImpl (unifSpec + (List Byte →ₒ List Byte))
      (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core)))
  | .inl t => (query (spec := unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr m => encodeSignature vp codec <$>
      (query (spec := unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core)) (.inr m) :
        OracleComp _ (GeneralScheme.SignatureCore vp core))

/-- **The program of `bytesToTyped` / `bytesToTypedS`.**  Encode the public key, run `main`
once under `bytesImpl`, decode the output signature (`constSigC y` if it does not parse). -/
def bytesProg (y : core.Y)
    (main : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))
    (pk : PublicKeyCore core) :
    OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp core))
      (List Byte × GeneralScheme.SignatureCore vp core) :=
  (fun out => (out.1, ((decodeSignature vp codec out.2).toOption).getD (constSigC y))) <$>
    simulateQ (bytesImpl codec) (main (encodePublicKey codec pk))

/-- Encoding of a typed external signature value (`encodePureSig` over a `CorePrimitives`). -/
def encPureSigC (s : Except External.Error (GeneralScheme.SignatureCore vp core)) :
    Option (List Byte) :=
  s.toOption.map (encodeSignature vp codec)

/-- Parser of a byte-level external signature value (`decodePureSig` over a `CorePrimitives`). -/
def decPureSigC : Option (List Byte) →
    Option (Except External.Error (GeneralScheme.SignatureCore vp core))
  | none => none
  | some raw => (decodeSignature vp codec raw).toOption.map Except.ok

/-- Query handler of `pureBytesToTyped(S)`: sampling queries forwarded; a signing query
`(M, ctx)` is one typed (external) signing query `(M, ctx)`, the answer encoded. -/
def pureBytesImpl :
    QueryImpl (unifSpec + ((List Byte × List Byte) →ₒ Option (List Byte)))
      (OracleComp (unifSpec + ((List Byte × List Byte) →ₒ
        Except External.Error (GeneralScheme.SignatureCore vp core))))
  | .inl t => (query (spec := unifSpec + ((List Byte × List Byte) →ₒ
        Except External.Error (GeneralScheme.SignatureCore vp core)))
      (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr m => encPureSigC codec <$>
      (query (spec := unifSpec + ((List Byte × List Byte) →ₒ
        Except External.Error (GeneralScheme.SignatureCore vp core))) (.inr m) :
        OracleComp _ (Except External.Error (GeneralScheme.SignatureCore vp core)))

/-- **The program of `pureBytesToTyped` / `pureBytesToTypedS`.** -/
def pureBytesProg
    (main : List Byte → OracleComp (unifSpec + ((List Byte × List Byte) →ₒ Option (List Byte)))
      ((List Byte × List Byte) × Option (List Byte)))
    (pk : PublicKeyCore core) :
    OracleComp (unifSpec + ((List Byte × List Byte) →ₒ
        Except External.Error (GeneralScheme.SignatureCore vp core)))
      ((List Byte × List Byte) × Except External.Error (GeneralScheme.SignatureCore vp core)) :=
  (fun out => (out.1, (decPureSigC codec out.2).getD (.error (.contextTooLong 0)))) <$>
    simulateQ (pureBytesImpl codec) (main (encodePublicKey codec pk))

end Programs

/-! ## 2. The wrappers are these programs; replacement of `Thash`, `Hmsg` -/

section Wrappers

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
  (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)

/-! ### Casts: the same program against the scheme over `withTH prims T H` -/

/-- Strong forger against the internal scheme, over `withTH prims T H`: the same program. -/
def castForgerS (A : SignatureAlg.StrongUnforgeableAdversary
      (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.StrongUnforgeableAdversary
      (internalAlg vp (withTH prims T H) optRand pkSeedDist) := ⟨A.main⟩

/-- External pure forger over `withTH prims T H`: the same program. -/
def castExt (A : ExtForger vp prims optRand pkSeedDist) :
    ExtForger vp (withTH prims T H) optRand pkSeedDist := ⟨A.main⟩

/-- External pure strong forger over `withTH prims T H`: the same program. -/
def castExtS (A : ExtStrongForger vp prims optRand pkSeedDist) :
    ExtStrongForger vp (withTH prims T H) optRand pkSeedDist := ⟨A.main⟩

/-- Byte-level forger over `withTH prims T H`: the same program. -/
def castBytes (A : BytesForger vp prims codec optRand pkSeedDist) :
    BytesForger vp (withTH prims T H) codec optRand pkSeedDist := ⟨A.main⟩

/-- Byte-level strong forger over `withTH prims T H`: the same program. -/
def castBytesS (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    BytesStrongForger vp (withTH prims T H) codec optRand pkSeedDist := ⟨A.main⟩

/-- Byte-level external pure forger over `withTH prims T H`: the same program. -/
def castPureBytes (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    PureBytesForger vp (withTH prims T H) codec optRand pkSeedDist := ⟨A.main⟩

/-- Byte-level external pure strong forger over `withTH prims T H`: the same program. -/
def castPureBytesS (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    PureBytesStrongForger vp (withTH prims T H) codec optRand pkSeedDist := ⟨A.main⟩

@[simp] theorem castForgerS_main (A : SignatureAlg.StrongUnforgeableAdversary
    (internalAlg vp prims optRand pkSeedDist)) : (castForgerS T H A).main = A.main := rfl
@[simp] theorem castExt_main (A : ExtForger vp prims optRand pkSeedDist) :
    (castExt T H A).main = A.main := rfl
@[simp] theorem castExtS_main (A : ExtStrongForger vp prims optRand pkSeedDist) :
    (castExtS T H A).main = A.main := rfl
@[simp] theorem castBytes_main (A : BytesForger vp prims codec optRand pkSeedDist) :
    (castBytes T H A).main = A.main := rfl
@[simp] theorem castBytesS_main (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (castBytesS T H A).main = A.main := rfl
@[simp] theorem castPureBytes_main (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    (castPureBytes T H A).main = A.main := rfl
@[simp] theorem castPureBytesS_main (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    (castPureBytesS T H A).main = A.main := rfl

/-! ### `toUnforgeableAdversary` (forgets "strong"; the same program) commutes with the casts -/

theorem toUnforgeableAdversary_main {M PK SK S : Type} {alg : SignatureAlg ProbComp M PK SK S}
    (A : SignatureAlg.StrongUnforgeableAdversary alg) :
    A.toUnforgeableAdversary.main = A.main := rfl

theorem castForgerS_toUnforgeableAdversary (A : SignatureAlg.StrongUnforgeableAdversary
    (internalAlg vp prims optRand pkSeedDist)) :
    (castForgerS T H A).toUnforgeableAdversary = castForger T H A.toUnforgeableAdversary := rfl
theorem castExtS_toUnforgeableAdversary (A : ExtStrongForger vp prims optRand pkSeedDist) :
    (castExtS T H A).toUnforgeableAdversary = castExt T H A.toUnforgeableAdversary := rfl
theorem castBytesS_toUnforgeableAdversary
    (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (castBytesS T H A).toUnforgeableAdversary = castBytes T H A.toUnforgeableAdversary := rfl
theorem castPureBytesS_toUnforgeableAdversary
    (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    (castPureBytesS T H A).toUnforgeableAdversary =
      castPureBytes T H A.toUnforgeableAdversary := rfl

variable [Inhabited prims.Y]

/-! ### The wrappers are the explicit programs at `prims.core` -/

theorem toInternal_main (A : ExtForger vp prims optRand pkSeedDist) :
    (toInternal A).main = extProg (core := prims.core) default A.main := rfl

theorem toInternalS_main (A : ExtStrongForger vp prims optRand pkSeedDist) :
    (toInternalS A).main = extProg (core := prims.core) default A.main := rfl

theorem bytesToTyped_main (A : BytesForger vp prims codec optRand pkSeedDist) :
    (bytesToTyped A).main = bytesProg (core := prims.core) codec default A.main := by
  funext pk
  show _ <$> simulateQ _ _ = _ <$> simulateQ _ _
  congr 2
  funext q; cases q <;> rfl

theorem bytesToTypedS_main (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (bytesToTypedS A).main = bytesProg (core := prims.core) codec default A.main :=
  bytesToTyped_main A.toUnforgeableAdversary

theorem pureBytesToTyped_main (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    (pureBytesToTyped A).main = pureBytesProg (core := prims.core) codec A.main := by
  funext pk
  show _ <$> simulateQ _ _ = _ <$> simulateQ _ _
  congr 2
  funext q; cases q <;> rfl

theorem pureBytesToTypedS_main (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    (pureBytesToTypedS A).main = pureBytesProg (core := prims.core) codec A.main :=
  pureBytesToTyped_main A.toUnforgeableAdversary

/-! ### R5: replacement of `Thash`, `Hmsg` -/

/-- **R5, `toInternal`.** -/
theorem toInternal_open (A : ExtForger vp prims optRand pkSeedDist) :
    toInternal (castExt T H A) = castForger T H (toInternal A) := rfl

theorem toInternal_open_main (A : ExtForger vp prims optRand pkSeedDist) :
    (toInternal (castExt T H A)).main = (toInternal A).main := rfl

/-- **R5, `toInternalS`.** -/
theorem toInternalS_open (A : ExtStrongForger vp prims optRand pkSeedDist) :
    toInternalS (castExtS T H A) = castForgerS T H (toInternalS A) := rfl

theorem toInternalS_open_main (A : ExtStrongForger vp prims optRand pkSeedDist) :
    (toInternalS (castExtS T H A)).main = (toInternalS A).main := rfl

/-- **R5, `bytesToTyped`.** -/
theorem bytesToTyped_open (A : BytesForger vp prims codec optRand pkSeedDist) :
    bytesToTyped (castBytes T H A) = castForger T H (bytesToTyped A) := rfl

theorem bytesToTyped_open_main (A : BytesForger vp prims codec optRand pkSeedDist) :
    (bytesToTyped (castBytes T H A)).main = (bytesToTyped A).main := rfl

/-- **R5, `bytesToTypedS`.** -/
theorem bytesToTypedS_open (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    bytesToTypedS (castBytesS T H A) = castForgerS T H (bytesToTypedS A) := rfl

theorem bytesToTypedS_open_main (A : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (bytesToTypedS (castBytesS T H A)).main = (bytesToTypedS A).main := rfl

/-- **R5, `pureBytesToTyped`.** -/
theorem pureBytesToTyped_open (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    pureBytesToTyped (castPureBytes T H A) = castExt T H (pureBytesToTyped A) := rfl

theorem pureBytesToTyped_open_main (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    (pureBytesToTyped (castPureBytes T H A)).main = (pureBytesToTyped A).main := rfl

/-- **R5, `pureBytesToTypedS`.** -/
theorem pureBytesToTypedS_open (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    pureBytesToTypedS (castPureBytesS T H A) = castExtS T H (pureBytesToTypedS A) := rfl

theorem pureBytesToTypedS_open_main (A : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    (pureBytesToTypedS (castPureBytesS T H A)).main = (pureBytesToTypedS A).main := rfl

/-! ### The two forgers of the headline (status/FINAL3.md §1) -/

/-- The forger of the byte-level internal SUF headline. -/
theorem headline_bytes_open (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (bytesToTypedS (castBytesS T H S)).toUnforgeableAdversary =
      castForger T H (bytesToTypedS S).toUnforgeableAdversary := rfl

/-- The forger of the byte-level external pure SUF headline. -/
theorem headline_pureBytes_open (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    toInternal (pureBytesToTyped (castPureBytesS T H S).toUnforgeableAdversary) =
      castForger T H (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) := rfl

/-- The headline forgers as explicit programs over `prims.core`. -/
theorem headline_bytes_main (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (bytesToTypedS S).toUnforgeableAdversary.main =
      bytesProg (core := prims.core) codec default S.main :=
  bytesToTypedS_main S

theorem headline_pureBytes_main (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    (toInternal (pureBytesToTyped S.toUnforgeableAdversary)).main =
      extProg (core := prims.core) default (pureBytesProg (core := prims.core) codec S.main) := by
  rw [toInternal_main, pureBytesToTyped_main]; rfl

end Wrappers

/-
Remark (all four components, `Open.withHash prims f`).  Not stated.  `withHash` also replaces
`PRF`/`PRFmsg`, which are fields of `prims.core`; `PublicKeyCore core`, `SignatureCore vp core`,
`CoreWireCodec p core` are indexed by the whole `core`, so over `(withHash prims f).core` the
wrappers are programs over a DIFFERENT (not definitionally, and not provably, equal) oracle
specification and public-key type.  A statement needs: the evident bijections
`PublicKeyCore (withHash prims f).core ≃ PublicKeyCore prims.core`, the same for `SignatureCore`
(field by field) and for the codec, the induced relabelling of `unifSpec + (M →ₒ S)` programs,
and then "relabel (wrapper over withHash) = wrapper over prims".  What IS available here: every
wrapper's `main` equals `extProg` / `bytesProg` / `pureBytesProg` at `prims.core`, whose
definitions take a `CorePrimitives` and use only its carrier types, `default : core.Y` and the
codec.
-/

#print axioms toInternal_open
#print axioms toInternalS_open
#print axioms bytesToTyped_open
#print axioms bytesToTypedS_open
#print axioms pureBytesToTyped_open
#print axioms pureBytesToTypedS_open
#print axioms headline_bytes_open
#print axioms headline_pureBytes_open
#print axioms toInternal_main
#print axioms toInternalS_main
#print axioms bytesToTyped_main
#print axioms bytesToTypedS_main
#print axioms pureBytesToTyped_main
#print axioms pureBytesToTypedS_main
#print axioms headline_pureBytes_main

end Open
end Reduction
