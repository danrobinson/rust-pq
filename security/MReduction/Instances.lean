import Reduction.ResourcesFinal
import MLink.Basic

/-!
# The six SHA-2 parameter sets as instances of the generic reduction

`Reduction` is generic over `vp : ValidatedParams`, `prims : Primitives vp.params` with the single
non-cryptographic hypothesis `Structural vp prims`.  This file supplies, for every
`S : MLink.Sha2Set`: `structural S`, `keyDiscipline S`, the wire codec `codec S`
(`sha2WireCodec S.vp.params`; definitionally VCVio's `approvedWireCodec S.fips` at each set), and
the class instances the final theorems ask for on `S.prims.Y = Bytes S.vp.params.n`
(`Inhabited`, `Fintype`; `DecidableEq`, `SampleableType` are found by instance resolution).
At `.s128s` everything is definitionally the SHA2-128s object of `security/Reduction`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace MReduction

open MLink Reduction

variable (S : Sha2Set)

/-- A default node (all zero); only used to state games (`Inhabited prims.Y`). -/
instance instInhabitedY : Inhabited S.prims.Y := ⟨Vector.replicate S.vp.params.n 0⟩

/-- `Y = Vector UInt8 n` is finite (needed only to state the DSPR game). -/
instance instFintypeY : Fintype S.prims.Y :=
  inferInstanceAs (Fintype (Vector UInt8 S.vp.params.n))

/-- The structural side conditions hold at every SHA-2 parameter set: `Bytes n` nodes are their
own encoding, the compressed address `ADRSc` is injective on in-range addresses, and the FIPS
address widths hold (`fipsApprovedAddressBounds`; at 256f the tree index has exactly 64 bits). -/
theorem structural : Structural S.vp S.prims :=
  have hb : ApprovedAddressBounds S.vp.params := fipsApprovedAddressBounds S.fips
  ⟨Concrete.sha2Primitives_byteLaws S.vp.params,
    Concrete.keyInjective_sha2Primitives S.vp hb, hb.toCanonicalAddressBounds⟩

/-- The full VCVio key discipline (adds key separation, which `Structural` does not need). -/
theorem keyDiscipline : S.prims.core.KeyDiscipline S.vp :=
  Concrete.keyDiscipline_sha2Primitives S.vp (fipsApprovedAddressBounds S.fips)

/-- The atomic wire codec of the set: every carrier is `n` bytes, encoded as itself.
`decodeSignature S.vp (codec S) = MLink.decodeSig S`, `decodePublicKey (codec S) = MLink.decodePk S`
by unfolding; equal to VCVio's `approvedWireCodec S.fips` at each set (`rfl`, below). -/
abbrev codec : CoreWireCodec S.vp.params S.prims.core := SLHDSA.Concrete.sha2WireCodec S.vp.params

example : codec .s128s = SLHDSA.Concrete.approvedWireCodec .SLHDSA_SHA2_128s := rfl
example : codec .s128f = SLHDSA.Concrete.approvedWireCodec .SLHDSA_SHA2_128f := rfl
example : codec .s192s = SLHDSA.Concrete.approvedWireCodec .SLHDSA_SHA2_192s := rfl
example : codec .s192f = SLHDSA.Concrete.approvedWireCodec .SLHDSA_SHA2_192f := rfl
example : codec .s256s = SLHDSA.Concrete.approvedWireCodec .SLHDSA_SHA2_256s := rfl
example : codec .s256f = SLHDSA.Concrete.approvedWireCodec .SLHDSA_SHA2_256f := rfl

theorem codec_heq_approved : HEq (codec S) (SLHDSA.Concrete.approvedWireCodec S.fips) := by
  cases S <;> rfl

/-- The FIPS conversion `PK.seed ↦ opt_rand` of deterministic signing is the identity on
`Bytes n` at every set. -/
theorem detRand (s : S.prims.PkSeed) :
    SLHDSA.Concrete.sha2RandomizerOfPkSeed S.vp.params s = s := rfl

/-! ### At `.s128s` these are the objects of `security/Reduction` -/

example : Sha2Set.s128s.fips = Link.S128 := rfl
example : Sha2Set.s128s.vp = Link.vp := rfl
example : Sha2Set.s128s.prims = Link.prims := rfl
example : codec .s128s = Reduction.codec128s := rfl
example : (instInhabitedY .s128s : Inhabited Link.prims.Y).default = (default : Bytes 16) := rfl
example : (default : Link.prims.Y) = Vector.replicate 16 0 := rfl
example : (instFintypeY .s128s : Fintype Link.prims.Y) = Reduction.instFintypeY128s := rfl
example : structural .s128s = Reduction.structural_128s := rfl

/-- The class instances the final theorems need are all available at every set. -/
example : SampleableType S.prims.SkSeed := inferInstance
example : SampleableType S.prims.SkPrf := inferInstance
example : SampleableType S.prims.Y := inferInstance
example : SampleableType S.prims.PkSeed := inferInstance
example : DecidableEq S.prims.Y := inferInstance
example : DecidableEq S.prims.PkSeed := inferInstance
example : DecidableEq S.prims.AdrsKey := inferInstance

#print axioms structural
#print axioms keyDiscipline

end MReduction
