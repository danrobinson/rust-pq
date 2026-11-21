import HashSig.SLHDSA.Concrete.Codec
import HashSig.SLHDSA.GeneralScheme

/-!
# Stand-in for `security/Link/Basic.lean` (Spec-free part, verbatim)

`security/Reduction` states its SHA2-128s instances at `Link.vp`, `Link.prims`.  The original
`Link.Basic` also imports the single-set `Spec` of `/lean`, whose declarations clash with the
parameterised `Spec` of `multi/lean`; this module keeps exactly the declarations that do not mention
`Spec`, with the same names and bodies, so that `security/Reduction` compiles unmodified.
-/

namespace Link

open SLHDSA SLHDSA.Concrete

/-- The parameter set of the single-set development. -/
abbrev S128 : FipsParameterSet := .SLHDSA_SHA2_128s
/-- Its validated parameters (`n=16, h=63, d=7, h'=9, a=12, k=14, lg w=4`). -/
abbrev vp : ValidatedParams := S128.validatedParams
/-- VCVio's executable FIPS SHA-2 primitive bundle at SLH-DSA-SHA2-128s
(definitionally `approvedPrimitives S128`). -/
abbrev prims : Primitives vp.params := sha2Primitives vp.params

theorem prims_eq_approved : prims = approvedPrimitives S128 := rfl

/-- `n`-byte nodes of the bundle. -/
abbrev Node : Type := Bytes 16

/-- The checked SHA-2 `ADRSc` domain (`Sha2Address`): canonical, one-byte layer, eight-byte tree. -/
def Dom (a : SLHDSA.Adrs) : Prop :=
  a.isCanonical = true ∧ Adrs.Fits 1 a.layer = true ∧ Adrs.Fits 8 a.tree = true

/-- A hypertree base address `(layer, tree)` in the SHA-2 domain. -/
def BaseDom (a : SLHDSA.Adrs) : Prop := a.layer < 256 ∧ a.tree < 2 ^ 64

end Link
