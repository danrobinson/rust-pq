/-
Work package OPEN (R4/R5): the shared notion "the same primitive bundle with other hash
functions".  `prims.withHash T H P Pm` has the carrier types, the address-key map and the byte
encoding of `prims` (all definitionally), and the four hash components replaced.
-/
import Reduction.Lazy.Open

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Reduction
namespace Open

set_option linter.unusedTactic false

/-- The four hash components over the carrier types of `prims`. -/
structure HashFns {p : Params} (prims : Primitives p) where
  /-- the tweakable hash collection (`F`, `H`, `T_ℓ`) -/
  thash : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y
  /-- `H_msg(R, PK.seed, PK.root, M)` -/
  hmsg : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes p.m
  /-- `PRF(PK.seed, SK.seed, ADRS)` -/
  prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y
  /-- `PRF_msg(SK.prf, opt_rand, M)` -/
  prfMsg : prims.SkPrf → prims.Y → List Byte → prims.Y

/-- The hash components of `prims` itself. -/
@[reducible] def hashFnsOf {p : Params} (prims : Primitives p) : HashFns prims :=
  ⟨prims.Thash, prims.Hmsg, prims.PRF, prims.PRFmsg⟩

/-- `prims` with its four hash components replaced by `f`; carrier types, `adrsToKey` and
`yToBytes` are those of `prims`, definitionally. -/
@[reducible] def withHash {p : Params} (prims : Primitives p) (f : HashFns prims) : Primitives p where
  PkSeed := prims.PkSeed
  SkSeed := prims.SkSeed
  SkPrf := prims.SkPrf
  Y := prims.Y
  AdrsKey := prims.AdrsKey
  adrsToKey := prims.adrsToKey
  PRF := f.prf
  PRFmsg := f.prfMsg
  yToBytes := prims.yToBytes
  Thash := f.thash
  Hmsg := f.hmsg

/-- Replacing the hash components by themselves changes nothing. -/
theorem withHash_self {p : Params} (prims : Primitives p) :
    withHash prims (hashFnsOf prims) = prims := rfl

example {p : Params} (prims : Primitives p) (f : HashFns prims) : (withHash prims f).Y = prims.Y := rfl
example {p : Params} (prims : Primitives p) (f : HashFns prims) [DecidableEq prims.Y] :
    DecidableEq (withHash prims f).Y := inferInstance
example {p : Params} (prims : Primitives p) (f : HashFns prims) :
    publicHashSpec (withHash prims f).core = publicHashSpec prims.core := by
  first | rfl | (funext q; cases q <;> rfl) | (unfold publicHashSpec; funext q; cases q <;> rfl)

/-- `prims` with the two PUBLIC hash components (`Thash`, `H_msg`) replaced.  The core bundle
(carrier types, `adrsToKey`, `yToBytes`, `PRF`, `PRF_msg`) is literally that of `prims`, so every
type built from `prims.core` (`PublicKeyCore`, `SignatureCore`, `publicHashSpec`, the SM problems'
index/carrier types) is definitionally unchanged. -/
@[reducible] def withTH {p : Params} (prims : Primitives p)
    (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes p.m) : Primitives p :=
  { toCorePrimitives := prims.core, Thash := T, Hmsg := H }

theorem withTH_core {p : Params} (prims : Primitives p) (T H) :
    (withTH prims T H).core = prims.core := rfl

theorem withTH_self {p : Params} (prims : Primitives p) :
    withTH prims prims.Thash prims.Hmsg = prims := rfl

/-- A forger against the scheme over `prims`, read as a forger against the scheme over
`withTH prims T H`: the SAME program (`main` is untouched; its type mentions only `prims.core`). -/
def castForger {vp : ValidatedParams} {prims : Primitives vp.params}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
    {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}
    (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    Forger vp (withTH prims T H) optRand pkSeedDist :=
  ⟨A.main⟩

@[simp] theorem castForger_main {vp : ValidatedParams} {prims : Primitives vp.params}
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
    {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}
    (T : prims.PkSeed → prims.AdrsKey → List prims.Y → prims.Y)
    (H : prims.Y → prims.PkSeed → prims.Y → List Byte → Bytes vp.params.m)
    (A : Forger vp prims optRand pkSeedDist) :
    (castForger T H A).main = A.main := rfl

end Open
end Reduction
