import Reduction.Gen.Final
open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash
namespace Reduction.Gen
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
set_option pp.explicit false
example {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds]
    [∀ d, Fintype (ds.Range d)] (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) : True := by
  have B : GForger ds vp prims optRand pkSeedDist := embedAdv ds A
  have h := slhdsa_euf_cmaG ds hS B
  trivial
end Reduction.Gen
