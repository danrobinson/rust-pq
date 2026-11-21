import PQ.Interactive.Strategy
import Reduction.Gen.Final

/-!
Scratch check (not part of any library): quantum's exact collapse theorem
(`PQ/Interactive/Strategy.lean`) composes with the general-spec headline at `ds := distSpec`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction.Gen

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

/-- quantum's `liftSig` is our `liftAlg` at `distSpec`. -/
example (sigAlg : SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core)
    (SecretKeyCore prims.core) (GeneralScheme.SignatureCore vp prims.core)) :
    liftSig sigAlg = liftAlg distSpec sigAlg := rfl

/-- EUF-CMA of the typed internal scheme against ALL quantum forgers (no rationality
hypothesis), by one application of quantum's lifting principle to the general-spec headline. -/
theorem slhdsa_euf_cma_quantum_viaG (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ betaEufG distSpec optRand pkSeedDist Q.toStrategy.main :=
  qUnforgeableAdvantage_le_of_forall_strategy Q
    (fun A ↦ betaEufG distSpec optRand pkSeedDist A.main) (fun A ↦ slhdsa_euf_cmaG distSpec hS A)

end Reduction.Gen

#print axioms Reduction.Gen.slhdsa_euf_cma_quantum_viaG
