import PQ.Interactive.Strategy
import PQ.Interactive.Wrap
import Reduction.Headline

/-!
# The standard-model SLH-DSA reduction against quantum forgers (integration)

NOT part of the default target of `quantum/`.  This file reads the compiled `Reduction.Headline`
of `security/` (read-only).  Check it with

```
cd quantum
LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/../security/.lake/build/lib/lean:\
$PWD/../.tools/aeneas/backends/lean/.lake/build/lib/lean" lean Integration/SlhDsa.lean
```

`slhdsa_euf_cma_final_quantum`: for every quantum forger `Q` (workspace `W`, classical signing
queries) against the internal SLH-DSA scheme whose Born probabilities are rational, the quantum
EUF-CMA advantage is at most the final bound of `Reduction.slhdsa_euf_cma_final`, evaluated at
the classical strategy `Q.toClassical` of the forger.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive

namespace Reduction

set_option linter.unusedSectionVars false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}
variable {W : Type} [Fintype W]

/-- **Standard-model EUF-CMA security of SLH-DSA against quantum forgers with classical signing
queries and rational Born probabilities.** -/
theorem slhdsa_euf_cma_final_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qUnforgeableAdvantage Q ≤
      boundFinal pkSeedDist (bPrfC Q.toClassical) (Lazy.bPrfMsgL Q.toClassical)
        (Lazy.bItsrL Q.toClassical)
        (toDspr (Lazy.bOpenPreS Q.toClassical)) (toTcr (Lazy.bOpenPreS Q.toClassical))
        (Lazy.bTcrS Q.toClassical)
        (rUd pkSeedDist (Lazy.bWotsS Q.toClassical)) (rPre pkSeedDist (Lazy.bWotsS Q.toClassical))
        (rTcr pkSeedDist (Lazy.bWotsS Q.toClassical)) :=
  qUnforgeableAdvantage_le_of_forall Q hQ betaEufFinal (slhdsa_euf_cma_final' hS)

/-- The SUF-CMA form. -/
theorem slhdsa_suf_cma_final_quantum (hS : Structural vp prims)
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist))
    (hQ : ∀ pk, RationalBorn (Q.main pk) Q.ρ₀) :
    qStrongUnforgeableAdvantage Q ≤ betaSufFinal Q.toClassicalStrong.toUnforgeableAdversary :=
  qStrongUnforgeableAdvantage_le_of_forall Q hQ
    (fun S ↦ betaSufFinal S.toUnforgeableAdversary) (slhdsa_suf_cma_final' hS)

/-- The harness `Reduction.runForger` is the generic harness `PQ.Interactive.runForgerG`, so
`toProbComp_qRunForger` applies: for every reduction adversary of the bound, the sub-program
`runForger Q.toClassical pk sign` is the classical strategy of the quantum machine "the harness
around the quantum forger". -/
theorem runForger_toClassical {ι : Type} {spec : OracleSpec ι}
    (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) (pk : PublicKeyCore prims.core)
    (sign : List Byte → OracleComp (unifSpec + spec) (GeneralScheme.SignatureCore vp prims.core)) :
    runForger Q.toClassical pk sign =
      toProbComp (qRunForger (Q.main pk) sign) Q.ρ₀ := by
  rw [toProbComp_qRunForger]
  rfl

end Reduction

#print axioms Reduction.slhdsa_euf_cma_final_quantum
#print axioms Reduction.slhdsa_suf_cma_final_quantum
#print axioms Reduction.runForger_toClassical
