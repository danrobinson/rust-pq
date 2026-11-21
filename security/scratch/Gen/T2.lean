import Reduction.Gen.Forger
import Reduction.Gen.GameTcr

/-!
# The arity-`n` SM-TCR adversary around a general-spec forger (`bTcrArM`)

`bTcrArMG ds n F`: phase 1 is the (forger-independent, classical) phase 1 of `bTcrArM n ·`;
phase 2 is `memoForge` with the forger run through `g2RunG`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Reduction.Gen

attribute [local irreducible] arityTargets tcrTargets

set_option linter.unusedSectionVars false

variable {κ : Type} (ds : OracleSpec κ) [OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]
variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- Phase 2 of `bTcrArMG`: `memoForge` around a general-spec forger. -/
noncomputable def memoForgeG (n : ℕ) (F : GFam ds vp prims)
    (s : SecretTable vp prims × List (prims.AdrsKey × List prims.Y)) (pkSeed : prims.PkSeed) :
    OracleComp (gSpec ds) (ℕ × {xs : List prims.Y // xs.length = n}) :=
  g2RunG ds optRand F s.1 (idealPk vp prims s.1 pkSeed) >>= fun z ↦
    pure (classOut prims n s.2
      ((findCollisionM pkSeed s.2
        (verifyCalls (idealPk vp prims s.1 pkSeed) z.1.1 z.1.2)).getD (0, [])))

/-- **`bTcrArM n` around a general-spec forger.** -/
noncomputable def bTcrArMG (n : ℕ) (F : GFam ds vp prims) :
    SM_DT_TCR_AdversaryG ds (thashArityProblemT vp prims pkSeedDist n) where
  State := SecretTable vp prims × List (prims.AdrsKey × List prims.Y)
  choose := embed ds (bTcrArM n (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist))).choose
  forge := memoForgeG ds optRand n F

variable {optRand pkSeedDist}

/-- **Naturality.** On a classical forger, `bTcrArMG` is `bTcrArM`. -/
theorem bTcrArMG_embed (n : ℕ) (A : Forger vp prims optRand pkSeedDist) :
    bTcrArMG ds optRand pkSeedDist n (fun pk ↦ embed ds (A.main pk)) =
      SM_DT_TCR_AdversaryG.ofClassical ds (bTcrArM n A) := by
  unfold bTcrArMG SM_DT_TCR_AdversaryG.ofClassical
  congr 1
  funext s pkSeed
  simp only [memoForgeG, g2RunG_embed, bTcrArM_forge, memoForge, liftR_bind, liftR_pure]

/-- **Linearity.** The wrapper-game advantage of `bTcrArMG` is an `IsLin` functional of the
forger family, also behind any forger-to-forger wrapper. -/
theorem isLin_bTcrArMG (n : ℕ) {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
    (w : QueryImpl (unifSpec + X')
      (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
    (e : PublicKeyCore prims.core → PK')
    (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core) :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      SM_DT_TCR_AdvantageG ds (bTcrArMG ds optRand pkSeedDist n (wrapFam ds w e g F'))) := by
  unfold SM_DT_TCR_AdvantageG SM_DT_TCR_ExperimentG bTcrArMG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  rw [runG_embed]
  simp only [bind_assoc, liftR_bind]
  trace_state
  sorry

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms bTcrArMG_embed
#print axioms isLin_bTcrArMG
end Axioms
