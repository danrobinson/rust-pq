import Reduction.Gen.Forger
import Reduction.Gen.GameWots
import Reduction.Lazy.WotsSparse
import Reduction.WotsUD

/-!
# The WOTS-game reduction adversaries around a general-spec forger

`rUdG`, `rPreG`, `rTcrTG` are `rUd pkSeedDist (Lazy.bWotsS ·)`, `rPre pkSeedDist (Lazy.bWotsS ·)`,
`rTcrT pkSeedDist (Lazy.bWotsS ·)` around a general-spec forger family.  Their first phases are
the classical ones (they do not depend on the forger), embedded; their second phases are the
classical post-processing around `bWotsForgeG`, the forge phase of `Lazy.bWotsS ·` with the
forger run through `g2RunWithG`.

* naturality: `rUdG_embed`, `rPreG_embed`, `rTcrTG_embed`;
* linearity behind any forger-to-forger wrapper: `isLin_rUdG_real`, `isLin_rUdG_ideal`,
  `isLin_rPreG`, `isLin_rTcrTG`;
* values on classical forgers: `udRealG_rUdG_embed`, `udIdealG_rUdG_embed`, `preAdvG_rPreG_embed`,
  `tcrAdvG_rTcrTG_embed`.
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

variable (vp prims) in
/-- The state of `Lazy.bWotsS ·` (table, signing history, root), written out. -/
abbrev WSt : Type := SecretTable vp prims × List (WotsGame.Entry prims) × prims.Y

/-- The forge phase of `Lazy.bWotsS ·` around a general-spec forger. -/
noncomputable def bWotsForgeG (F : GFam ds vp prims) (st : WSt vp prims) (pkSeed : prims.PkSeed) :
    OracleComp (gSpec ds) (ℕ × prims.Y × WotsSig vp.params prims.core) :=
  g2RunWithG ds optRand F ⟨pkSeed, st.2.2⟩ (signFromHist st.1 st.2.1 ⟨pkSeed, st.2.2⟩) >>= fun z ↦
    pure (wotsAnswer st.1 st.2.1 ⟨pkSeed, st.2.2⟩ z.1.1 z.1.2)

variable {optRand pkSeedDist} in
/-- On a classical forger, `bWotsForgeG` is the forge phase of `Lazy.bWotsS`. -/
theorem bWotsForgeG_embed (A : Forger vp prims optRand pkSeedDist) (st : WSt vp prims)
    (pkSeed : prims.PkSeed) :
    bWotsForgeG ds optRand (fun pk ↦ embed ds (A.main pk)) st pkSeed =
      liftR ds ((Lazy.bWotsS A).forge st pkSeed) := by
  unfold bWotsForgeG
  rw [g2RunWithG_embed]
  simp only [Lazy.bWotsS, Lazy.bWotsWith, liftR_bind, liftR_pure]

/-! ## SM-UD -/

/-- Phase 1 of `rUd pkSeedDist (Lazy.bWotsS ·)` (it does not depend on the forger). -/
noncomputable def udPickW :
    OracleComp (UdSpec (vp := vp) (prims := prims) pkSeedDist)
      (WSt vp prims × List (WotsGame.Entry prims)) :=
  (rUd pkSeedDist
    (Lazy.bWotsS (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)))).pick

/-- **`rUd pkSeedDist (Lazy.bWotsS ·)` around a general-spec forger.** -/
noncomputable def rUdG (F : GFam ds vp prims) :
    SM_DT_UD_AdversaryG ds (wotsUdProblem vp prims pkSeedDist) where
  State := WSt vp prims × List (WotsGame.Entry prims)
  pick := embed ds (udPickW optRand pkSeedDist)
  distinguish st pk :=
    bWotsForgeG ds optRand F st.1 pk >>= fun x ↦ pure (WotsGame.win pk st.2 x.1 x.2.1 x.2.2)

/-! ## SM-PRE -/

/-- Phase 1 of `rPre pkSeedDist (Lazy.bWotsS ·)`. -/
noncomputable def preChooseW :
    OracleComp (PreSpec (vp := vp) (prims := prims) pkSeedDist)
      (WSt vp prims × List (WotsGame.Entry prims)) :=
  (rPre pkSeedDist
    (Lazy.bWotsS (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)))).choose

/-- **`rPre pkSeedDist (Lazy.bWotsS ·)` around a general-spec forger.** -/
noncomputable def rPreG (F : GFam ds vp prims) :
    SM_DT_PRE_AdversaryG ds (wotsPreProblem vp prims pkSeedDist) where
  State := WSt vp prims × List (WotsGame.Entry prims)
  choose := embed ds (preChooseW optRand pkSeedDist)
  invert st pk :=
    bWotsForgeG ds optRand F st.1 pk >>= fun x ↦ pure (preAnswer pk st.2 x.1 x.2.1 x.2.2)

/-! ## SM-TCR (tight cap) -/

/-- Phase 1 of `rTcrT pkSeedDist (Lazy.bWotsS ·)`. -/
noncomputable def tcrChooseW :
    OracleComp (unifSpec + (SM_DT_TCR_challengeSpec prims.AdrsKey prims.Y prims.Y +
        collectionSpec (wotsTcrProblemT vp prims pkSeedDist).thColl))
      (WSt vp prims × List (WotsGame.Entry prims)) :=
  (rTcrT pkSeedDist
    (Lazy.bWotsS (dummyForger (optRand := optRand) (pkSeedDist := pkSeedDist)))).choose

/-- **`rTcrT pkSeedDist (Lazy.bWotsS ·)` around a general-spec forger.** -/
noncomputable def rTcrTG (F : GFam ds vp prims) :
    SM_DT_TCR_AdversaryG ds (wotsTcrProblemT vp prims pkSeedDist) where
  State := WSt vp prims × List (WotsGame.Entry prims)
  choose := embed ds (tcrChooseW optRand pkSeedDist)
  forge st pk :=
    bWotsForgeG ds optRand F st.1 pk >>= fun x ↦ pure (tcrAnswer pk st.2 x.1 x.2.1 x.2.2)

variable {optRand pkSeedDist}

/-! ## Naturality -/

/-- **Naturality.** On a classical forger, `rUdG` is `rUd pkSeedDist (Lazy.bWotsS A)`. -/
theorem rUdG_embed (A : Forger vp prims optRand pkSeedDist) :
    rUdG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      SM_DT_UD_AdversaryG.ofClassical ds (rUd pkSeedDist (Lazy.bWotsS A)) := by
  unfold rUdG SM_DT_UD_AdversaryG.ofClassical
  congr 1
  funext st pk
  simp only [bWotsForgeG_embed, rUd, liftR_bind, liftR_pure]

/-- **Naturality.** On a classical forger, `rPreG` is `rPre pkSeedDist (Lazy.bWotsS A)`. -/
theorem rPreG_embed (A : Forger vp prims optRand pkSeedDist) :
    rPreG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      SM_DT_PRE_AdversaryG.ofClassical ds (rPre pkSeedDist (Lazy.bWotsS A)) := by
  unfold rPreG SM_DT_PRE_AdversaryG.ofClassical
  congr 1
  funext st pk
  simp only [bWotsForgeG_embed, rPre, liftR_bind, liftR_pure]

/-- **Naturality.** On a classical forger, `rTcrTG` is `rTcrT pkSeedDist (Lazy.bWotsS A)`. -/
theorem rTcrTG_embed (A : Forger vp prims optRand pkSeedDist) :
    rTcrTG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk)) =
      SM_DT_TCR_AdversaryG.ofClassical ds (rTcrT pkSeedDist (Lazy.bWotsS A)) := by
  unfold rTcrTG SM_DT_TCR_AdversaryG.ofClassical
  congr 1
  funext st pk
  simp only [bWotsForgeG_embed, rTcrT_forge, rTcr, liftR_bind, liftR_pure]

/-! ## Linearity -/

section Lin

variable {ιx' : Type} {X' : OracleSpec ιx'} {PK' α' : Type}
  (w' : QueryImpl (unifSpec + X')
    (OracleComp (unifSpec + (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))))
  (e : PublicKeyCore prims.core → PK')
  (g : α' → List Byte × GeneralScheme.SignatureCore vp prims.core)

/-- **Linearity**, real-world success of `rUdG`. -/
theorem isLin_rUdG_real :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      SM_DT_UD_RealSuccessG ds (rUdG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold SM_DT_UD_RealSuccessG SM_DT_UD_ExperimentG rUdG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  simp only [runG_embed, bWotsForgeG, g2RunWithG, runG_wrapFam, bind_assoc, bind_map_left,
    pure_bind]
  refine isLin_liftR_bind ds _ _ fun r ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity**, ideal-world success of `rUdG`. -/
theorem isLin_rUdG_ideal :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      SM_DT_UD_IdealSuccessG ds (rUdG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold SM_DT_UD_IdealSuccessG SM_DT_UD_ExperimentG rUdG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  simp only [runG_embed, bWotsForgeG, g2RunWithG, runG_wrapFam, bind_assoc, bind_map_left,
    pure_bind]
  refine isLin_liftR_bind ds _ _ fun r ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity**, SM-PRE advantage of `rPreG`. -/
theorem isLin_rPreG :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      SM_DT_PRE_AdvantageG ds (rPreG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold SM_DT_PRE_AdvantageG SM_DT_PRE_ExperimentG rPreG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  simp only [runG_embed, bWotsForgeG, g2RunWithG, runG_wrapFam, bind_assoc, bind_map_left,
    pure_bind]
  refine isLin_liftR_bind ds _ _ fun r ↦ ?_
  exact isLin_run_pure ds _ _ _ _

/-- **Linearity**, SM-TCR advantage of `rTcrTG`. -/
theorem isLin_rTcrTG :
    IsLin ds (wOf ds) 1 (fun F' : PK' → OracleComp ((ds + unifSpec) + X') α' ↦
      SM_DT_TCR_AdvantageG ds (rTcrTG ds optRand pkSeedDist (wrapFam ds w' e g F'))) := by
  unfold SM_DT_TCR_AdvantageG SM_DT_TCR_ExperimentG rTcrTG
  dsimp only
  refine isLin_liftR_bind ds _ _ fun pk ↦ ?_
  simp only [runG_embed, bWotsForgeG, g2RunWithG, runG_wrapFam, bind_assoc, bind_map_left,
    pure_bind]
  refine isLin_liftR_bind ds _ _ fun r ↦ ?_
  exact isLin_run_pure ds _ _ _ _

end Lin

/-! ## Values on classical forgers: the terms of the linear headline -/

theorem udRealG_rUdG_embed (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_UD_RealSuccessG ds (rUdG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_UD_RealSuccess (rUd pkSeedDist (Lazy.bWotsS A)) := by
  rw [rUdG_embed, SM_DT_UD_RealSuccessG_ofClassical]

theorem udIdealG_rUdG_embed (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_UD_IdealSuccessG ds (rUdG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_UD_IdealSuccess (rUd pkSeedDist (Lazy.bWotsS A)) := by
  rw [rUdG_embed, SM_DT_UD_IdealSuccessG_ofClassical]

theorem preAdvG_rPreG_embed (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_PRE_AdvantageG ds (rPreG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_PRE_Advantage (rPre pkSeedDist (Lazy.bWotsS A)) := by
  rw [rPreG_embed, SM_DT_PRE_AdvantageG_ofClassical]

theorem tcrAdvG_rTcrTG_embed (A : Forger vp prims optRand pkSeedDist) :
    SM_DT_TCR_AdvantageG ds (rTcrTG ds optRand pkSeedDist (fun pk ↦ embed ds (A.main pk))) =
      SM_DT_TCR_Advantage (rTcrT pkSeedDist (Lazy.bWotsS A)) := by
  rw [rTcrTG_embed, SM_DT_TCR_AdvantageG_ofClassical]

end Reduction.Gen

section Axioms
open Reduction.Gen
#print axioms rUdG_embed
#print axioms rPreG_embed
#print axioms rTcrTG_embed
#print axioms isLin_rUdG_real
#print axioms isLin_rUdG_ideal
#print axioms isLin_rPreG
#print axioms isLin_rTcrTG
#print axioms udRealG_rUdG_embed
#print axioms udIdealG_rUdG_embed
#print axioms preAdvG_rPreG_embed
#print axioms tcrAdvG_rTcrTG_embed
end Axioms
