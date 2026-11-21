import Ideal.Realize.ForsAdv

/-!
# The FORS-leaf adversary equalities (FORS-leaf realisers, part 4)

For every table `g`: the Reduction's FORS-leaf SM-DSPR / SM-TCR adversary built from the
ideal-model forger `S` (SUF wrapper `S.typedS`, EUF wrapper `S.typedE`, table-independent
`opt_rand` sampler `optRandU oR`) IS the instantiation at `g` of the ONE ideal-model adversary
`dsprAdvI S oR pkSeedDist` / `tcrAdvI S oR pkSeedDist` (`dspr_eq_S`, `dspr_eq_E`, `tcr_eq_S`,
`tcr_eq_E`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security TweakableHash

namespace Ideal.Realize.Fors

open Reduction Reduction.Open Reduction.Lazy Reduction.Resources2 Ideal.Realize Ideal.Transport

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option synthInstance.maxHeartbeats 400000

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
  (pkSeedDist : ProbComp (Bytes 16))

theorem choose_eq (g : CF St Blk) :
    ((toDspr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g)))).choose :
      OracleComp (ForsP1Spec P₀) (ForsP1State Link.vp P₀)) =
      simulateQ (instImpl g) (simulateQ embImpl phase1P) := by
  rw [instImpl_emb, phase1P_def]
  exact (toDspr_choose_eq _).trans (forsPhase1_withTH (prims := P₀) (thG g) (hmG g))

theorem choose_eq_tcr (g : CF St Blk) :
    ((toTcr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g)))).choose :
      OracleComp (ForsP1Spec P₀) (ForsP1State Link.vp P₀)) =
      simulateQ (instImpl g) (simulateQ embImpl phase1P) := by
  rw [instImpl_emb, phase1P_def]
  exact (toTcr_choose_eq _).trans (forsPhase1_withTH (prims := P₀) (thG g) (hmG g))

theorem dsprAdv_eta {ι PkSeed Tweak M Y : Type}
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (X : SM_DT_DSPR_SourceFinalValidity.Adversary prob) : X = ⟨X.State, X.choose, X.guess⟩ := rfl

theorem tcrAdv_eta {ι PkSeed Tweak M Y : Type}
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y}
    (X : SM_DT_TCR_SourceFinalValidity.Adversary prob) : X = ⟨X.State, X.choose, X.forge⟩ := rfl

theorem dspr_eq_base (g : CF St Blk) :
    toDspr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g))) =
      instForsDspr (dsprAdvI S oR pkSeedDist) g := by
  refine (dsprAdv_eta _).trans ?_
  unfold instForsDspr dsprAdvI
  refine dsprAdv_mk_congr (σ := ForsP1State Link.vp P₀) ?_ ?_
  · dsimp only
    exact choose_eq S oR pkSeedDist g
  rintro ⟨tbl, tg, ys⟩ pk
  dsimp only
  refine (forsDspr_phase2_open_eq (A₀ S oR pkSeedDist g (thG g) (hmG g)) tbl tg ys pk).trans ?_
  exact phase2_open S oR pkSeedDist g (fun tg z => forsDsprPost tg z) tbl tg ys pk

theorem tcr_eq_base (g : CF St Blk) :
    toTcr (Lazy.bOpenPreS (A₀ S oR pkSeedDist g (thG g) (hmG g))) =
      instFors (tcrAdvI S oR pkSeedDist) g := by
  refine (tcrAdv_eta _).trans ?_
  unfold instFors tcrAdvI
  refine tcrAdv_mk_congr (σ := ForsP1State Link.vp P₀) ?_ ?_
  · dsimp only
    exact choose_eq_tcr S oR pkSeedDist g
  rintro ⟨tbl, tg, ys⟩ pk
  dsimp only
  refine (forsTcr_phase2_open_eq (A₀ S oR pkSeedDist g (thG g) (hmG g)) tbl tg ys pk).trans ?_
  exact phase2_open S oR pkSeedDist g (fun _ z => forsTcrPost z) tbl tg ys pk

/-- **SUF, DSPR: the Reduction's adversary at `g` is the ideal-model adversary at `g`.** -/
theorem dspr_eq_S (g : CF St Blk) :
    toDspr (Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)) =
      instForsDspr (dsprAdvI S oR pkSeedDist) g :=
  (toDspr_S_eq S oR pkSeedDist g).trans (dspr_eq_base S oR pkSeedDist g)

/-- **EUF, DSPR.** -/
theorem dspr_eq_E (g : CF St Blk) :
    toDspr (Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)) =
      instForsDspr (dsprAdvI S oR pkSeedDist) g :=
  (toDspr_E_eq S oR pkSeedDist g).trans (dspr_eq_base S oR pkSeedDist g)

/-- **SUF, FORS TCR.** -/
theorem tcr_eq_S (g : CF St Blk) :
    toTcr (Lazy.bOpenPreS (S.typedS (optRandU oR) pkSeedDist g)) =
      instFors (tcrAdvI S oR pkSeedDist) g :=
  (toTcr_S_eq S oR pkSeedDist g).trans (tcr_eq_base S oR pkSeedDist g)

/-- **EUF, FORS TCR.** -/
theorem tcr_eq_E (g : CF St Blk) :
    toTcr (Lazy.bOpenPreS (S.typedE (optRandU oR) pkSeedDist g)) =
      instFors (tcrAdvI S oR pkSeedDist) g :=
  (toTcr_E_eq S oR pkSeedDist g).trans (tcr_eq_base S oR pkSeedDist g)

end Ideal.Realize.Fors

#print axioms Ideal.Realize.Fors.dspr_eq_S
#print axioms Ideal.Realize.Fors.dspr_eq_E
#print axioms Ideal.Realize.Fors.tcr_eq_S
#print axioms Ideal.Realize.Fors.tcr_eq_E
