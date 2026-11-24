import Integration.SlhDsaShakeXofForsMachine
import Integration.SlhDsaShakeXofDspr
import Integration.SlhDsaShakeXofArityReduction

namespace Reduction.ShakeXof
open MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal TweakableHash ShakeApi
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] wotsChainTargets wotsStepTargetsT openPreTargets
variable (S : Sha2Set) (N : ℕ) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
  {E : Type} [Fintype E] [DecidableEq E] (F : PortForger (ShakeApi.Input N) (Bytes S.vp.params.m) E)
local notation "H₀" => zeroTable S N
local notation "P₀" => primitives S (extend H₀)
local notation "internal" => rawInternal S N rand seeds F

private noncomputable def actualForsTcrSelect : QTcrFV_Adversary (Work S N E) (baseProblem S seeds) where
  State := Open.ForsP1State S.vp P₀
  choose := Open.forsPhase1 S.vp P₀
  forge := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem actualForsTcrEq (H : RawTable S N) :
    forsAdversary S seeds (actualForsTcrSelect S N seeds F)
      (fun G st pk => (qToTcr (internal G)).forge st pk) H = qToTcr (internal H) := by
  have ch : (qToTcr (internal H)).choose = (actualForsTcrSelect S N seeds F).choose := by
    refine (Open.toTcr_choose_eq (internal H).toClassical).trans ?_
    qm_kernel_rfl
  kexact congrArg (fun c => (⟨Open.ForsP1State S.vp P₀,c,(qToTcr (internal H)).forge,
    F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QTcrFV_Adversary (Work S N E) (forsProblem S H seeds))) ch.symm

theorem actualForsTcr (cap : FitsSingleton S (N := N)) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    SetOracle.uniformMean (fun H => qTcrFV_Advantage (qToTcr (internal H))) ≤
      (2*((q+forsMHashes S.vp qs:ℕ):ℝ≥0∞)+1)^2 / 2^(8*S.vp.params.n) := by
  simp_rw [← actualForsTcrEq S N rand seeds F]
  apply fors_tcr_port S cap seeds
  intro st pk
  obtain ⟨M,hm,he⟩ := ShakeApi.fors_tcr_mach_exists S N rand seeds F H₀ st pk q qs hq hs
  exact (funext he) ▸ hm

private noncomputable def actualForsDsprSelect : QDsprFV_Adversary (Work S N E) (SM_DT_DSPR_SourceFinalValidity.Problem.standalone (baseProblem S seeds).th (openPreTargets S.vp)) where
  State := Open.ForsP1State S.vp P₀
  choose := Open.forsPhase1 S.vp P₀
  guess := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem actualForsDsprEq (H : RawTable S N) :
    dsprAdversary S seeds (actualForsDsprSelect S N seeds F)
      (fun G st pk => (qToDspr (internal G)).guess st pk) H = qToDspr (internal H) := by
  have ch : (qToDspr (internal H)).choose = (actualForsDsprSelect S N seeds F).choose := by
    refine (Open.toDspr_choose_eq (internal H).toClassical).trans ?_
    qm_kernel_rfl
  kexact congrArg (fun c => (⟨Open.ForsP1State S.vp P₀,c,(qToDspr (internal H)).guess,
    F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QDsprFV_Adversary (Work S N E) (dsprProblem S H seeds))) ch.symm

theorem actualForsDspr (cap : FitsSingleton S (N := N)) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    SetOracle.uniformMean (fun H => qDsprFV_Success (qToDspr (internal H))) ≤
      SetOracle.uniformMean (fun H => qDsprFV_SPProbability (qToDspr (internal H))) +
      ENNReal.ofReal (168*((q+forsMHashes S.vp qs:ℕ):ℝ)^2 / 2^(8*S.vp.params.n)) := by
  simp_rw [← actualForsDsprEq S N rand seeds F]
  apply fors_dspr_port S cap seeds
  intro st pk
  obtain ⟨M,hm,he⟩ := ShakeApi.fors_dspr_mach_exists S N rand seeds F H₀ st pk q qs hq hs
  exact (funext he) ▸ hm

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.actualForsTcr
#print axioms Reduction.ShakeXof.actualForsDspr
