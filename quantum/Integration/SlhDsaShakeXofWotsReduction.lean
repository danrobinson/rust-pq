import Integration.SlhDsaShakeXofWotsMachine
import Integration.SlhDsaShakeXofWotsUd
import Integration.SlhDsaShakeXofWotsTcr
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

private noncomputable def actualWotsPreSelect : QSM_DT_PRE_Adversary (Work S N E) (basePre S seeds) where
  State := Open.RState S.vp P₀
  choose := Open.prePhase1 (vp := S.vp) (prims := P₀) seeds
  invert := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem actualWotsPreEq (H : RawTable S N) :
    preAdversary S seeds (actualWotsPreSelect S N seeds F)
      (fun G st pk => (qrPre (internal G)).invert st pk) H = qrPre (internal H) := by
  let real := primitives S (extend H)
  let hf : Open.HashFns P₀ := ⟨real.Thash,real.Hmsg,real.PRF,real.PRFmsg⟩
  have ch : (qrPre (internal H)).choose = (actualWotsPreSelect S N seeds F).choose := by
    kexact Open.wotsPre_phase1_q1_zero (prims := P₀) (pkSeedDist := seeds) hf (internal H).toClassical
  kexact congrArg (fun c => (⟨Open.RState S.vp P₀,c,(qrPre (internal H)).invert,
    F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_PRE_Adversary (Work S N E) (preProblem S seeds H))) ch.symm

theorem actualWotsPre (cap : FitsSingleton S (N := N)) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    SetOracle.uniformMean (fun H => qSM_DT_PRE_Advantage (qrPre (internal H))) ≤
      SetOracle.epsPreSet S (q+qmWotsPreHashes S.vp qs) := by
  simp_rw [← actualWotsPreEq S N rand seeds F]
  apply wots_pre_port S cap seeds
  intro st pk
  obtain ⟨M,hm,he⟩ := ShakeApi.wotsPre_mach_exists S N rand seeds F H₀ st pk q qs hq hs
  exact (funext he) ▸ hm

private noncomputable def actualWotsTcrSelect : QSM_DT_TCR_Adversary (Work S N E) (baseWotsTcr S seeds) where
  State := Open.RState S.vp P₀
  choose := Open.wotsTcrPhase1 (vp := S.vp) (prims := P₀) seeds
  forge := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem actualWotsTcrEq (H : RawTable S N) :
    chainTcrAdversary S seeds (actualWotsTcrSelect S N seeds F)
      (fun G st pk => (qrTcrT (internal G)).forge st pk) H = qrTcrT (internal H) := by
  let real := primitives S (extend H)
  let hf : Open.HashFns P₀ := ⟨real.Thash,real.Hmsg,real.PRF,real.PRFmsg⟩
  have ch : (qrTcrT (internal H)).choose = (actualWotsTcrSelect S N seeds F).choose := by
    kexact Open.wotsTcrT_phase1_q1_zero (prims := P₀) (pkSeedDist := seeds) hf (internal H).toClassical
  kexact congrArg (fun c => (⟨Open.RState S.vp P₀,c,(qrTcrT (internal H)).forge,
    F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_TCR_Adversary (Work S N E) (chainTcrProblem S seeds H))) ch.symm

theorem actualWotsTcr (cap : FitsSingleton S (N := N)) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    SetOracle.uniformMean (fun H => qSM_DT_TCR_Advantage (qrTcrT (internal H))) ≤
      epsTcr S (q+qmWotsTcrTHashes S.vp qs) := by
  simp_rw [← actualWotsTcrEq S N rand seeds F]
  apply wots_chain_tcr_port S cap seeds
  intro st pk
  obtain ⟨M,hm,he⟩ := ShakeApi.wotsTcrT_mach_exists S N rand seeds F H₀ st pk q qs hq hs
  exact (funext he) ▸ hm

private noncomputable def actualWotsUdSelect : QSM_DT_UD_Adversary (Work S N E) (baseUd S seeds) where
  State := Open.RState S.vp P₀
  pick := Open.udPhase1 (vp := S.vp) (prims := P₀) seeds
  distinguish := fun _ _ => pure default
  ρ₀ := F.ρ₀
  posSemidef := F.posSemidef
  trace_eq_one := F.trace_eq_one

private theorem actualWotsUdEq (H : RawTable S N) :
    udAdversary S seeds (actualWotsUdSelect S N seeds F)
      (fun G st pk => (qrUd (internal G)).distinguish st pk) H = qrUd (internal H) := by
  let real := primitives S (extend H)
  let hf : Open.HashFns P₀ := ⟨real.Thash,real.Hmsg,real.PRF,real.PRFmsg⟩
  have ch : (qrUd (internal H)).pick = (actualWotsUdSelect S N seeds F).pick := by
    kexact Open.wotsUd_phase1_q1_zero (prims := P₀) (pkSeedDist := seeds) hf (internal H).toClassical
  kexact congrArg (fun c => (⟨Open.RState S.vp P₀,c,(qrUd (internal H)).distinguish,
    F.ρ₀,F.posSemidef,F.trace_eq_one⟩ : QSM_DT_UD_Adversary (Work S N E) (udProblem S seeds H))) ch.symm

theorem actualWotsUd (cap : FitsSingleton S (N := N)) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    SetOracle.uniformMean (fun H => qSM_DT_UD_RealSuccess (qrUd (internal H))) ≤
      SetOracle.uniformMean (fun H => qSM_DT_UD_IdealSuccess (qrUd (internal H))) +
      SetOracle.epsUdSet S (q+qmWotsUdHashes S.vp qs) := by
  simp_rw [← actualWotsUdEq S N rand seeds F]
  apply wots_ud_port S cap seeds
  intro st pk
  obtain ⟨M,hm,he⟩ := ShakeApi.wotsUd_mach_exists S N rand seeds F H₀ st pk q qs hq hs
  exact (funext he) ▸ hm

end Reduction.ShakeXof
#print axioms Reduction.ShakeXof.actualWotsPre
#print axioms Reduction.ShakeXof.actualWotsTcr
#print axioms Reduction.ShakeXof.actualWotsUd
