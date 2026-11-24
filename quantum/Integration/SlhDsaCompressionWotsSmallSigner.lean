import Integration.SlhDsaCompressionWotsSmallNative

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open HiddenWeight (mean)
variable {E : Type} [Fintype E] [DecidableEq E]
variable (rand : Node → Node → ProbComp Node) (seeds : ProbComp Node) (F : PortForger Input Output E)
attribute [local irreducible] wotsChainTargets wotsStepTargetsT

theorem pre_measured_slow (g : CompressionTables) :
    qSM_DT_PRE_Advantage (qrPre (reduced Sha2Set.s128s rand seeds F g)) =
      mean seeds (preValue seeds (wotsChainTargets Sha2Set.s128s.vp) (preSelect Sha2Set.s128s seeds F).choose (preMachine Sha2Set.s128s rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_PRE_Advantage (preGame_eq Sha2Set.s128s rand seeds F g).symm).trans
  apply (qSM_DT_PRE_Advantage_eq_tsum (preAdversary Sha2Set.s128s seeds (preSelect Sha2Set.s128s seeds F) (preMachine Sha2Set.s128s rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := pre_native seeds (wotsChainTargets Sha2Set.s128s.vp) (preSelect Sha2Set.s128s seeds F).choose (preMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128s.vp.params).Thash (shape_slow g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [preAdversary,preNative,preSelect] at h ⊢
  kexact h

theorem tcr_measured_slow (g : CompressionTables) :
    qSM_DT_TCR_Advantage (qrTcrT (reduced Sha2Set.s128s rand seeds F g)) =
      mean seeds (tcrValue seeds (wotsStepTargetsT Sha2Set.s128s.vp) (chainTcrSelect Sha2Set.s128s seeds F).choose (chainTcrMachine Sha2Set.s128s rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_TCR_Advantage (chainTcrGame_eq Sha2Set.s128s rand seeds F g).symm).trans
  apply (qSM_DT_TCR_Advantage_eq_tsum (chainTcrAdversary Sha2Set.s128s seeds (chainTcrSelect Sha2Set.s128s seeds F) (chainTcrMachine Sha2Set.s128s rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := tcr_native seeds (wotsStepTargetsT Sha2Set.s128s.vp) (chainTcrSelect Sha2Set.s128s seeds F).choose (chainTcrMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128s.vp.params).Thash (shape_slow g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [chainTcrAdversary,tcrNative,chainTcrSelect] at h ⊢
  kexact h

theorem ud_real_measured_slow (g : CompressionTables) :
    qSM_DT_UD_RealSuccess (qrUd (reduced Sha2Set.s128s rand seeds F g)) =
      mean seeds (udValue .real seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick (udMachine Sha2Set.s128s rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_UD_RealSuccess (udGame_eq Sha2Set.s128s rand seeds F g).symm).trans
  apply (qSM_DT_UD_RealSuccess_eq_tsum (udAdversary Sha2Set.s128s seeds (udSelect Sha2Set.s128s seeds F) (udMachine Sha2Set.s128s rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := ud_native .real seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick (udMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128s.vp.params).Thash (shape_slow g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [udAdversary,udNative,udSelect] at h ⊢
  kexact h

theorem ud_ideal_measured_slow (g : CompressionTables) :
    qSM_DT_UD_IdealSuccess (qrUd (reduced Sha2Set.s128s rand seeds F g)) =
      mean seeds (udValue .ideal seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick (udMachine Sha2Set.s128s rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_UD_IdealSuccess (udGame_eq Sha2Set.s128s rand seeds F g).symm).trans
  apply (qSM_DT_UD_IdealSuccess_eq_tsum (udAdversary Sha2Set.s128s seeds (udSelect Sha2Set.s128s seeds F) (udMachine Sha2Set.s128s rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := ud_native .ideal seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick (udMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128s.vp.params).Thash (shape_slow g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [udAdversary,udNative,udSelect] at h ⊢
  kexact h

theorem pre_measured_fast (g : CompressionTables) :
    qSM_DT_PRE_Advantage (qrPre (reduced Sha2Set.s128f rand seeds F g)) =
      mean seeds (preValue seeds (wotsChainTargets Sha2Set.s128f.vp) (preSelect Sha2Set.s128f seeds F).choose (preMachine Sha2Set.s128f rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_PRE_Advantage (preGame_eq Sha2Set.s128f rand seeds F g).symm).trans
  apply (qSM_DT_PRE_Advantage_eq_tsum (preAdversary Sha2Set.s128f seeds (preSelect Sha2Set.s128f seeds F) (preMachine Sha2Set.s128f rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := pre_native seeds (wotsChainTargets Sha2Set.s128f.vp) (preSelect Sha2Set.s128f seeds F).choose (preMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128f.vp.params).Thash (shape_fast g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [preAdversary,preNative,preSelect] at h ⊢
  kexact h

theorem tcr_measured_fast (g : CompressionTables) :
    qSM_DT_TCR_Advantage (qrTcrT (reduced Sha2Set.s128f rand seeds F g)) =
      mean seeds (tcrValue seeds (wotsStepTargetsT Sha2Set.s128f.vp) (chainTcrSelect Sha2Set.s128f seeds F).choose (chainTcrMachine Sha2Set.s128f rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_TCR_Advantage (chainTcrGame_eq Sha2Set.s128f rand seeds F g).symm).trans
  apply (qSM_DT_TCR_Advantage_eq_tsum (chainTcrAdversary Sha2Set.s128f seeds (chainTcrSelect Sha2Set.s128f seeds F) (chainTcrMachine Sha2Set.s128f rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := tcr_native seeds (wotsStepTargetsT Sha2Set.s128f.vp) (chainTcrSelect Sha2Set.s128f seeds F).choose (chainTcrMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128f.vp.params).Thash (shape_fast g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [chainTcrAdversary,tcrNative,chainTcrSelect] at h ⊢
  kexact h

theorem ud_real_measured_fast (g : CompressionTables) :
    qSM_DT_UD_RealSuccess (qrUd (reduced Sha2Set.s128f rand seeds F g)) =
      mean seeds (udValue .real seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick (udMachine Sha2Set.s128f rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_UD_RealSuccess (udGame_eq Sha2Set.s128f rand seeds F g).symm).trans
  apply (qSM_DT_UD_RealSuccess_eq_tsum (udAdversary Sha2Set.s128f seeds (udSelect Sha2Set.s128f seeds F) (udMachine Sha2Set.s128f rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := ud_native .real seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick (udMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128f.vp.params).Thash (shape_fast g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [udAdversary,udNative,udSelect] at h ⊢
  kexact h

theorem ud_ideal_measured_fast (g : CompressionTables) :
    qSM_DT_UD_IdealSuccess (qrUd (reduced Sha2Set.s128f rand seeds F g)) =
      mean seeds (udValue .ideal seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick (udMachine Sha2Set.s128f rand F) F.ρ₀ g) := by
  apply (congrArg qSM_DT_UD_IdealSuccess (udGame_eq Sha2Set.s128f rand seeds F g).symm).trans
  apply (qSM_DT_UD_IdealSuccess_eq_tsum (udAdversary Sha2Set.s128f seeds (udSelect Sha2Set.s128f seeds F) (udMachine Sha2Set.s128f rand F) g)).trans
  unfold mean
  apply tsum_congr
  intro pk
  have h := ud_native .ideal seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick (udMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128f.vp.params).Thash (shape_fast g)
  apply congrArg (fun z => PQ.Interactive.prob seeds (· = pk) * z)
  dsimp only [udAdversary,udNative,udSelect] at h ⊢
  kexact h
end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.pre_measured_slow
#print axioms Reduction.Compression.Wots256.ud_ideal_measured_fast
