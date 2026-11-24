import Integration.SlhDsaCompressionWotsSmallSigner

namespace Reduction.Compression.Wots256
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open Resources2
open HiddenWeight (mean)
open SetOracle (uniformMean)
variable {E : Type} [Fintype E] [DecidableEq E]
variable (rand : Node → Node → ProbComp Node) (seeds : ProbComp Node) (F : PortForger Input Output E)
attribute [local irreducible] wotsChainTargets wotsStepTargetsT wotsBudget preFirst tcrFirst preProg₁ tcrProg₁
set_option maxRecDepth 2000

private theorem node_card : (Fintype.card Node : ℝ≥0∞) = 2^128 := by rw [card_bytes]; norm_num
private theorem cardReal : (Fintype.card Node : ℝ) = 2^128 := by rw [card_bytes]; norm_num

theorem pre_fixed_slow (c : Caps) (q qs C L : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (h0 : IsQueryBoundP (preProg₁ id (preFirst seeds (wotsChainTargets Sha2Set.s128s.vp) (preSelect Sha2Set.s128s seeds F).choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (preProg₁ id (preFirst seeds (wotsChainTargets Sha2Set.s128s.vp) (preSelect Sha2Set.s128s seeds F).choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (preProg₁ id (preFirst seeds (wotsChainTargets Sha2Set.s128s.vp) (preSelect Sha2Set.s128s seeds F).choose)) (chainLenLe L)) :
    uniformMean (fun g => qSM_DT_PRE_Advantage (qrPre (reduced Sha2Set.s128s rand seeds F g))) ≤ SetOracle.epsPreSet Sha2Set.s128s (wotsBudget Sha2Set.s128s c.ml q qs (wotsPreHashes Sha2Set.s128s.vp)) + phaseLoss C L := by
  have b := pre_average seeds (wotsChainTargets Sha2Set.s128s.vp) (preSelect Sha2Set.s128s seeds F).choose (preMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one C L (wotsBudget Sha2Set.s128s c.ml q qs (wotsPreHashes Sha2Set.s128s.vp))
    (preMachine_budget Sha2Set.s128s rand F c q qs hq hs hc) (by kexact h0) (by kexact hC) (by kexact hL)
  simp_rw [pre_measured_slow rand seeds F]
  unfold SetOracle.epsPreSet
  simpa only [node_card,cardReal,show 8*Sha2Set.s128s.vp.params.n = 128 from rfl] using b

theorem tcr_fixed_slow (c : Caps) (q qs C L : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (h0 : IsQueryBoundP (tcrProg₁ (tcrFirst seeds (wotsStepTargetsT Sha2Set.s128s.vp) (chainTcrSelect Sha2Set.s128s seeds F).choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (tcrProg₁ (tcrFirst seeds (wotsStepTargetsT Sha2Set.s128s.vp) (chainTcrSelect Sha2Set.s128s seeds F).choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (tcrProg₁ (tcrFirst seeds (wotsStepTargetsT Sha2Set.s128s.vp) (chainTcrSelect Sha2Set.s128s seeds F).choose)) (chainLenLe L)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qrTcrT (reduced Sha2Set.s128s rand seeds F g))) ≤ epsTcr Sha2Set.s128s (wotsBudget Sha2Set.s128s c.ml q qs (wotsTcrHashes Sha2Set.s128s.vp)) + phaseLoss C L := by
  have b := tcr_average seeds (wotsStepTargetsT Sha2Set.s128s.vp) (chainTcrSelect Sha2Set.s128s seeds F).choose (chainTcrMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one C L (wotsBudget Sha2Set.s128s c.ml q qs (wotsTcrHashes Sha2Set.s128s.vp))
    (chainTcrMachine_budget Sha2Set.s128s rand F c q qs hq hs hc) (by kexact h0) (by kexact hC) (by kexact hL)
  simp_rw [tcr_measured_slow rand seeds F]
  unfold epsTcr
  simpa only [node_card,cardReal,show 8*Sha2Set.s128s.vp.params.n = 128 from rfl] using b

theorem ud_fixed_slow (c : Caps) (q qs C L : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (h0 : ∀ world, IsQueryBoundP (udProg₁ world id (udFirst seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick)) (fun i => isPub i = true) 0)
    (hC : ∀ world, IsQueryBoundP (udProg₁ world id (udFirst seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick)) (fun i => isChain i = true) C)
    (hL : ∀ world, AllQueriesSatisfy (udProg₁ world id (udFirst seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick)) (chainLenLe L)) :
    uniformMean (fun g => qSM_DT_UD_RealSuccess (qrUd (reduced Sha2Set.s128s rand seeds F g))) -
    uniformMean (fun g => qSM_DT_UD_IdealSuccess (qrUd (reduced Sha2Set.s128s rand seeds F g))) ≤ SetOracle.epsUdSet Sha2Set.s128s (wotsBudget Sha2Set.s128s c.ml q qs (wotsWinHashes Sha2Set.s128s.vp)) + 2*phaseLoss C L := by
  have b := ud_average seeds (wotsChainTargets Sha2Set.s128s.vp) (udSelect Sha2Set.s128s seeds F).pick (udMachine Sha2Set.s128s rand F) F.ρ₀ F.posSemidef F.trace_eq_one C L (wotsBudget Sha2Set.s128s c.ml q qs (wotsWinHashes Sha2Set.s128s.vp))
    (udMachine_budget Sha2Set.s128s rand F c q qs hq hs hc) (by kexact h0) (by kexact hC) (by kexact hL)
  apply tsub_le_iff_right.mpr
  rw [add_comm]
  simp_rw [ud_real_measured_slow rand seeds F,ud_ideal_measured_slow rand seeds F]
  unfold SetOracle.epsUdSet
  simpa only [node_card,cardReal,show 8*Sha2Set.s128s.vp.params.n = 128 from rfl] using b

theorem pre_fixed_fast (c : Caps) (q qs C L : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (h0 : IsQueryBoundP (preProg₁ id (preFirst seeds (wotsChainTargets Sha2Set.s128f.vp) (preSelect Sha2Set.s128f seeds F).choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (preProg₁ id (preFirst seeds (wotsChainTargets Sha2Set.s128f.vp) (preSelect Sha2Set.s128f seeds F).choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (preProg₁ id (preFirst seeds (wotsChainTargets Sha2Set.s128f.vp) (preSelect Sha2Set.s128f seeds F).choose)) (chainLenLe L)) :
    uniformMean (fun g => qSM_DT_PRE_Advantage (qrPre (reduced Sha2Set.s128f rand seeds F g))) ≤ SetOracle.epsPreSet Sha2Set.s128f (wotsBudget Sha2Set.s128f c.ml q qs (wotsPreHashes Sha2Set.s128f.vp)) + phaseLoss C L := by
  have b := pre_average seeds (wotsChainTargets Sha2Set.s128f.vp) (preSelect Sha2Set.s128f seeds F).choose (preMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one C L (wotsBudget Sha2Set.s128f c.ml q qs (wotsPreHashes Sha2Set.s128f.vp))
    (preMachine_budget Sha2Set.s128f rand F c q qs hq hs hc) (by kexact h0) (by kexact hC) (by kexact hL)
  simp_rw [pre_measured_fast rand seeds F]
  unfold SetOracle.epsPreSet
  simpa only [node_card,cardReal,show 8*Sha2Set.s128f.vp.params.n = 128 from rfl] using b

theorem tcr_fixed_fast (c : Caps) (q qs C L : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (h0 : IsQueryBoundP (tcrProg₁ (tcrFirst seeds (wotsStepTargetsT Sha2Set.s128f.vp) (chainTcrSelect Sha2Set.s128f seeds F).choose)) (fun i => isPub i = true) 0)
    (hC : IsQueryBoundP (tcrProg₁ (tcrFirst seeds (wotsStepTargetsT Sha2Set.s128f.vp) (chainTcrSelect Sha2Set.s128f seeds F).choose)) (fun i => isChain i = true) C)
    (hL : AllQueriesSatisfy (tcrProg₁ (tcrFirst seeds (wotsStepTargetsT Sha2Set.s128f.vp) (chainTcrSelect Sha2Set.s128f seeds F).choose)) (chainLenLe L)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qrTcrT (reduced Sha2Set.s128f rand seeds F g))) ≤ epsTcr Sha2Set.s128f (wotsBudget Sha2Set.s128f c.ml q qs (wotsTcrHashes Sha2Set.s128f.vp)) + phaseLoss C L := by
  have b := tcr_average seeds (wotsStepTargetsT Sha2Set.s128f.vp) (chainTcrSelect Sha2Set.s128f seeds F).choose (chainTcrMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one C L (wotsBudget Sha2Set.s128f c.ml q qs (wotsTcrHashes Sha2Set.s128f.vp))
    (chainTcrMachine_budget Sha2Set.s128f rand F c q qs hq hs hc) (by kexact h0) (by kexact hC) (by kexact hL)
  simp_rw [tcr_measured_fast rand seeds F]
  unfold epsTcr
  simpa only [node_card,cardReal,show 8*Sha2Set.s128f.vp.params.n = 128 from rfl] using b

theorem ud_fixed_fast (c : Caps) (q qs C L : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (h0 : ∀ world, IsQueryBoundP (udProg₁ world id (udFirst seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick)) (fun i => isPub i = true) 0)
    (hC : ∀ world, IsQueryBoundP (udProg₁ world id (udFirst seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick)) (fun i => isChain i = true) C)
    (hL : ∀ world, AllQueriesSatisfy (udProg₁ world id (udFirst seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick)) (chainLenLe L)) :
    uniformMean (fun g => qSM_DT_UD_RealSuccess (qrUd (reduced Sha2Set.s128f rand seeds F g))) -
    uniformMean (fun g => qSM_DT_UD_IdealSuccess (qrUd (reduced Sha2Set.s128f rand seeds F g))) ≤ SetOracle.epsUdSet Sha2Set.s128f (wotsBudget Sha2Set.s128f c.ml q qs (wotsWinHashes Sha2Set.s128f.vp)) + 2*phaseLoss C L := by
  have b := ud_average seeds (wotsChainTargets Sha2Set.s128f.vp) (udSelect Sha2Set.s128f seeds F).pick (udMachine Sha2Set.s128f rand F) F.ρ₀ F.posSemidef F.trace_eq_one C L (wotsBudget Sha2Set.s128f c.ml q qs (wotsWinHashes Sha2Set.s128f.vp))
    (udMachine_budget Sha2Set.s128f rand F c q qs hq hs hc) (by kexact h0) (by kexact hC) (by kexact hL)
  apply tsub_le_iff_right.mpr
  rw [add_comm]
  simp_rw [ud_real_measured_fast rand seeds F,ud_ideal_measured_fast rand seeds F]
  unfold SetOracle.epsUdSet
  simpa only [node_card,cardReal,show 8*Sha2Set.s128f.vp.params.n = 128 from rfl] using b
end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.ud_fixed_slow
#print axioms Reduction.Compression.Wots256.pre_fixed_fast
