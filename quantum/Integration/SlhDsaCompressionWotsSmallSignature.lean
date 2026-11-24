import Integration.SlhDsaCompressionWotsSmallFixed
import Integration.SlhDsaCompressionWotsSmallCounts
namespace Reduction.Compression.Wots256
open Ideal SLHDSA MLink OracleComp OracleSpec PQ.Interactive Quantum ENNReal Resources2
open SetOracle (uniformMean)
set_option maxRecDepth 2000
attribute [local irreducible] preFirst tcrFirst preProg₁ tcrProg₁ wotsChainTargets wotsStepTargetsT chooseBudget
variable {E : Type} [Fintype E] [DecidableEq E]
variable (S : Sha2Set) (hn : S.vp.params.n = 16)
variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)
include hn in
theorem pre_signature (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_PRE_Advantage (qrPre (reduced S rand seeds F g))) ≤
      SetOracle.epsPreSet S (wotsBudget S c.ml q qs (wotsPreHashes S.vp)) + phaseLoss (chooseBudget S) 9 := by
  cases S <;> try contradiction
  case s128s =>
    have hh := pre_counts_128s seeds F
    exact pre_fixed_slow rand seeds F c q qs _ 9 hq hs hc (by kexact hh.1) (by kexact hh.2.1) (by kexact hh.2.2)
  case s128f =>
    have hh := pre_counts_128f seeds F
    exact pre_fixed_fast rand seeds F c q qs _ 9 hq hs hc (by kexact hh.1) (by kexact hh.2.1) (by kexact hh.2.2)
include hn in
theorem tcr_signature (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qrTcrT (reduced S rand seeds F g))) ≤
      epsTcr S (wotsBudget S c.ml q qs (wotsTcrHashes S.vp)) + phaseLoss (chooseBudget S) 9 := by
  cases S <;> try contradiction
  case s128s =>
    have hh := tcr_counts_128s seeds F
    exact tcr_fixed_slow rand seeds F c q qs _ 9 hq hs hc (by kexact hh.1) (by kexact hh.2.1) (by kexact hh.2.2)
  case s128f =>
    have hh := tcr_counts_128f seeds F
    exact tcr_fixed_fast rand seeds F c q qs _ 9 hq hs hc (by kexact hh.1) (by kexact hh.2.1) (by kexact hh.2.2)
include hn in
theorem ud_signature (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_UD_RealSuccess (qrUd (reduced S rand seeds F g))) - uniformMean (fun g => qSM_DT_UD_IdealSuccess (qrUd (reduced S rand seeds F g))) ≤
      SetOracle.epsUdSet S (wotsBudget S c.ml q qs (wotsWinHashes S.vp)) + 2*phaseLoss (chooseBudget S) 9 := by
  cases S <;> try contradiction
  case s128s =>
    have hh := ud_counts_128s seeds F
    exact ud_fixed_slow rand seeds F c q qs _ 9 hq hs hc (fun w => (hh w).1) (fun w => (hh w).2.1) (fun w => (hh w).2.2)
  case s128f =>
    have hh := ud_counts_128f seeds F
    exact ud_fixed_fast rand seeds F c q qs _ 9 hq hs hc (fun w => (hh w).1) (fun w => (hh w).2.1) (fun w => (hh w).2.2)
end Reduction.Compression.Wots256
#print axioms Reduction.Compression.Wots256.pre_signature
#print axioms Reduction.Compression.Wots256.tcr_signature
#print axioms Reduction.Compression.Wots256.ud_signature
