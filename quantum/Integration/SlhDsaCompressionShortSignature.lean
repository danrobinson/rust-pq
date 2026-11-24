import Integration.SlhDsaCompressionShortAverage
import Integration.SlhDsaCompressionShortCounts
import Integration.SlhDsaCompressionClassEnd

namespace Reduction.Compression.ShortBlocks
open Ideal SLHDSA MLink OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open HiddenWeight (mean)
open SetOracle (uniformMean)
open Wots256 (Node)
variable {E : Type} [Fintype E] [DecidableEq E]
attribute [local irreducible] arityTargets tcrTargets classFirst tcrProg₁ ClassOne.budget

noncomputable def loss (S : Sha2Set) (L q qs : ℕ) : ℝ≥0∞ :=
  epsTcr S (ClassOne.budget S L q qs) + Wots256.phaseLoss (tcrTargets S.vp) 9

private theorem card : (Fintype.card Node : ℝ≥0∞) = 2^128 := by rw [card_bytes]; norm_num

private theorem measured_slow (rand : Node → Node → ProbComp Node) (seeds : ProbComp Node) (F : PortForger Input Output E)
    (ar : ℕ) (g : CompressionTables) :
    qSM_DT_TCR_Advantage (qbTcrArM ar (reduced Sha2Set.s128s rand seeds F g)) =
      mean seeds (tcrValue seeds (arityTargets Sha2Set.s128s.vp ar) (Open.tcrPhase1 Sha2Set.s128s.vp (randPrims (carrier Sha2Set.s128s)) ar) (ClassOne.classEnd Sha2Set.s128s rand F ar) F.ρ₀ g) := by
  apply (ClassOne.classMean Sha2Set.s128s rand seeds F ar g).trans
  apply congrArg (mean seeds)
  funext pk
  have h := tcr_native seeds (arityTargets Sha2Set.s128s.vp ar) (Open.tcrPhase1 Sha2Set.s128s.vp (randPrims (carrier Sha2Set.s128s)) ar) (ClassOne.classEnd Sha2Set.s128s rand F ar) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128s.vp.params).Thash (Wots256.shape_slow g)
  dsimp only [ClassOne.classActual,tcrNative] at h ⊢
  kexact h

private theorem fixed_slow (rand : Node → Node → ProbComp Node) (seeds : ProbComp Node) (F : PortForger Input Output E)
    (ar : ℕ) (ha : ar ≤ 2) (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced Sha2Set.s128s rand seeds F g))) ≤ loss Sha2Set.s128s c.ml q qs := by
  have hh := class_counts_128s seeds ar ha
  have b := tcr_average ha seeds (arityTargets Sha2Set.s128s.vp ar) (Open.tcrPhase1 Sha2Set.s128s.vp (randPrims (carrier Sha2Set.s128s)) ar) (ClassOne.classEnd Sha2Set.s128s rand F ar) F.ρ₀ F.posSemidef F.trace_eq_one (tcrTargets Sha2Set.s128s.vp) 9 (ClassOne.budget Sha2Set.s128s c.ml q qs)
    (ClassOne.class_cost Sha2Set.s128s rand F ar c q qs hq hs hc) (by kexact hh.1) (by kexact hh.2.1) (by kexact hh.2.2)
  simp_rw [measured_slow rand seeds F ar]
  unfold loss epsTcr
  simpa only [card,show 8*Sha2Set.s128s.vp.params.n = 128 from rfl] using b

private theorem measured_fast (rand : Node → Node → ProbComp Node) (seeds : ProbComp Node) (F : PortForger Input Output E)
    (ar : ℕ) (g : CompressionTables) :
    qSM_DT_TCR_Advantage (qbTcrArM ar (reduced Sha2Set.s128f rand seeds F g)) =
      mean seeds (tcrValue seeds (arityTargets Sha2Set.s128f.vp ar) (Open.tcrPhase1 Sha2Set.s128f.vp (randPrims (carrier Sha2Set.s128f)) ar) (ClassOne.classEnd Sha2Set.s128f rand F ar) F.ρ₀ g) := by
  apply (ClassOne.classMean Sha2Set.s128f rand seeds F ar g).trans
  apply congrArg (mean seeds)
  funext pk
  have h := tcr_native seeds (arityTargets Sha2Set.s128f.vp ar) (Open.tcrPhase1 Sha2Set.s128f.vp (randPrims (carrier Sha2Set.s128f)) ar) (ClassOne.classEnd Sha2Set.s128f rand F ar) F.ρ₀ F.posSemidef F.trace_eq_one g pk
    (tablePrimitives g Sha2Set.s128f.vp.params).Thash (Wots256.shape_fast g)
  dsimp only [ClassOne.classActual,tcrNative] at h ⊢
  kexact h

private theorem fixed_fast (rand : Node → Node → ProbComp Node) (seeds : ProbComp Node) (F : PortForger Input Output E)
    (ar : ℕ) (ha : ar ≤ 2) (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced Sha2Set.s128f rand seeds F g))) ≤ loss Sha2Set.s128f c.ml q qs := by
  have hh := class_counts_128f seeds ar ha
  have b := tcr_average ha seeds (arityTargets Sha2Set.s128f.vp ar) (Open.tcrPhase1 Sha2Set.s128f.vp (randPrims (carrier Sha2Set.s128f)) ar) (ClassOne.classEnd Sha2Set.s128f rand F ar) F.ρ₀ F.posSemidef F.trace_eq_one (tcrTargets Sha2Set.s128f.vp) 9 (ClassOne.budget Sha2Set.s128f c.ml q qs)
    (ClassOne.class_cost Sha2Set.s128f rand F ar c q qs hq hs hc) (by kexact hh.1) (by kexact hh.2.1) (by kexact hh.2.2)
  simp_rw [measured_fast rand seeds F ar]
  unfold loss epsTcr
  simpa only [card,show 8*Sha2Set.s128f.vp.params.n = 128 from rfl] using b

/-- Shared compression security of all short-input class-TCR games in the two 128-bit signatures. -/
theorem class_tcr_le (S : Sha2Set) (hn : S.vp.params.n = 16)
    (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)
    (ar : ℕ) (ha : ar ≤ 2) (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g))) ≤ loss S c.ml q qs := by
  cases S <;> try contradiction
  · exact fixed_slow rand seeds F ar ha c q qs hq hs hc
  · exact fixed_fast rand seeds F ar ha c q qs hq hs hc

end Reduction.Compression.ShortBlocks
#print axioms Reduction.Compression.ShortBlocks.class_tcr_le
