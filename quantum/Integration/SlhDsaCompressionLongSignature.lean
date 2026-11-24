import Integration.SlhDsaCompressionLongConditional
import Integration.SlhDsaCompressionLongPhase
import Integration.SlhDsaCompressionLongCertificate
import Integration.SlhDsaCompressionSmallSingle
namespace Reduction.Compression.LongSignature
open Ideal Ideal.HP SLHDSA MLink TweakableHash OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal
open HiddenWeight (mean)
open Wots256 (Node)
open LongClass
open scoped ComplexOrder
variable {σ E : Type} [Fintype E] [DecidableEq E]
local notation "W" => WS Input Output E

private theorem score (seeds : ProbComp Node) (ar n : ℕ) (pk : Node) (cv : St)
    (c : Cell St Blk → Option St) (U : CF St Blk) (V : Blk → St) (b : CF Chain512 Block512)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × ShortBlocks.Msg ar))
    (ρ : Matrix W W ℂ) (x : ShortBlocks.TraceTcr σ ar) :
    let g := Certificate.normalized IV128 (sb128 pk) cv c U V
    ShortBlocks.tcrScore pk (g,b) M ρ x = qWeight
      (fun jm => (Certificate.report seeds ar n pk cv c U V x.2.1 jm).1 = true)
      (M (oracle (g,b)) x.1 pk) ρ := by
  dsimp only
  unfold ShortBlocks.tcrScore
  let flag := fun jm => (Certificate.report seeds ar n pk cv c U V x.2.1 jm).1
  let prog := M (oracle (Certificate.normalized IV128 (sb128 pk) cv c U V,b)) x.1 pk
  calc _ = qWeight (· = true) (flag <$> prog) ρ := by
             apply congrArg (fun Z => qWeight (· = true) Z ρ)
             rw [map_eq_bind_pure_comp]
             apply congrArg (fun k => prog >>= k)
             funext jm
             unfold flag Certificate.report
             dsimp only [Function.comp_def]
             cases h : x.2.1[jm.1]? with
             | none => rfl
             | some tx => cases tx; rfl
       _ = _ := qWeight_map _ _ _ _

noncomputable def loss (S : Sha2Set) (L q qs ar : ℕ) : ℝ≥0∞ :=
  let C := tcrTargets S.vp
  let m := 2*(LongPhase.tails ar+1)
  let post := LongClass.endLoss (LongPhase.cacheSize ar C) (ClassOne.budget S L q qs + m) m
  LongPhase.firstLoss ar C + (LongPhase.avoidLoss ar C + post) +
    Wots256.phaseLoss (C+C) (max (LongPhase.tails ar) 9)

private theorem average (seeds : ProbComp Node) (ar n C : ℕ)
    (choose : OracleComp (TcrSpec (ShortBlocks.tcrP seeds ar n (fun _ => IV128))) σ)
    (M : (Input → Output) → σ → Node → Closed W (ℕ × ShortBlocks.Msg ar))
    (ρ : Matrix W W ℂ) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) (q : ℕ)
    (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => M H st pk) q)
    (setup : let A := ShortBlocks.classFirst seeds ar n choose;
      A.ChooseBound 0 ∧ A.ChalBound C ∧ A.CollBound C ∧ A.CollLen 9) :
    let m := 2*(LongPhase.tails ar+1)
    SetOracle.uniformMean (fun t => mean seeds (ShortBlocks.tcrValue seeds n choose M ρ t)) ≤
      LongPhase.firstLoss ar C + (LongPhase.avoidLoss ar C + LongClass.endLoss (LongPhase.cacheSize ar C) (q+m) m) +
        Wots256.phaseLoss (C+C) (max (LongPhase.tails ar) 9) := by
  obtain ⟨h0,hch,hc,hL⟩ := setup
  apply LongPhase.class_average seeds ar n choose M ρ hp ht C h0 hch hc hL
  intro seed b x cache cv hcv fin hm hg
  have post := LongClass.conditional seeds ar n seed cv (look cache) x.2.1
    (fun H => M H x.1 seed) ρ b (LongPhase.cacheSize ar C) q hg fin hm.twfun hcv (hq x.1 seed) hp ht
  simp_rw [← score seeds ar n seed cv (look cache) _ _ b M ρ x] at post
  exact post

attribute [local irreducible] tcrTargets arityTargets
theorem class_tcr_le (S : Sha2Set) (hn : S.vp.params.n = 16)
    (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node) (F : PortForger Input Output E)
    (ar : ℕ) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    SetOracle.uniformMean (fun t => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F t))) ≤ loss S c.ml q qs ar := by
  cases S <;> try contradiction
  · simp_rw [ShortBlocks.measured_slow rand seeds F ar]
    exact average seeds ar (arityTargets Sha2Set.s128s.vp ar) (tcrTargets Sha2Set.s128s.vp)
      _ _ F.ρ₀ F.posSemidef F.trace_eq_one _ (ClassOne.class_cost .s128s rand F ar c q qs hq hs hc) (ShortBlocks.setup_128s seeds ar)
  · simp_rw [ShortBlocks.measured_fast rand seeds F ar]
    exact average seeds ar (arityTargets Sha2Set.s128f.vp ar) (tcrTargets Sha2Set.s128f.vp)
      _ _ F.ρ₀ F.posSemidef F.trace_eq_one _ (ClassOne.class_cost .s128f rand F ar c q qs hq hs hc) (ShortBlocks.setup_128f seeds ar)
end Reduction.Compression.LongSignature

namespace Reduction.Compression
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)

noncomputable def smallLongClass (S : Sha2Set) (L q qs ar : ℕ) : ℝ≥0∞ :=
  if ar ≤ 2 then ShortBlocks.loss S L q qs else LongSignature.loss S L q qs ar

noncomputable def smallLongSingleBound (S : Sha2Set) (L q qs : ℕ) : ℝ≥0∞ :=
  smallWithComponents S L q qs (SmallItsr.loss S L q qs (S.vp.params.a*S.vp.params.k)) (smallLongClass S L q qs)

noncomputable def smallLongBound (S : Sha2Set) (L q qs : ℕ) : ℝ≥0∞ :=
  smallWithClasses S L q qs (smallLongClass S L q qs)

variable (S : Sha2Set) (hn : S.vp.params.n = 16) (rand : S.Node → S.Node → ProbComp S.Node)
  (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)
variable (c : Caps) (q qs : ℕ) (hq : ∀ pk, CountBound isPort (F.main pk) q)
  (hs : ∀ pk, CountBound isSign (F.main pk) qs) (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
include hn hq hs hc

theorem small_long_class_le (ar : ℕ) :
    uniformMean (fun g => qSM_DT_TCR_Advantage (qbTcrArM ar (reduced S rand seeds F g))) ≤ smallLongClass S c.ml q qs ar := by
  unfold smallLongClass
  split_ifs with ha
  · exact ShortBlocks.class_tcr_le S hn rand seeds F ar ha c q qs hq hs hc
  · exact LongSignature.class_tcr_le S hn rand seeds F ar c q qs hq hs hc

/-- Strong unforgeability of either SHA2-128 parameter set with the tighter,
single-signature message-hash extraction and a separate estimate at each arity. -/
theorem small_long_single_suf (single : qs ≤ 1) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      smallLongSingleBound S c.ml q qs :=
  small_suf_with_components S hn rand seeds F c q qs _ _
    (SmallItsr.single_itsr S hn rand seeds F c q qs single hq hs hc)
    (small_long_class_le S hn rand seeds F c q qs hq hs hc) hq hs hc

theorem small_long_single_euf (single : qs ≤ 1) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      smallLongSingleBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans
    (small_long_single_suf S hn rand seeds F c q qs hq hs hc single)

/-- The same class estimates compose with the message-hash reduction for
an arbitrary signing-query budget. -/
theorem small_long_suf :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      smallLongBound S c.ml q qs :=
  small_suf_with_classes S hn rand seeds F c q qs _ (small_long_class_le S hn rand seeds F c q qs hq hs hc) hq hs hc

theorem small_long_euf :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S rand seeds F g)) ≤
      smallLongBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S rand seeds F g))).trans (small_long_suf S hn rand seeds F c q qs hq hs hc)

end Reduction.Compression
#print axioms Reduction.Compression.LongSignature.class_tcr_le
#print axioms Reduction.Compression.small_long_single_suf
#print axioms Reduction.Compression.small_long_single_euf
#print axioms Reduction.Compression.small_long_suf
#print axioms Reduction.Compression.small_long_euf
