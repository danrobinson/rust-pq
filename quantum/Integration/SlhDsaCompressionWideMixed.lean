import Integration.SlhDsaCompressionWideClosed
import Integration.SlhDsaCompressionClassTwoPhase

namespace Reduction.Compression
open MLink Ideal SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal
open SetOracle (uniformMean)
open scoped ComplexOrder
variable (S : Sha2Set) (r : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
variable {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Input Output E)

/-- Shared-compression signature bound charging the honest class-TCR walk classically. -/
noncomputable def wideMixedBound (L q qs : ℕ) :=
  wideLossWithClasses S L q qs (fun ar => ClassCollision.twoPhaseLoss S ar L q qs) +
    MessageHash.coordinateLoss S (MessageHash.queries S L q qs)

theorem wide_suf_mixed (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qStrongUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideMixedBound S c.ml q qs :=
  (wide_suf_with_classes S r seeds F hw c q qs hq hs hc _ (fun ar ha =>
    ClassCollision.two_phase_class_tcr S r seeds F ar hw ha c q qs hq hs hc)).trans
    (add_le_add le_rfl (MessageHash.signature_itsr_le S r seeds F hw c q qs hq hs hc))

theorem wide_euf_mixed (hw : S.vp.params.n ≠ 16) (c : Caps) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun g => qUnforgeableAdvantage (experimentForger S r seeds F g)) ≤ wideMixedBound S c.ml q qs :=
  (Finset.sum_le_sum fun g _ => mul_le_mul' (a := unifW _ g) le_rfl
    (quantum_euf_le_suf (experimentForger S r seeds F g))).trans
    (wide_suf_mixed S r seeds F hw c q qs hq hs hc)
theorem wideMixedBound_benchmark (L qs : ℕ) : 1 ≤ wideMixedBound S L (2^40) qs :=
  (MessageHash.coordinate_benchmark S L qs).trans le_add_self

end Reduction.Compression
#print axioms Reduction.Compression.wide_suf_mixed
#print axioms Reduction.Compression.wide_euf_mixed
#print axioms Reduction.Compression.wideMixedBound_benchmark
