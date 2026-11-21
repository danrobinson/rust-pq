import Integration.SlhDsaComposedEnc
import Integration.SlhDsaBridgeInd

/-!
# The composed QROM statement with `hInd` discharged

NOT part of the default target; compiled like the other `Integration/*.lean` files.

`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc2`: exactly
`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc` (`Integration/SlhDsaComposedEnc.lean`)
WITHOUT the hypothesis `hInd`, which is now the theorem `QInd.prfMachSuf_withPrf` /
`QInd.prfMachEuf_withPrf` (`Integration/SlhDsaBridgeInd.lean`).  The eleven `BridgesRest`
fields are still hypotheses (`hB`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

namespace Reduction

section port

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- **Composed theorem, SUF-CMA, encoding fixed, `PRF` term proved, no `hInd`.** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc2
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRest c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F)
        (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
          (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀)
        (fun ω ↦ qPrfIdealPr (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) q qs r) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrf := by
  have hb := hB hq hqs hcap
  exact composed_of_linear_eps (internalΩ c optRand₀ pkSeedDist₀ encΩ F) _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (prf_term_suf c optRand₀ pkSeedDist₀ F q hq
      (QInd.prfMachSuf_withPrf c optRand₀ pkSeedDist₀ F))
    (hb.msg.le fun _ _ ↦ PrfValue.le) (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

/-- **Composed theorem, EUF-CMA, encoding fixed, `PRF` term proved, no `hInd`.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc2
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRest c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F)
        (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
          (qbPrfMsgL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀)
        (fun ω ↦ qPrfIdealPr (qbPrfMsgL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) q qs r) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrf := by
  have hb := hB hq hqs hcap
  exact composed_of_linear_eps (internalΩ c optRand₀ pkSeedDist₀ encΩ F) _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (prf_term_euf c optRand₀ pkSeedDist₀ F q hq
      (QInd.prfMachEuf_withPrf c optRand₀ pkSeedDist₀ F))
    (hb.msg.le fun _ _ ↦ PrfValue.le) (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

end port

end Reduction

#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc2
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc2
