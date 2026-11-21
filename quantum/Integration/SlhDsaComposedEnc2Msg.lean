import Integration.SlhDsaComposedEnc
import Integration.SlhDsaBridgeMsg

/-!
# The composed QROM statement with `hInd` and the `PRF_msg` bridge discharged

NOT part of the default target; compiled like the other `Integration/*.lean` files.

`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc2msg`: as
`…_qrom_enc` (`Integration/SlhDsaComposedEnc.lean`) with

* `hInd` removed (proved: `QInd.prfMachSuf_withPrf`, `QInd.prfMachEuf_withPrf`,
  `Integration/SlhDsaBridgeInd.lean`);
* the field `msg` of `BridgesRest` removed (proved: `QMsg.msg_term_suf`, `QMsg.msg_term_euf`,
  `Integration/SlhDsaBridgeMsg.lean`, using the cap hypothesis `hcap`), with count `q`: the
  bound is at `r.noPrfMsg` (`prf := 0`, `msg := 0`);
* the remaining ten fields as the hypothesis bundle `BridgesRest10` (UNPROVED).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

namespace Reduction

variable {W : Type} [Fintype W]

section
variable (c : Caps)
  (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
  (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)

/-- The bridge hypotheses for the ten terms other than `PRF` and `PRF_msg` (UNPROVED):
`BridgesRest` (`Integration/SlhDsaComposedEnc.lean`) without its field `msg`, field for
field. -/
structure BridgesRest10
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (q qs : ℕ) (r : RedCounts) : Prop where
  /-- ITSR of `H_msg`, at most `qs` target requests. -/
  itsr : MixLE
    (avΩ c fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀)
    (ItsrValue (q + r.itsr) qs)
  /-- DSPR (source final validity), FORS leaves. -/
  dspr : MixPair (avΩ c fun ω ↦ qDsprFV_Success (qToDspr (B ω)))
    (avΩ c fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) (DsprValue (q + r.dspr))
  /-- TCR (source final validity), FORS leaves. -/
  tcrFv : MixLE (avΩ c fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) (TcrFvValue (q + r.tcrFv))
  /-- SM-DT-TCR, arity 1. -/
  tcr1 : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 1 (B ω))) (TcrValue (q + r.tcr1))
  /-- SM-DT-TCR, arity 2. -/
  tcr2 : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM 2 (B ω))) (TcrValue (q + r.tcr2))
  /-- SM-DT-TCR, arity `len`. -/
  tcrLen : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.len (B ω)))
    (TcrValue (q + r.tcrLen))
  /-- SM-DT-TCR, arity `k`. -/
  tcrK : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM Link.vp.params.k (B ω)))
    (TcrValue (q + r.tcrK))
  /-- SM-DT-UD of the WOTS chains. -/
  ud : MixPair (avΩ c fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω)))
    (avΩ c fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) (UdValue (q + r.ud))
  /-- SM-DT-PRE of the WOTS chains. -/
  pre : MixLE (avΩ c fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) (PreValue (q + r.pre))
  /-- SM-DT-TCR of the WOTS chains. -/
  tcrT : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) (TcrValue (q + r.tcrT))

end

/-- The reduction's counts with no charge for the `PRF` and `PRF_msg` terms. -/
def RedCounts.noPrfMsg (r : RedCounts) : RedCounts := { r with prf := 0, msg := 0 }

section port

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- **Composed theorem, SUF-CMA, encoding fixed, `PRF` and `PRF_msg` terms proved; ten bridge
hypotheses left (`BridgesRest10`).** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc2msg
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRest10 c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F) q qs r) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrfMsg := by
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
    (QMsg.msg_term_suf c optRand₀ pkSeedDist₀ F q hq hcap)
    (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

/-- **Composed theorem, EUF-CMA, encoding fixed, `PRF` and `PRF_msg` terms proved; ten bridge
hypotheses left (`BridgesRest10`).** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc2msg
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRest10 c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F) q qs r) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs r.noPrfMsg := by
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
    (QMsg.msg_term_euf c optRand₀ pkSeedDist₀ F q hq hcap)
    (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

end port

end Reduction

#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc2msg
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc2msg
