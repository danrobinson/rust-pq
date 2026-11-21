import Integration.SlhDsaBridgeTcr
import Integration.SlhDsaBridgeMach
import Integration.SlhDsaComposedEnc

/-!
# The class-TCR terms, closed (game side `qtcr` + machine side `qmach`)

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

`tcr_term` (`Integration/SlhDsaBridgeTcr.lean`, game side) consumes the hybrid-model hypothesis
`hModel`; `tcr_hModel` (`Integration/SlhDsaBridgeMach.lean`, agent `qmach`) proves it with
`q' = q + tcrMHashes Link.vp qs` for every port forger with at most `q` port calls and `qs`
signing queries per path.  Together: the four class-TCR term inequalities with NO hypothesis
beyond the forger's resources and `35 ≤ c.tl`, in the form consumed by `composed_of_linear_eps`
(`h1`, `h2`, `hLen`, `hK`), with the counts of `openCounts128s qs`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum

set_option linter.unusedSectionVars false

namespace Reduction

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- **Class-TCR term at arity `n`, closed**: count `q + tcrMHashes Link.vp qs`. -/
theorem tcr_term_closed (n : ℕ) (hn : n ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
        epsTcr0 (q + tcrMHashes Link.vp qs) :=
  tcr_term c optRand₀ pkSeedDist₀ F n hn _
    (tcr_hModel c optRand₀ pkSeedDist₀ F n q qs hq hqs)

/-- **The four class-TCR terms, closed**, with the counts `r = openCounts128s qs`, exactly the
hypotheses `h1`, `h2`, `hLen`, `hK` of `composed_of_linear_eps` at
`e· = epsTcr0 (q + r.tcr·)`. -/
theorem tcr_terms_closed_128s (q qs : ℕ) (htl : 35 ≤ c.tl)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM 1 (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
          epsTcr0 (q + (openCounts128s qs).tcr1) ∧
      avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM 2 (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
          epsTcr0 (q + (openCounts128s qs).tcr2) ∧
      avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM Link.vp.params.len (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
          epsTcr0 (q + (openCounts128s qs).tcrLen) ∧
      avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM Link.vp.params.k (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
          epsTcr0 (q + (openCounts128s qs).tcrK) := by
  obtain ⟨e1, e2, eL, eK⟩ := tcrMHashes_openCounts128s qs
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← e1]; exact tcr_term_closed c optRand₀ pkSeedDist₀ F 1 (by omega) q qs hq hqs
  · rw [← e2]; exact tcr_term_closed c optRand₀ pkSeedDist₀ F 2 (by omega) q qs hq hqs
  · rw [← eL]
    exact tcr_term_closed c optRand₀ pkSeedDist₀ F _ (by rw [len_eq_35]; exact htl) q qs hq hqs
  · rw [← eK]
    exact tcr_term_closed c optRand₀ pkSeedDist₀ F _ (by rw [k_eq_14]; omega) q qs hq hqs

end closed

section headline

variable {W : Type} [Fintype W]

/-- The bridge hypotheses still open after the class-TCR terms (`tcr1/tcr2/tcrLen/tcrK`) are
discharged: the seven fields of `BridgesRest` other than those four (UNPROVED). -/
structure BridgesRestNoTcr (c : Caps)
    (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
    (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)
    (B : ∀ ω, QForger W (internalAlg Link.vp (primsΩ ω) (optRand ω) (pkSeedDist ω)))
    (R₂ I₂ : Ω128 c → ℝ≥0∞) (q qs : ℕ) (r : RedCounts) : Prop where
  /-- `PRF_msg`. -/
  msg : MixPair (avΩ c R₂) (avΩ c I₂) (PrfValue (q + r.msg))
  /-- ITSR of `H_msg`, at most `qs` target requests. -/
  itsr : MixLE
    (avΩ c fun ω ↦ qItsrAdvantage (itsrProblem Link.vp (primsΩ ω)) (qbItsrL (B ω)) (B ω).ρ₀)
    (ItsrValue (q + r.itsr) qs)
  /-- DSPR (source final validity), FORS leaves. -/
  dspr : MixPair (avΩ c fun ω ↦ qDsprFV_Success (qToDspr (B ω)))
    (avΩ c fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) (DsprValue (q + r.dspr))
  /-- TCR (source final validity), FORS leaves. -/
  tcrFv : MixLE (avΩ c fun ω ↦ qTcrFV_Advantage (qToTcr (B ω))) (TcrFvValue (q + r.tcrFv))
  /-- SM-DT-UD of the WOTS chains. -/
  ud : MixPair (avΩ c fun ω ↦ qSM_DT_UD_RealSuccess (qrUd (B ω)))
    (avΩ c fun ω ↦ qSM_DT_UD_IdealSuccess (qrUd (B ω))) (UdValue (q + r.ud))
  /-- SM-DT-PRE of the WOTS chains. -/
  pre : MixLE (avΩ c fun ω ↦ qSM_DT_PRE_Advantage (qrPre (B ω))) (PreValue (q + r.pre))
  /-- SM-DT-TCR of the WOTS chains. -/
  tcrT : MixLE (avΩ c fun ω ↦ qSM_DT_TCR_Advantage (qrTcrT (B ω))) (TcrValue (q + r.tcrT))

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- **Composed theorem, SUF-CMA, encoding fixed, `PRF` term under `hInd`, class-TCR terms
PROVED** (counts `r = openCounts128s qs`). -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_tcr
    (F : PortForger (EncX c) EncY E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachSuf c optRand₀ pkSeedDist₀ F ω H)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRestNoTcr c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F)
        (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
          (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀)
        (fun ω ↦ qPrfIdealPr (qbPrfMsgWL sufCheck (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) q qs (openCounts128s qs)) :
    avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs (openCounts128s qs).noPrf := by
  have hb := hB hq hqs hcap
  obtain ⟨h1, h2, hL, hK⟩ := tcr_terms_closed_128s c optRand₀ pkSeedDist₀ F q qs htl hq hqs
  exact composed_of_linear_eps (internalΩ c optRand₀ pkSeedDist₀ encΩ F) _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_suf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (prf_term_suf c optRand₀ pkSeedDist₀ F q hq hInd)
    (hb.msg.le fun _ _ ↦ PrfValue.le) (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    h1 h2 hL hK
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

/-- **Composed theorem, EUF-CMA, encoding fixed, `PRF` term under `hInd`, class-TCR terms
PROVED** (counts `r = openCounts128s qs`). -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_tcr
    (F : PortForger (EncX c) EncY E) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (htl : 35 ≤ c.tl)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachEuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachEuf c optRand₀ pkSeedDist₀ F ω H)
    (hB : (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
      (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) →
      BridgesRestNoTcr c (optRandOf c optRand₀) (fun _ ↦ pkSeedDist₀)
        (internalΩ c optRand₀ pkSeedDist₀ encΩ F)
        (fun ω ↦ qPrfRealPr (msgPrf Link.vp (primsΩ ω))
          (qbPrfMsgL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀)
        (fun ω ↦ qPrfIdealPr (qbPrfMsgL (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))
          (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).ρ₀) q qs (openCounts128s qs)) :
    avΩ c (fun ω ↦ qUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))) ≤
      composedBoundFinal q qs (openCounts128s qs).noPrf := by
  have hb := hB hq hqs hcap
  obtain ⟨h1, h2, hL, hK⟩ := tcr_terms_closed_128s c optRand₀ pkSeedDist₀ F q qs htl hq hqs
  exact composed_of_linear_eps (internalΩ c optRand₀ pkSeedDist₀ encΩ F) _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (fun ω ↦ qPrfIdealPr_le_one' _ (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).posSemidef
      (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω).trace_eq_one)
    (slhdsa_sha2_128s_pure_bytes_euf_cma_linear_quantum_uniform c (optRandOf c optRand₀)
      (fun _ ↦ pkSeedDist₀) fun ω ↦ F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω))
    (prf_term_euf c optRand₀ pkSeedDist₀ F q hq hInd)
    (hb.msg.le fun _ _ ↦ PrfValue.le) (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    h1 h2 hL hK
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

end headline

end Reduction

#print axioms Reduction.tcr_term_closed
#print axioms Reduction.tcr_terms_closed_128s
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_tcr
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_tcr
