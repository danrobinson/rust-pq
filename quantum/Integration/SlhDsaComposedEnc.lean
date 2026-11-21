import Integration.SlhDsaBridgePrf

/-!
# The composed QROM statement with the encoding fixed and the `PRF` term proved

NOT part of the default target; checked by `scripts/check-integration.sh`.

`slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc`: as
`…_qrom_of_bridges` (`Integration/SlhDsaComposedFinal.lean`), with

* the port function FIXED to `encΩ` (`Integration/SlhDsaBridgePrf.lean`): the forger is a
  `PortForger (EncX c) EncY E`, no quantification over an encoding;
* the `PRF` term PROVED (`prf_term_suf`, `prf_term_euf`), with count `q` (the reduction's own
  hashing is not charged), under ONE named hypothesis `hInd`: the `PRF` distinguisher machine of
  the reduction does not depend on the `PRF` component of the world
  (`prfMachSuf (ω.withPrf g) H = prfMachSuf ω H`).  This is a statement about the reduction's
  code only (no probability).  It is NOT provable by `rfl`: the signature and key types
  `SignatureCore core`, `PublicKeyCore core` are structures indexed by the whole `core`, which
  contains `PRF`, so the two machines are built through different intermediate types; a transport
  of the signing/verification/codec code along `core ↦ {core with PRF := g}` is needed.
* the other eleven terms still as bridge hypotheses (`BridgesRest`).
* the `Thash` list cap is now an explicit hypothesis `_htl : 35 ≤ c.tl` (`35 = len` is the
  largest `Thash` arity of SLH-DSA-SHA2-128s).  It is not used by the proof: it is the side
  condition under which the functions of `Ω128 c` (constant outside the caps) are random oracles
  on every input the scheme evaluates; the remaining bridge hypotheses can only hold under it.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

namespace Reduction

variable {W : Type} [Fintype W]

section
variable (c : Caps)
  (optRand : ∀ ω : Ω128 c, PublicKeyCore (primsΩ ω).core → ProbComp (primsΩ ω).Y)
  (pkSeedDist : ∀ ω : Ω128 c, ProbComp (primsΩ ω).PkSeed)

/-- The bridge hypotheses for the eleven terms other than `PRF` (UNPROVED); see `Bridges`. -/
structure BridgesRest
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

/-- The reduction's counts with no charge for the `PRF` term. -/
def RedCounts.noPrf (r : RedCounts) : RedCounts := { r with prf := 0 }

section port

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))

/-- **Composed theorem, SUF-CMA, encoding fixed, `PRF` term proved under `hInd`.** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachSuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachSuf c optRand₀ pkSeedDist₀ F ω H)
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
    (prf_term_suf c optRand₀ pkSeedDist₀ F q hq hInd)
    (hb.msg.le fun _ _ ↦ PrfValue.le) (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

/-- **Composed theorem, EUF-CMA, encoding fixed, `PRF` term proved under `hInd`.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc
    (F : PortForger (EncX c) EncY E) (q qs : ℕ) (r : RedCounts)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs)
    (hcap : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (_htl : 35 ≤ c.tl)
    (hInd : ∀ (ω : Ω128 c) g H, prfMachEuf c optRand₀ pkSeedDist₀ F (ω.withPrf g) H =
      prfMachEuf c optRand₀ pkSeedDist₀ F ω H)
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
    (prf_term_euf c optRand₀ pkSeedDist₀ F q hq hInd)
    (hb.msg.le fun _ _ ↦ PrfValue.le) (hb.itsr.le fun _ ↦ ItsrValue.le)
    (hb.dspr.le fun _ _ ↦ DsprValue.le) (hb.tcrFv.le fun _ ↦ TcrFvValue.le)
    (hb.tcr1.le fun _ ↦ TcrValue.le) (hb.tcr2.le fun _ ↦ TcrValue.le)
    (hb.tcrLen.le fun _ ↦ TcrValue.le) (hb.tcrK.le fun _ ↦ TcrValue.le)
    (hb.ud.le fun _ _ ↦ UdValue.le) (hb.pre.le fun _ ↦ PreValue.le)
    (hb.tcrT.le fun _ ↦ TcrValue.le)

end port

end Reduction

#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_suf_cma_qrom_enc
#print axioms Reduction.slhdsa_sha2_128s_pure_bytes_euf_cma_qrom_enc
