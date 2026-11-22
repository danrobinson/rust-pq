import Ideal.Realize.FinalTight
import Ideal.Realize.MsgMark

/-!
# Second tightening: shape marking for the `PRF` and `PRF_msg` games (`status/TIGHT.md`, step M1)

`suf_ideal_closed_tight` (`FinalTight.lean`) charges every compression query of the `PRF` and
`PRF_msg` realisers `2^-128` (coefficients `1·QP`, `2·QM` of `linT`), about `2.2·10^7` queries
per signature each, nearly all of them the reduction's own `F`/`H` evaluations.  The marked
game bounds (`skPrf_bound_128s_marked`, `msgPrf_bound_128s_marked`) charge only queries at a
block of key shape, and the realisers make at most

* `qPrfM qf qs ℓ ≤ qf + (qs+1)·(32272 + 2·⌊(ℓ+56)/64⌋)` such queries (`Prf.AprfS_mark`,
  `Prf.qPrfM_le`: key blocks `blk128 a k` of secret-key addresses);
* `qMsgM qf qs ℓ ≤ qf + (qs+1)·(39438 + ⌊(ℓ+56)/64⌋)` (`Msg.AmsgS_mark`, `Msg.qMsgM_le`:
  HMAC key blocks).

The composition is re-run with these two legs (`ideal_bound_core_legs`): the other nine terms,
the ITSR term and the `2^-256` part are those of `suf_ideal_closed_tight`.

* `QlinT2 qf qs ℓ = 27·qf + (qs+1)·(187792316 + 45·⌊(ℓ+56)/64⌋)` replaces `QlinT`
  (`QlinT2_le_QlinT`: never larger; the per-signature constant drops by `66132570`).
* `suf_ideal_closed_tight2`, `euf_ideal_closed_tight2`: same hypotheses as `suf_ideal_closed`.
* Numeric points (messages `≤ 2^26` bytes): `qs ≤ 2^20, qf ≤ 2^60`: `2^-77 + 2^-132 + 2^-63`;
  `qs ≤ 2^40, qf ≤ 2^64`: `2^-63 + 2^-94 + 2^-58`; `qs ≤ 2^64, qf ≤ 2^64`:
  `2^-45 + 2^-46 + 2^-36` (was `2^-35`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

/-! ## The two refined legs -/

/-- `skPrf_bound_128s_marked`. -/
noncomputable def epsPrfM (qM q qO : ℕ) : ℝ≥0∞ :=
  (qM : ℝ≥0∞) / 2 ^ 128 + (((q + qO) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- `msgPrf_bound_128s_marked`. -/
noncomputable def epsMsgM (qM q qO mlen : ℕ) : ℝ≥0∞ :=
  2 * (qM : ℝ≥0∞) / 2 ^ 128 +
    (((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

theorem RealizesPrf.boundM
    {B : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y} {q qO qM : ℕ}
    (R : RealizesPrf B q qO) (hM : IsQueryBoundP R.A (Prf.markQ blk128) qM) :
    (cfAvg fun g => Reduction.prfRealPr (B g)) ≤
      (cfAvg fun g => Reduction.prfIdealPr (B g)) + epsPrfM qM q qO := by
  have h1 : (cfAvg fun g => Reduction.prfRealPr (B g)) = cfAdvantage fun g =>
      (Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (R.A.inst g) :=
    cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => Reduction.prfIdealPr (B g)) = cfAdvantage fun g =>
      PRFScheme.prfIdealExperiment (R.A.inst g) :=
    cfAvg_of_evalDist_eq R.ideal
  rw [h1, h2]
  have h3 := skPrf_bound_128s_marked R.A qM q qO hM R.hq R.hO
  unfold skPrfAdvantageI at h3
  exact (cfAdvantage_le_add_boolDist _ _).trans (add_le_add le_rfl h3)

theorem RealizesMsg.boundM {B : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g))}
    {q qO mlen qM : ℕ} (R : RealizesMsg B q qO mlen)
    (hM : IsQueryBoundP R.A (MsgPrf.markK ikey okey) qM) :
    (cfAvg fun g => Reduction.msgRealPr (B g)) ≤
      (cfAvg fun g => Reduction.msgIdealPr (B g)) + epsMsgM qM q qO mlen := by
  have h1 : (cfAvg fun g => Reduction.msgRealPr (B g)) = msgRealI R.A :=
    cfAvg_of_evalDist_eq R.real
  have h2 : (cfAvg fun g => Reduction.msgIdealPr (B g)) = msgIdealI R.A :=
    (cfAvg_of_evalDist_eq R.ideal).trans (msgIdealI_prims R.A).symm
  rw [h1, h2]
  exact msgPrf_bound_128s_marked R.A qM q qO mlen hM R.hq R.hO R.hM

/-! ## The composition with the two legs as hypotheses -/

private theorem compose_arith'
    {adv r1 i1 a1 r2 i2 a2 c c' Ds S dv T T' X X' n R I aU p p' t t' : ℝ≥0∞}
    (h1 : r1 ≤ i1 + a1) (h2 : r2 ≤ i2 + a2) (h3 : Ds ≤ S + dv) (h4 : R ≤ I + aU)
    (hc : c ≤ c') (hT : T ≤ T') (hX : X ≤ X') (hp : p ≤ p') (ht : t ≤ t')
    (hfin : i1 + i2 + S + n * I ≠ ⊤)
    (h : adv + (i1 + i2 + S + n * I) ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t) :
    adv ≤ a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t' := by
  have h' : adv + (i1 + i2 + S + n * I) ≤
      (a1 + a2 + c' + (dv + 3 * T') + X' + n * aU + p' + t') + (i1 + i2 + S + n * I) :=
    calc adv + (i1 + i2 + S + n * I)
        ≤ r1 + r2 + c + (Ds + 3 * T) + X + n * R + p + t := h
      _ ≤ (i1 + a1) + (i2 + a2) + c' + ((S + dv) + 3 * T') + X' + n * (I + aU) + p' + t' := by
          gcongr
      _ = _ := by ring
  exact (ENNReal.add_le_add_iff_right hfin).1 h'

section Core

variable {pkSeedDist : ProbComp (Bytes 16)} {γ : ℝ≥0∞}

/-- **`ideal_bound_core` with the `PRF` and `PRF_msg` legs as hypotheses** (`e₁`, `e₂` any bounds
on the two averaged real-minus-ideal gaps; the realisers `R₁`, `R₂` are used only to see that the
averaged ideal probabilities are at most `1`). -/
theorem ideal_bound_core_legs (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (a : CF St Blk → ℝ≥0∞)
    (B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y)
    (B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g)))
    (B₃ : ∀ g : CF St Blk, KeyedHash.ITSRAdversary (Reduction.itsrProblem Link.vp (primsG (liftC g))))
    (D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1))
    (C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2))
    (C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len))
    (C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k))
    (B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist))
    (B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist))
    (hlin : ∀ g, a g + Reduction.linearIdealSide (B₁ g) (B₂ g) (D g) (B₆ g) ≤
      Reduction.linearRealSide pkSeedDist (B₁ g) (B₂ g) (B₃ g) (D g) (T g) (C₁ g) (C₂ g) (C₃ g)
        (C₄ g) (B₆ g) (B₇ g) (B₈ g))
    {εI : ℝ≥0∞} (hI : (cfAvg fun g => KeyedHash.ITSRAdvantage (B₃ g)) ≤ εI)
    {q qO : ℕ} (R₁ : RealizesPrf B₁ q qO)
    {qm qOm mlen : ℕ} (R₂ : RealizesMsg B₂ qm qOm mlen)
    {pD : P3} (RD : RealizesDspr pkSeedDist D pD) (hD : pD.q₂ ≤ 2 ^ 126)
    {pT : P3} (RT : RealizesForsTcr pkSeedDist T pT)
    {pF pH pL pK : P5} (RF : RealizesTcr pkSeedDist 1 C₁ pF) (RH : RealizesTcr pkSeedDist 2 C₂ pH)
    (RL : RealizesTcr pkSeedDist Link.vp.params.len C₃ pL)
    (RK : RealizesTcr pkSeedDist Link.vp.params.k C₄ pK)
    {pU pP pW : P5} (RU : RealizesUd pkSeedDist B₆ pU) (RP : RealizesPre pkSeedDist B₇ pP)
    (RW : RealizesWotsTcr pkSeedDist B₈ pW)
    {e₁ e₂ : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr (B₁ g)) ≤
      (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr (B₂ g)) ≤
      (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) + e₂) :
    cfAvg a ≤ e₁ + e₂ + εI +
      (epsDspr γ pD + 3 * epsForsTcr γ pT) +
      (epsTcr γ pF + epsTcr γ pH + epsTcrLen γ pL + epsTcrK γ pK) +
      14 * epsUd γ pU + epsPre γ pP + epsTcr γ pW := by
  have havg := cfAvg_mono hlin
  simp only [Reduction.linearIdealSide, Reduction.linearRealSide, cfAvg_add, cfAvg_mul_left]
    at havg
  rw [w_sub_two_128s] at havg
  have i1 : (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) ≤ 1 := by
    rw [show (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) = _ from cfAvg_of_evalDist_eq R₁.ideal]
    exact cfAdvantage_le_one _
  have i2 : (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) ≤ 1 := by
    rw [show (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) = _ from cfAvg_of_evalDist_eq R₂.ideal]
    exact cfAdvantage_le_one _
  have i3 : (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) ≤ 1 := by
    rw [show (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) = _ from
      cfAvg_of_evalDist_eq RD.sp]
    exact cfAdvantage_le_one _
  have i4 : (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) ≤ 1 := by
    rw [show (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) = _ from cfAvg_of_evalDist_eq RU.ideal]
    exact cfAdvantage_le_one _
  have hfin : (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) +
      (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) +
      (cfAvg fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability (D g)) +
      ((14 : ℕ) : ℝ≥0∞) * (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨(i1.trans_lt ENNReal.one_lt_top).ne, (i2.trans_lt ENNReal.one_lt_top).ne⟩,
      (i3.trans_lt ENNReal.one_lt_top).ne⟩,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (i4.trans_lt ENNReal.one_lt_top).ne⟩
  have key := compose_arith' h₁ h₂ (RD.bound hγ hD) (RU.bound hγ) hI (RT.bound hγ)
    (add_le_add (add_le_add (add_le_add (RF.bound hγ (Or.inl rfl)) (RH.bound hγ (Or.inr rfl)))
      (RL.bound_len hγ len_128s)) (RK.bound_k hγ k_128s))
    (RP.bound hγ) (RW.bound hγ) hfin havg
  simpa using key

end Core

section Bundle

variable {pkSeedDist : ProbComp (Bytes 16)}
  {B₁ : ∀ g : CF St Blk, PRFScheme.PRFAdversary
      ((primsG (liftC g)).PkSeed × Reduction.SkAdrs Link.vp) (primsG (liftC g)).Y}
  {B₂ : ∀ g : CF St Blk, Reduction.MsgPrfAdv (primsG (liftC g))}
  {D : ∀ g : CF St Blk, SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {T : ∀ g : CF St Blk, SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {C₁ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 1)}
  {C₂ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist 2)}
  {C₃ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.len)}
  {C₄ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.thashArityProblemT Link.vp (primsG (liftC g)) pkSeedDist Link.vp.params.k)}
  {B₆ : ∀ g : CF St Blk, SM_DT_UD_Adversary
      (Reduction.wotsUdProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {B₇ : ∀ g : CF St Blk, SM_DT_PRE_Adversary
      (Reduction.wotsPreProblem Link.vp (primsG (liftC g)) pkSeedDist)}
  {B₈ : ∀ g : CF St Blk, SM_DT_TCR_Adversary
      (Reduction.wotsTcrProblemT Link.vp (primsG (liftC g)) pkSeedDist)}

/-- The sum of the explicit bounds, with the `PRF` and `PRF_msg` terms replaced by `e₁`, `e₂`. -/
noncomputable def Realizers.epsL (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    (e₁ e₂ γ : ℝ≥0∞) : ℝ≥0∞ :=
  e₁ + e₂ + (epsDspr γ R.pD + 3 * epsForsTcr γ R.pT) +
    (epsTcr γ R.pF + epsTcr γ R.pH + epsTcrLen γ R.pL + epsTcrK γ R.pK) +
    14 * epsUd γ R.pU + epsPre γ R.pP + epsTcr γ R.pW

theorem epsPrfM_le_t {qM q qO Q Qc N : ℕ} (hqM : qM ≤ Q) (hq : q ≤ Qc) (hO : qO ≤ N) :
    epsPrfM qM q qO ≤ nf Q ((Qc + N) ^ 2) := by
  have e : epsPrfM qM q qO = nf qM ((q + qO) ^ 2) := by
    unfold epsPrfM nf
    simp only [div_eq_mul_inv]
  rw [e]
  exact nf_mono hqM (Nat.pow_le_pow_left (by omega) 2)

theorem epsMsgM_le_t {qM q qO mlen Q Qc qs ℓ : ℕ} (hqM : qM ≤ Q) (hq : q ≤ Qc) (hO : qO ≤ qs)
    (hm : mlen ≤ 64 * ℓ) :
    epsMsgM qM q qO mlen ≤ nf (2 * Q) ((Qc + qs * (ℓ + 1) + 2) ^ 2) := by
  have e : epsMsgM qM q qO mlen = nf (2 * qM) ((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2) := by
    unfold epsMsgM nf
    simp only [div_eq_mul_inv]
    push_cast
    ring
  rw [e]
  have h1 : qO * ((mlen + 24) / 64 + 1) ≤ qs * (ℓ + 1) := Nat.mul_le_mul hO (by omega)
  exact nf_mono (by omega) (Nat.pow_le_pow_left (by omega) 2)

/-- **`Realizers.eps_le_tight` with the refined `PRF`/`PRF_msg` legs**: the same normal form
`nf (linT QP QM QF QT QW) (polyP …)`, now with `QP`, `QM` caps on the MARKED queries `qPM`, `qMM`
only (the total counts `R.q`, `R.qm` enter the `2^-256` part, under `R.Le`). -/
theorem Realizers.epsL_le_tight (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    {Qc N qs ℓ QP QM QF QT QW qPM qMM : ℕ} (h : R.Le Qc N qs ℓ)
    (hP : qPM ≤ QP) (hM : qMM ≤ QM)
    (hD : R.pD.q₁ = 0) (hT : R.pT.q₁ = 0) (hT2 : R.pT.q₂ ≤ QF)
    (hF : R.pF.q₁ = 0) (hF2 : R.pF.q₂ ≤ QT) (hH : R.pH.q₁ = 0) (hH2 : R.pH.q₂ ≤ QT)
    (hL : R.pL.q₁ = 0) (hL2 : R.pL.q₂ ≤ QT) (hK : R.pK.q₁ = 0) (hK2 : R.pK.q₂ ≤ QT)
    (hU : R.pU.q₁ = 0) (hU2 : R.pU.q₂ ≤ QW) (hR : R.pP.q₁ = 0) (hR2 : R.pP.q₂ ≤ QW)
    (hW : R.pW.q₁ = 0) (hW2 : R.pW.q₂ ≤ QW) :
    R.epsL (epsPrfM qPM R.q R.qO) (epsMsgM qMM R.qm R.qOm R.mlen) γu ≤
      nf (linT QP QM QF QT QW) (polyP Qc N qs ℓ) := by
  have e : nf (linT QP QM QF QT QW) (polyP Qc N qs ℓ) =
      nf QP ((Qc + N) ^ 2) + nf (2 * QM) ((Qc + qs * (ℓ + 1) + 2) ^ 2) +
      (nf 0 (4 * Qc + 2 * N + 3) + 3 * nf (QF + 1) (2 * Qc + N + 2)) +
      (nf (QT + 1) (2 * Qc + 42 * N + 2) + nf (QT + 1) (2 * Qc + 42 * N + 2) +
        nf (QT + 22) (18 * (2 * Qc + 22 * N + 21) ^ 2 + 2 * Qc + 42 * N + 1) +
        nf (QT + 10) (18 * (2 * Qc + 22 * N + 9) ^ 2 + 2 * Qc + 42 * N + 1)) +
      14 * nf QW (4 * Qc + 84 * N + 2) + nf (2 * (QW + 1)) (2 * Qc + 42 * N + 2) +
      nf (QW + 1) (2 * Qc + 42 * N + 2) := by
    unfold nf polyP linT
    push_cast
    ring
  rw [e]
  unfold Realizers.epsL
  gcongr
  · exact epsPrfM_le_t hP h.q h.qO
  · exact epsMsgM_le_t hM h.qm h.qOm h.mlen
  · exact epsDspr_le_t h.pD hD
  · exact epsForsTcr_le_t h.pT hT hT2
  · exact epsTcr_le_t h.pF hF hF2
  · exact epsTcr_le_t h.pH hH hH2
  · exact epsTcrLen_le_t h.pL hL hL2
  · exact epsTcrK_le_t h.pK hK hK2
  · exact epsUd_le_t h.pU hU hU2
  · exact epsPre_le_t h.pP hR hR2
  · exact epsTcr_le_t h.pW hW hW2

end Bundle

section Legs

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}
  {pkSeedDist : ProbComp (Bytes 16)}

/-- `suf_ideal_bound'` with the `PRF` and `PRF_msg` legs as hypotheses. -/
theorem suf_ideal_bound_legs {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrSufI S optRand pkSeedDist ≤ εI)
    (R : SufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) {e₁ e₂ : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr
        (Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.prfIdealPr
        (Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr
        (Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.msgIdealPr
        (Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))) + e₂) :
    sufI S optRand pkSeedDist ≤ εI + R.epsL e₁ e₂ γ := by
  rw [sufI_eq_cfAvg]
  refine (ideal_bound_core_legs hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_suf_cma_linear (structuralG g) (S.sufInst optRand pkSeedDist g))
    hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK R.ud R.pre R.wotsTcr
    h₁ h₂).trans (le_of_eq ?_)
  unfold Realizers.epsL
  ring

/-- `euf_ideal_bound'` with the `PRF` and `PRF_msg` legs as hypotheses. -/
theorem euf_ideal_bound_legs {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrEufI S optRand pkSeedDist ≤ εI)
    (R : EufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) {e₁ e₂ : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr
        (Reduction.bPrfC (S.typedE optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.prfIdealPr
        (Reduction.bPrfC (S.typedE optRand pkSeedDist g))) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr
        (Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.msgIdealPr
        (Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))) + e₂) :
    eufI S optRand pkSeedDist ≤ εI + R.epsL e₁ e₂ γ := by
  rw [eufI_eq_cfAvg]
  refine (ideal_bound_core_legs hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_euf_cma_linear (structuralG g) (S.eufInst optRand pkSeedDist g))
    hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK R.ud R.pre R.wotsTcr
    h₁ h₂).trans (le_of_eq ?_)
  unfold Realizers.epsL
  ring

end Legs

/-! ## The coefficient at the realisers of `Final.lean` -/

/-- **The `2^-128` coefficient after shape marking**: `27` per forger compression query, and per
signing query `187792316 ≈ 2^27.48` compression queries of the reductions' own hashing plus `45`
per message block. -/
def QlinT2 (qf qs ℓ : ℕ) : ℕ := 27 * qf + (qs + 1) * (187792316 + 45 * ((ℓ + 56) / 64))

theorem linT_le_QlinT2 (qf qs ℓ : ℕ) :
    linT (qf + (qs + 1) * (32272 + 2 * ((ℓ + 56) / 64)))
      (qf + (qs + 1) * (39438 + (ℓ + 56) / 64))
      (qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3))
      (qf + (qs + 1) * (25135729 + (ℓ + 56) / 64))
      (Wots.QcW qf qs ℓ) ≤ QlinT2 qf qs ℓ := by
  unfold linT QlinT2 Wots.QcW
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

/-- `QlinT2 ≤ QlinT`: never worse than the bound of `suf_ideal_closed_tight`. -/
theorem QlinT2_le_QlinT (qf qs ℓ : ℕ) : QlinT2 qf qs ℓ ≤ QlinT qf qs ℓ := by
  unfold QlinT2 QlinT
  generalize (ℓ + 56) / 64 = x
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

section Tight2

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem sufRealizersU_epsL_le :
    (sufRealizersU S oR hqf hqs hlong hout).epsL
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ) γu ≤
      nf (QlinT2 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((sufRealizersU S oR hqf hqs hlong hout).epsL_le_tight
    (sufRealizersU_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2Fors_eq qf qs ℓ).le
    rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Wots.pU_le qf qs ℓ).2.2.2.2 rfl (Wots.pP_le qf qs ℓ).2.2.2.2
    rfl (Wots.pW_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT2 qf qs ℓ) le_rfl)

theorem eufRealizersU_epsL_le :
    (eufRealizersU S oR hqf hqs hlong hout).epsL
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ) γu ≤
      nf (QlinT2 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((eufRealizersU S oR hqf hqs hlong hout).epsL_le_tight
    (eufRealizersU_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2Fors_eq qf qs ℓ).le
    rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Wots.pU_le qf qs ℓ).2.2.2.2 rfl (Wots.pP_le qf qs ℓ).2.2.2.2
    rfl (Wots.pW_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT2 qf qs ℓ) le_rfl)

/-- The SUF bound from any bound `εI` on the ITSR term, marked `PRF`/`PRF_msg` legs. -/
theorem suf_tight2_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrSufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT2 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (suf_ideal_bound_legs hγ_uniform hI (sufRealizersU S oR hqf hqs hlong hout)
    ((sufRealizersU_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfSuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfSuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgSuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgSuf_mark S oR _ hqf hqs hlong hout))).trans
    (add_le_add le_rfl (sufRealizersU_epsL_le S oR hqf hqs hlong hout))

/-- The EUF bound from any bound `εI` on the ITSR term, marked `PRF`/`PRF_msg` legs. -/
theorem euf_tight2_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrEufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT2 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (euf_ideal_bound_legs hγ_uniform hI (eufRealizersU S oR hqf hqs hlong hout)
    ((eufRealizersU_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfEuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfEuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgEuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgEuf_mark S oR _ hqf hqs hlong hout))).trans
    (add_le_add le_rfl (eufRealizersU_epsL_le S oR hqf hqs hlong hout))

end Tight2

/-! ## The headlines -/

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only, with
shape marking for the `PRF` and `PRF_msg` games.**  Same hypotheses as `suf_ideal_closed`; the
`2^-128` coefficient is `QlinT2 qf qs ℓ = 27·qf + (qs+1)·(187792316 + 45·⌊(ℓ+56)/64⌋)`
(`QlinT2_le_QlinT`: never larger than that of `suf_ideal_closed_tight`). -/
theorem suf_ideal_closed_tight2 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT2 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact suf_tight2_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrSufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- **EUF-CMA analogue of `suf_ideal_closed_tight2`.** -/
theorem euf_ideal_closed_tight2 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT2 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact euf_tight2_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrEufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- The right-hand side of `suf_ideal_closed_tight2` is at most that of
`suf_ideal_closed_tight` (and so, by `QlinT_le_old`, of `suf_ideal_closed`). -/
theorem tight2_le_tight (qf qs ℓ : ℕ) :
    epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT2 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  gcongr
  exact QlinT2_le_QlinT qf qs ℓ

/-! ## Numerics -/

theorem QlinT2_le {qf qs ℓ F₀ S₀ : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀) (hℓ : ℓ ≤ 2 ^ 26) :
    QlinT2 qf qs ℓ ≤ 27 * F₀ + (S₀ + 1) * (187792316 + 45 * 2 ^ 20) := by
  have := div64_le_2_20 hℓ
  unfold QlinT2
  gcongr

/-- The eleven-game part at caps `qf ≤ F₀`, `qs ≤ S₀`, `ℓ ≤ 2^26`, `QcAll ≤ Qc₀`, `NAll ≤ N₀`. -/
theorem eleven_tight2_le {qf qs ℓ F₀ S₀ Qc₀ N₀ k m : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hnum : (27 * F₀ + (S₀ + 1) * (187792316 + 45 * 2 ^ 20)) * 2 ^ 128 +
      polyP Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m) :
    nf (QlinT2 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (nf_mono (QlinT2_le hf hs hℓ) (polyP_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow k m hkm hnum)

/-- SUF, shape-marked `PRF`/`PRF_msg`, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_closed_tight2_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 60 + 2 ^ 46 := QcAll_le_of hs hℓ (Nat.add_le_add hf (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 60) (2 ^ 21) (2 ^ 60) (2007387 * 2 ^ 20) (2 ^ 20 + 1) (2 ^ 20) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight2_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight2_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- SUF, shape-marked `PRF`/`PRF_msg`, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-58`. -/
theorem suf_ideal_closed_tight2_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 58)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight2_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight2_le hf hs hℓ hQc (NAll_le_81 hs) (k := 58) (m := 198) rfl
      (by unfold polyP; norm_num)))

/-- SUF, shape-marked `PRF`/`PRF_msg`, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + 2^-36`. -/
theorem suf_ideal_closed_tight2_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 36)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight2_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight2_le hf hs hℓ hQc (NAll_le_82 hs) (k := 36) (m := 220) rfl
      (by unfold polyP; norm_num)))

/-- EUF, shape-marked `PRF`/`PRF_msg`, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_closed_tight2_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ + ((2 : ℝ≥0∞) ^ 63)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 60 + 2 ^ 46 := QcAll_le_of hs hℓ (Nat.add_le_add hf (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 60) (2 ^ 21) (2 ^ 60) (2007387 * 2 ^ 20) (2 ^ 20 + 1) (2 ^ 20) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight2_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight2_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- EUF, shape-marked `PRF`/`PRF_msg`, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-58`. -/
theorem euf_ideal_closed_tight2_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 58)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight2_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight2_le hf hs hℓ hQc (NAll_le_81 hs) (k := 58) (m := 198) rfl
      (by unfold polyP; norm_num)))

/-- EUF, shape-marked `PRF`/`PRF_msg`, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + 2^-36`. -/
theorem euf_ideal_closed_tight2_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 36)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight2_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight2_le hf hs hℓ hQc (NAll_le_82 hs) (k := 36) (m := 220) rfl
      (by unfold polyP; norm_num)))

end Ideal

#print axioms Ideal.Realize.Prf.qPrfM_le
#print axioms Ideal.Realize.Msg.qMsgM_le
#print axioms Ideal.RealizesPrf.boundM
#print axioms Ideal.RealizesMsg.boundM
#print axioms Ideal.ideal_bound_core_legs
#print axioms Ideal.Realizers.epsL_le_tight
#print axioms Ideal.suf_ideal_bound_legs
#print axioms Ideal.euf_ideal_bound_legs
#print axioms Ideal.linT_le_QlinT2
#print axioms Ideal.QlinT2_le_QlinT
#print axioms Ideal.sufRealizersU_epsL_le
#print axioms Ideal.eufRealizersU_epsL_le
#print axioms Ideal.suf_ideal_closed_tight2
#print axioms Ideal.euf_ideal_closed_tight2
#print axioms Ideal.tight2_le_tight
#print axioms Ideal.suf_ideal_closed_tight2_2_20
#print axioms Ideal.suf_ideal_closed_tight2_2_40
#print axioms Ideal.suf_ideal_closed_tight2_2_64
#print axioms Ideal.euf_ideal_closed_tight2_2_20
#print axioms Ideal.euf_ideal_closed_tight2_2_40
#print axioms Ideal.euf_ideal_closed_tight2_2_64
