import Ideal.Realize.FinalTight6
import Ideal.Realize.WotsUdFine

/-!
# Seventh tightening: the message blocks of the SM-UD realiser are not charged
(`status/TIGHT.md` §9)

The SM-UD leg enters the composition `14` times (`w − 2` hybrids).  `udLeg_fine`
(`Ideal/Realize/WotsUdFine.lean`) bounds it with the per-game bound of `Games/UdFine.lean`:
the realiser's second phase issues each SHA-256 chain of an `H_msg` query as one chain query
whose first block is not the seed block, and such chains are not charged at `2^-128`.  The
SM-UD second-phase cap drops from `QcWL = … + (qs+2)·(x+3)` to
`QU = qf + 2·(121857·qs + 146514) + 9·(3577·qs + 146514)`.  The other ten legs are those of
`suf_ideal_closed_tight6` (same realisers, `sufRealizers5` / `eufRealizers5`).

* `ideal_bound_core_legs7`, `suf/euf_ideal_bound_legs7`: the composition with the UD leg as a
  hypothesis as well;
* `linT7 = QP + 2·QM + 3·QF + 4·QT + 3·QW + 14·QU + 40`,
  `polyP7 = polyP + 14·(20·N + 1)` (`Realizers.epsL7_le_tight`);
* `QlinT7 qf qs ℓ = 27·qf + qs·(16944233 + 17·x) + 29487867 + 17·x`, `x = ⌊(ℓ+56)/64⌋`
  (`= QlinT6 − 14·(qs+2)·(x+3)`, `QlinT7_add`);
* `suf_ideal_closed_tight7`, `euf_ideal_closed_tight7`: same hypotheses as `suf_ideal_closed`;
  `tight7_le_tight6`: never above `_tight6`;
* points (messages `≤ 2^26` bytes): `qs ≤ 2^20, qf ≤ 2^60`: `2^-77 + 2^-132 + 2^-63`;
  `qs ≤ 2^40, qf ≤ 2^64`: `2^-63 + 2^-94 + 2^-59`; `qs ≤ 2^64, qf ≤ 2^64`:
  `2^-45 + 2^-46 + (2^-39 + 2^-43)` (was `… + (2^-39 + 2^-40)`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

/-! ## The composition with the `PRF`, `PRF_msg` and SM-UD legs as hypotheses -/

private theorem compose_arith7
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

/-- **`ideal_bound_core_legs` with the SM-UD leg as a hypothesis too** (`e₆` any bound on the
averaged real-minus-ideal SM-UD gap; the realiser `RU` is used only to see that the averaged
ideal probability is at most `1`). -/
theorem ideal_bound_core_legs7 (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
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
    {e₁ e₂ e₆ : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr (B₁ g)) ≤
      (cfAvg fun g => Reduction.prfIdealPr (B₁ g)) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr (B₂ g)) ≤
      (cfAvg fun g => Reduction.msgIdealPr (B₂ g)) + e₂)
    (h₆ : (cfAvg fun g => SM_DT_UD_RealSuccess (B₆ g)) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (B₆ g)) + e₆) :
    cfAvg a ≤ e₁ + e₂ + εI +
      (epsDspr γ pD + 3 * epsForsTcr γ pT) +
      (epsTcr γ pF + epsTcr γ pH + epsTcrLen γ pL + epsTcrK γ pK) +
      14 * e₆ + epsPre γ pP + epsTcr γ pW := by
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
  have key := compose_arith7 h₁ h₂ (RD.bound hγ hD) h₆ hI (RT.bound hγ)
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

/-- The sum of the explicit bounds, with the `PRF`, `PRF_msg` and SM-UD terms replaced by `e₁`,
`e₂`, `e₆`. -/
noncomputable def Realizers.epsL7 (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    (e₁ e₂ e₆ γ : ℝ≥0∞) : ℝ≥0∞ :=
  e₁ + e₂ + (epsDspr γ R.pD + 3 * epsForsTcr γ R.pT) +
    (epsTcr γ R.pF + epsTcr γ R.pH + epsTcrLen γ R.pL + epsTcrK γ R.pK) +
    14 * e₆ + epsPre γ R.pP + epsTcr γ R.pW

/-- The fine SM-UD error in normal form. -/
theorem epsUdF_le_t {p : P5} {Qc N Q qM : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : qM ≤ Q) :
    epsUdF γu p qM ≤ nf Q (4 * Qc + 84 * N + 2 + (20 * N + 1)) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsUdF γu p qM =
      nf qM (p.q₂ + (2 * (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 1) +
        (1 + 2 * ((p.q₁ + p.qc) * max 1 p.L)) + 2 * p.q₂)) := by
    unfold epsUdF nf
    rw [h0]
    have : ((2 : ℝ≥0∞) ^ 256)⁻¹ = ((2 : ℝ≥0∞) ^ 128)⁻¹ * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
      rw [← ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), ← pow_add]
    rw [this]
    push_cast
    ring
  rw [e]
  have hm : max 1 p.L ≤ 10 := max_le (by norm_num) h4
  have hq : (0 + p.qc) * max 1 p.L ≤ 10 * N := by
    rw [zero_add]
    calc p.qc * max 1 p.L ≤ N * 10 := Nat.mul_le_mul h3 hm
      _ = 10 * N := by ring
  rw [h0]
  exact nf_mono hQ (by omega)

/-- The `2^-128` coefficient of the eleven terms with the fine SM-UD leg: `QU` is the cap on the
SM-UD realiser's RAW second-phase queries, `QW` the cap of the SM-PRE and SM-TCR realisers. -/
def linT7 (QP QM QF QT QW QU : ℕ) : ℕ := QP + 2 * QM + 3 * QF + 4 * QT + 3 * QW + 14 * QU + 40

/-- The `2^-256` part with the fine SM-UD leg. -/
def polyP7 (Qc N qs ℓ : ℕ) : ℕ := polyP Qc N qs ℓ + 14 * (20 * N + 1)

theorem polyP7_mono {Qc N qs ℓ Qc' N' qs' ℓ' : ℕ} (h1 : Qc ≤ Qc') (h2 : N ≤ N') (h3 : qs ≤ qs')
    (h4 : ℓ ≤ ℓ') : polyP7 Qc N qs ℓ ≤ polyP7 Qc' N' qs' ℓ' := by
  unfold polyP7
  have := polyP_mono h1 h2 h3 h4
  omega

/-- **`Realizers.epsL_le_tight` with the fine SM-UD leg.** -/
theorem Realizers.epsL7_le_tight (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    {Qc N qs ℓ QP QM QF QT QW QU qPM qMM qUM : ℕ} (h : R.Le Qc N qs ℓ)
    (hP : qPM ≤ QP) (hM : qMM ≤ QM)
    (hD : R.pD.q₁ = 0) (hT : R.pT.q₁ = 0) (hT2 : R.pT.q₂ ≤ QF)
    (hF : R.pF.q₁ = 0) (hF2 : R.pF.q₂ ≤ QT) (hH : R.pH.q₁ = 0) (hH2 : R.pH.q₂ ≤ QT)
    (hL : R.pL.q₁ = 0) (hL2 : R.pL.q₂ ≤ QT) (hK : R.pK.q₁ = 0) (hK2 : R.pK.q₂ ≤ QT)
    (hU : R.pU.q₁ = 0) (hU2 : qUM ≤ QU) (hR : R.pP.q₁ = 0) (hR2 : R.pP.q₂ ≤ QW)
    (hW : R.pW.q₁ = 0) (hW2 : R.pW.q₂ ≤ QW) :
    R.epsL7 (epsPrfM qPM R.q R.qO) (epsMsgM qMM R.qm R.qOm R.mlen) (epsUdF γu R.pU qUM) γu ≤
      nf (linT7 QP QM QF QT QW QU) (polyP7 Qc N qs ℓ) := by
  have e : nf (linT7 QP QM QF QT QW QU) (polyP7 Qc N qs ℓ) =
      nf QP ((Qc + N) ^ 2) + nf (2 * QM) ((Qc + qs * (ℓ + 1) + 2) ^ 2) +
      (nf 0 (4 * Qc + 2 * N + 3) + 3 * nf (QF + 1) (2 * Qc + N + 2)) +
      (nf (QT + 1) (2 * Qc + 42 * N + 2) + nf (QT + 1) (2 * Qc + 42 * N + 2) +
        nf (QT + 22) (18 * (2 * Qc + 22 * N + 21) ^ 2 + 2 * Qc + 42 * N + 1) +
        nf (QT + 10) (18 * (2 * Qc + 22 * N + 9) ^ 2 + 2 * Qc + 42 * N + 1)) +
      14 * nf QU (4 * Qc + 84 * N + 2 + (20 * N + 1)) + nf (2 * (QW + 1)) (2 * Qc + 42 * N + 2) +
      nf (QW + 1) (2 * Qc + 42 * N + 2) := by
    unfold nf polyP7 polyP linT7
    push_cast
    ring
  rw [e]
  unfold Realizers.epsL7
  gcongr
  · exact epsPrfM_le_t hP h.q h.qO
  · exact epsMsgM_le_t hM h.qm h.qOm h.mlen
  · exact epsDspr_le_t h.pD hD
  · exact epsForsTcr_le_t h.pT hT hT2
  · exact epsTcr_le_t h.pF hF hF2
  · exact epsTcr_le_t h.pH hH hH2
  · exact epsTcrLen_le_t h.pL hL hL2
  · exact epsTcrK_le_t h.pK hK hK2
  · exact epsUdF_le_t h.pU hU hU2
  · exact epsPre_le_t h.pP hR hR2
  · exact epsTcr_le_t h.pW hW hW2

end Bundle

section Legs

variable {S : ForgerI}
  {optRand : ∀ g : CF St Blk, PublicKeyCore (primsG (liftC g)).core → ProbComp (primsG (liftC g)).Y}
  {pkSeedDist : ProbComp (Bytes 16)}

/-- `suf_ideal_bound_legs` with the SM-UD leg as a hypothesis too. -/
theorem suf_ideal_bound_legs7 {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrSufI S optRand pkSeedDist ≤ εI)
    (R : SufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) {e₁ e₂ e₆ : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr
        (Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.prfIdealPr
        (Reduction.bPrfWC Reduction.sufCheck (S.typedS optRand pkSeedDist g))) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr
        (Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.msgIdealPr
        (Reduction.Lazy.bPrfMsgWL Reduction.sufCheck (S.typedS optRand pkSeedDist g))) + e₂)
    (h₆ : (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedS optRand pkSeedDist g)))) + e₆) :
    sufI S optRand pkSeedDist ≤ εI + R.epsL7 e₁ e₂ e₆ γ := by
  rw [sufI_eq_cfAvg]
  refine (ideal_bound_core_legs7 hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_suf_cma_linear (structuralG g) (S.sufInst optRand pkSeedDist g))
    hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK R.ud R.pre R.wotsTcr
    h₁ h₂ h₆).trans (le_of_eq ?_)
  unfold Realizers.epsL7
  ring

/-- `euf_ideal_bound_legs` with the SM-UD leg as a hypothesis too. -/
theorem euf_ideal_bound_legs7 {γ : ℝ≥0∞} (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    {εI : ℝ≥0∞} (hI : itsrEufI S optRand pkSeedDist ≤ εI)
    (R : EufRealizers S optRand pkSeedDist) (hD : R.pD.q₂ ≤ 2 ^ 126) {e₁ e₂ e₆ : ℝ≥0∞}
    (h₁ : (cfAvg fun g => Reduction.prfRealPr
        (Reduction.bPrfC (S.typedE optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.prfIdealPr
        (Reduction.bPrfC (S.typedE optRand pkSeedDist g))) + e₁)
    (h₂ : (cfAvg fun g => Reduction.msgRealPr
        (Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))) ≤
      (cfAvg fun g => Reduction.msgIdealPr
        (Reduction.Lazy.bPrfMsgL (S.typedE optRand pkSeedDist g))) + e₂)
    (h₆ : (cfAvg fun g => SM_DT_UD_RealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))) ≤
      (cfAvg fun g => SM_DT_UD_IdealSuccess (Reduction.rUd pkSeedDist
        (Reduction.Lazy.bWotsS (S.typedE optRand pkSeedDist g)))) + e₆) :
    eufI S optRand pkSeedDist ≤ εI + R.epsL7 e₁ e₂ e₆ γ := by
  rw [eufI_eq_cfAvg]
  refine (ideal_bound_core_legs7 hγ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun g => Reduction.slhdsa_bytes_euf_cma_linear (structuralG g) (S.eufInst optRand pkSeedDist g))
    hI R.prf R.msg R.dspr hD R.forsTcr R.tcrF R.tcrH R.tcrLen R.tcrK R.ud R.pre R.wotsTcr
    h₁ h₂ h₆).trans (le_of_eq ?_)
  unfold Realizers.epsL7
  ring

end Legs

/-! ## The coefficient -/

/-- **The `2^-128` coefficient with the SM-UD realiser's message blocks uncharged**: `27` per
forger compression query; per signing query `16944233` compressions of the reductions' own
hashing and `17` per message block (`31` before); one-off `29487867 + 17` per message block. -/
def QlinT7 (qf qs ℓ : ℕ) : ℕ :=
  27 * qf + qs * (16944233 + 17 * ((ℓ + 56) / 64)) + 29487867 + 17 * ((ℓ + 56) / 64)

/-- The SM-UD realiser's raw second-phase cap. -/
def QU (qf qs : ℕ) : ℕ := qf + 2 * (121857 * qs + 146514) + 9 * (3577 * qs + 146514)

theorem qMU_le_QU (qf qs : ℕ) : Wots.qMU qf qs ≤ QU qf qs := by
  have h1 := Wots.udH_le qs
  have h2 := Wots.udLg_le qs
  unfold Wots.qMU QU
  omega

theorem linT7_le_QlinT7 (qf qs ℓ : ℕ) :
    linT7 (qf + (qs + 1) * (32272 + 2 * ((ℓ + 56) / 64)))
      (qf + (qs + 1) * (39438 + (ℓ + 56) / 64))
      (qf + 544286 + 3932321 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3))
      (qf + (qs + 1) * (86419 + (ℓ + 56) / 64))
      (Wots.QcWL qf qs ℓ) (QU qf qs) ≤ QlinT7 qf qs ℓ := by
  unfold linT7 QlinT7 Wots.QcWL QU
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

/-- `QlinT7` is `QlinT6` minus the fourteen SM-UD copies of the `H_msg` cost `(qs+2)·(x+3)`. -/
theorem QlinT7_add (qf qs ℓ : ℕ) :
    QlinT7 qf qs ℓ + 14 * ((qs + 2) * ((ℓ + 56) / 64 + 3)) = QlinT6 qf qs ℓ := by
  unfold QlinT7 QlinT6
  generalize (ℓ + 56) / 64 = x
  ring

theorem QlinT7_le_QlinT6 (qf qs ℓ : ℕ) : QlinT7 qf qs ℓ ≤ QlinT6 qf qs ℓ := by
  have := QlinT7_add qf qs ℓ
  omega

section Tight7

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem sufRealizers7_epsL_le :
    (sufRealizers5 S oR hqf hqs hlong hout).epsL7
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ)
        (epsUdF γu (Wots.pUL qf qs ℓ) (Wots.qMU qf qs)) γu ≤
      nf (QlinT7 qf qs ℓ) (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((sufRealizers5 S oR hqf hqs hlong hout).epsL7_le_tight
    (sufRealizers5_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2ForsL_eq qf qs ℓ).le
    rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (qMU_le_QU qf qs) rfl (Wots.pPL_le qf qs ℓ).2.2.2.2
    rfl (Wots.pWL_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT7_le_QlinT7 qf qs ℓ) le_rfl)

theorem eufRealizers7_epsL_le :
    (eufRealizers5 S oR hqf hqs hlong hout).epsL7
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ)
        (epsUdF γu (Wots.pUL qf qs ℓ) (Wots.qMU qf qs)) γu ≤
      nf (QlinT7 qf qs ℓ) (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((eufRealizers5 S oR hqf hqs hlong hout).epsL7_le_tight
    (eufRealizers5_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2ForsL_eq qf qs ℓ).le
    rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (qMU_le_QU qf qs) rfl (Wots.pPL_le qf qs ℓ).2.2.2.2
    rfl (Wots.pWL_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT7_le_QlinT7 qf qs ℓ) le_rfl)

/-- The SUF bound from any bound `εI` on the ITSR term. -/
theorem suf_tight7_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrSufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT7 qf qs ℓ) (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (suf_ideal_bound_legs7 hγ_uniform hI (sufRealizers5 S oR hqf hqs hlong hout)
    ((sufRealizers5_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfSuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfSuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgSuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgSuf_mark S oR _ hqf hqs hlong hout))
    (udLeg_fine hγ_uniform hqf hqs hlong hout)).trans
    (add_le_add le_rfl (sufRealizers7_epsL_le S oR hqf hqs hlong hout))

/-- The EUF bound from any bound `εI` on the ITSR term. -/
theorem euf_tight7_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrEufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT7 qf qs ℓ) (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (euf_ideal_bound_legs7 hγ_uniform hI (eufRealizers5 S oR hqf hqs hlong hout)
    ((eufRealizers5_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfEuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfEuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgEuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgEuf_mark S oR _ hqf hqs hlong hout))
    (udLeg_fineE hγ_uniform hqf hqs hlong hout)).trans
    (add_le_add le_rfl (eufRealizers7_epsL_le S oR hqf hqs hlong hout))

end Tight7

/-! ## The headlines -/

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only, with
shape marking for `PRF`/`PRF_msg`, answer-storing class-TCR realisers, per-arity FORS and WOTS
counts, message blocks per signing query, and the SM-UD realiser's `H_msg` chains uncharged.**
Same hypotheses as `suf_ideal_closed`; the `2^-128` coefficient is
`QlinT7 qf qs ℓ = 27·qf + qs·(16944233 + 17·x) + 29487867 + 17·x` (`QlinT7_le_QlinT6`), the
`2^-256` part `polyP7 = polyP + 14·(20·NAll qs + 1)`. -/
theorem suf_ideal_closed_tight7 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT7 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact suf_tight7_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrSufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- **EUF-CMA analogue of `suf_ideal_closed_tight7`.** -/
theorem euf_ideal_closed_tight7 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT7 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact euf_tight7_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrEufI_le_optRandU S oR _ hqf hqs hlong hout)

theorem NAll_le_lin (qs : ℕ) : NAll qs ≤ 2 ^ 81 + 17920 + 182784 * qs :=
  max_le (by omega) (by rw [Prf.qOPrf_128s]; omega)

/-- The right-hand side of `suf_ideal_closed_tight7` is at most that of
`suf_ideal_closed_tight6`: the `2^-128` coefficient loses `14·(qs+2)·(x+3)`, the `2^-256` part
gains `14·(20·NAll qs + 1) ≤ 14·(qs+2)·(x+3)·2^128`. -/
theorem tight7_le_tight6 (qf qs ℓ : ℕ) :
    epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT7 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT6 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc, add_assoc]
  refine add_le_add le_rfl ?_
  rw [← QlinT7_add qf qs ℓ]
  unfold polyP7
  set a := QlinT7 qf qs ℓ
  set b := (qs + 2) * ((ℓ + 56) / 64 + 3)
  set P := polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)
  have hN : 20 * NAll qs + 1 ≤ b * 2 ^ 128 := by
    have h1 := NAll_le_lin qs
    have h2 : 2 * 3 ≤ b := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (qs + 2) * 3 ≤ b := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have e1 : ((2 : ℝ≥0∞) ^ 256) = 2 ^ 128 * 2 ^ 128 := by rw [← pow_add]
  have key : ((14 * (20 * NAll qs + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤
      ((14 * b : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
    rw [e1, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
      ENNReal.mul_inv (Or.inl (by positivity)) (Or.inl (by simp)), mul_assoc]
    gcongr
    rw [ENNReal.inv_mul_le_iff (by positivity) (by simp)]
    exact_mod_cast (show 14 * (20 * NAll qs + 1) ≤ 2 ^ 128 * (14 * b) by nlinarith)
  calc ((a : ℕ) : ℝ≥0∞) / 2 ^ 128 + ((P + 14 * (20 * NAll qs + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256
      = (a : ℝ≥0∞) / 2 ^ 128 + (P : ℝ≥0∞) / 2 ^ 256 +
          ((14 * (20 * NAll qs + 1) : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
        push_cast; rw [ENNReal.add_div]; ring
    _ ≤ (a : ℝ≥0∞) / 2 ^ 128 + (P : ℝ≥0∞) / 2 ^ 256 + ((14 * b : ℕ) : ℝ≥0∞) / 2 ^ 128 := by
        gcongr
    _ = _ := by push_cast; rw [ENNReal.add_div]; ring

/-! ## Numerics -/

theorem QlinT7_le {qf qs ℓ F₀ S₀ : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀) (hℓ : ℓ ≤ 2 ^ 26) :
    QlinT7 qf qs ℓ ≤ 27 * F₀ + S₀ * (16944233 + 17 * 2 ^ 20) + 29487867 + 17 * 2 ^ 20 := by
  have := div64_le_2_20 hℓ
  unfold QlinT7
  gcongr

theorem eleven_tight7_le {qf qs ℓ F₀ S₀ Qc₀ N₀ k m : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hnum : (27 * F₀ + S₀ * (16944233 + 17 * 2 ^ 20) + 29487867 + 17 * 2 ^ 20) * 2 ^ 128 +
      polyP7 Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m) :
    nf (QlinT7 qf qs ℓ) (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (nf_mono (QlinT7_le hf hs hℓ) (polyP7_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow k m hkm hnum)

theorem eleven_tight7_le2 {qf qs ℓ F₀ S₀ Qc₀ N₀ k m k' m' : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hkm' : m' + k' = 256)
    (hnum : (27 * F₀ + S₀ * (16944233 + 17 * 2 ^ 20) + 29487867 + 17 * 2 ^ 20) * 2 ^ 128 +
      polyP7 Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m + 2 ^ m') :
    nf (QlinT7 qf qs ℓ) (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤
      ((2 : ℝ≥0∞) ^ k)⁻¹ + ((2 : ℝ≥0∞) ^ k')⁻¹ :=
  (nf_mono (QlinT7_le hf hs hℓ) (polyP7_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow2 k m k' m' hkm hkm' hnum)

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD message blocks uncharged, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_closed_tight7_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (suf_tight7_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight7_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD message blocks uncharged, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-59`. -/
theorem suf_ideal_closed_tight7_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight7_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight7_le hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) rfl
      (by unfold polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD message blocks uncharged, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + (2^-39 + 2^-43)` (≈ `2^-38.91` for the last part). -/
theorem suf_ideal_closed_tight7_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 39)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight7_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight7_le2 hf hs hℓ hQc (NAll_le_82 hs) (k := 39) (m := 217) (k' := 43) (m' := 213)
      rfl rfl (by unfold polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD message blocks uncharged, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_closed_tight7_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (euf_tight7_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight7_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD message blocks uncharged, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-59`. -/
theorem euf_ideal_closed_tight7_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + ((2 : ℝ≥0∞) ^ 59)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight7_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight7_le hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) rfl
      (by unfold polyP7 polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, SM-UD message blocks uncharged, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + (2^-39 + 2^-43)` (≈ `2^-38.91` for the last part). -/
theorem euf_ideal_closed_tight7_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 39)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight7_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight7_le2 hf hs hℓ hQc (NAll_le_82 hs) (k := 39) (m := 217) (k' := 43) (m' := 213)
      rfl rfl (by unfold polyP7 polyP; norm_num)))


end Ideal

#print axioms Ideal.linT7_le_QlinT7
#print axioms Ideal.QlinT7_le_QlinT6
#print axioms Ideal.QlinT7_add
#print axioms Ideal.ideal_bound_core_legs7
#print axioms Ideal.Realizers.epsL7_le_tight
#print axioms Ideal.suf_ideal_closed_tight7
#print axioms Ideal.euf_ideal_closed_tight7
#print axioms Ideal.tight7_le_tight6
#print axioms Ideal.suf_ideal_closed_tight7_2_20
#print axioms Ideal.suf_ideal_closed_tight7_2_40
#print axioms Ideal.suf_ideal_closed_tight7_2_64
#print axioms Ideal.euf_ideal_closed_tight7_2_20
#print axioms Ideal.euf_ideal_closed_tight7_2_40
#print axioms Ideal.euf_ideal_closed_tight7_2_64
