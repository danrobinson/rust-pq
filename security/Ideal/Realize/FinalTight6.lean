import Ideal.Realize.FinalTight5

/-!
# Sixth tightening: the message-block coefficient per signing query (`status/TIGHT.md` §8.5)

Pure arithmetic over the realisers of `FinalTight5.lean` (`sufRealizers5` / `eufRealizers5`,
unchanged): `QlinT5` charges `45` message-block compressions per signing query, but the
realisers' second phases issue per signing query only `31` `H_msg` chains in total (PRF 1+1,
PRF_msg 2·1, FORS 3·2, class TCR 4·1, WOTS 17·1; `45` is the one-off part, with the forgery and
the answer extraction).  `QlinT6` separates the two.

* `QlinT6 qf qs ℓ = 27·qf + qs·(16944275 + 31·x) + 29487951 + 45·x`, `x = ⌊(ℓ+56)/64⌋`
  (`linT_le_QlinT6`, `QlinT6_le_QlinT5`).
* `suf_ideal_closed_tight6`, `euf_ideal_closed_tight6`: same hypotheses as `suf_ideal_closed`.
* Numeric points (messages `≤ 2^26` bytes): `qs ≤ 2^20, qf ≤ 2^60`: `2^-77 + 2^-132 + 2^-63`;
  `qs ≤ 2^40, qf ≤ 2^64`: `2^-63 + 2^-94 + 2^-59`; `qs ≤ 2^64, qf ≤ 2^64`:
  `2^-45 + 2^-46 + (2^-39 + 2^-40)`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize



/-! ## The coefficient -/

/-- **The `2^-128` coefficient with the message blocks counted per signing query**: `27` per
forger compression query; per signing query `16944275` compressions of the reductions' own
hashing and `31` per message block; one-off `29487951 + 45` per message block. -/
def QlinT6 (qf qs ℓ : ℕ) : ℕ :=
  27 * qf + qs * (16944275 + 31 * ((ℓ + 56) / 64)) + 29487951 + 45 * ((ℓ + 56) / 64)

theorem linT_le_QlinT6 (qf qs ℓ : ℕ) :
    linT (qf + (qs + 1) * (32272 + 2 * ((ℓ + 56) / 64)))
      (qf + (qs + 1) * (39438 + (ℓ + 56) / 64))
      (qf + 544286 + 3932321 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3))
      (qf + (qs + 1) * (86419 + (ℓ + 56) / 64))
      (Wots.QcWL qf qs ℓ) ≤ QlinT6 qf qs ℓ := by
  unfold linT QlinT6 Wots.QcWL
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

/-- `QlinT6 ≤ QlinT5`: never worse than the bound of `suf_ideal_closed_tight5`. -/
theorem QlinT6_le_QlinT5 (qf qs ℓ : ℕ) : QlinT6 qf qs ℓ ≤ QlinT5 qf qs ℓ := by
  unfold QlinT6 QlinT5
  generalize (ℓ + 56) / 64 = x
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

section Tight6

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem sufRealizers6_epsL_le :
    (sufRealizers5 S oR hqf hqs hlong hout).epsL
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ) γu ≤
      nf (QlinT6 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((sufRealizers5 S oR hqf hqs hlong hout).epsL_le_tight
    (sufRealizers5_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2ForsL_eq qf qs ℓ).le
    rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Wots.pUL_le qf qs ℓ).2.2.2.2 rfl (Wots.pPL_le qf qs ℓ).2.2.2.2
    rfl (Wots.pWL_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT6 qf qs ℓ) le_rfl)

theorem eufRealizers6_epsL_le :
    (eufRealizers5 S oR hqf hqs hlong hout).epsL
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ) γu ≤
      nf (QlinT6 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((eufRealizers5 S oR hqf hqs hlong hout).epsL_le_tight
    (eufRealizers5_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2ForsL_eq qf qs ℓ).le
    rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Wots.pUL_le qf qs ℓ).2.2.2.2 rfl (Wots.pPL_le qf qs ℓ).2.2.2.2
    rfl (Wots.pWL_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT6 qf qs ℓ) le_rfl)

/-- The SUF bound from any bound `εI` on the ITSR term (round 4). -/
theorem suf_tight6_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrSufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT6 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (suf_ideal_bound_legs hγ_uniform hI (sufRealizers5 S oR hqf hqs hlong hout)
    ((sufRealizers5_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfSuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfSuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgSuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgSuf_mark S oR _ hqf hqs hlong hout))).trans
    (add_le_add le_rfl (sufRealizers6_epsL_le S oR hqf hqs hlong hout))

/-- The EUF bound from any bound `εI` on the ITSR term (round 4). -/
theorem euf_tight6_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrEufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT6 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (euf_ideal_bound_legs hγ_uniform hI (eufRealizers5 S oR hqf hqs hlong hout)
    ((eufRealizers5_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfEuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfEuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgEuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgEuf_mark S oR _ hqf hqs hlong hout))).trans
    (add_le_add le_rfl (eufRealizers6_epsL_le S oR hqf hqs hlong hout))

end Tight6

/-! ## The headlines -/

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only, with
shape marking for `PRF`/`PRF_msg`, answer-storing class-TCR realisers per-arity FORS
and WOTS counts, message blocks counted per signing query.**  Same hypotheses as
`suf_ideal_closed`; the `2^-128` coefficient is
`QlinT6 qf qs ℓ = 27·qf + qs·(16944275 + 31·x) + 29487951 + 45·x` (`QlinT6_le_QlinT5`). -/
theorem suf_ideal_closed_tight6 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT6 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact suf_tight6_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrSufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- **EUF-CMA analogue of `suf_ideal_closed_tight6`.** -/
theorem euf_ideal_closed_tight6 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT6 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact euf_tight6_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrEufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- The right-hand side of `suf_ideal_closed_tight6` is at most that of
`suf_ideal_closed_tight5`. -/
theorem tight6_le_tight5 (qf qs ℓ : ℕ) :
    epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT6 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT5 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  gcongr
  exact QlinT6_le_QlinT5 qf qs ℓ

/-! ## Numerics -/

theorem QlinT6_le {qf qs ℓ F₀ S₀ : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀) (hℓ : ℓ ≤ 2 ^ 26) :
    QlinT6 qf qs ℓ ≤ 27 * F₀ + S₀ * (16944275 + 31 * 2 ^ 20) + 29487951 + 45 * 2 ^ 20 := by
  have := div64_le_2_20 hℓ
  unfold QlinT6
  gcongr

theorem eleven_tight6_le {qf qs ℓ F₀ S₀ Qc₀ N₀ k m : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hnum : (27 * F₀ + S₀ * (16944275 + 31 * 2 ^ 20) + 29487951 + 45 * 2 ^ 20) * 2 ^ 128 +
      polyP Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m) :
    nf (QlinT6 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (nf_mono (QlinT6_le hf hs hℓ) (polyP_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow k m hkm hnum)

theorem eleven_tight6_le2 {qf qs ℓ F₀ S₀ Qc₀ N₀ k m k' m' : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hkm' : m' + k' = 256)
    (hnum : (27 * F₀ + S₀ * (16944275 + 31 * 2 ^ 20) + 29487951 + 45 * 2 ^ 20) * 2 ^ 128 +
      polyP Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m + 2 ^ m') :
    nf (QlinT6 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤
      ((2 : ℝ≥0∞) ^ k)⁻¹ + ((2 : ℝ≥0∞) ^ k')⁻¹ :=
  (nf_mono (QlinT6_le hf hs hℓ) (polyP_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow2 k m k' m' hkm hkm' hnum)

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_closed_tight6_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (suf_tight6_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight6_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-59`. -/
theorem suf_ideal_closed_tight6_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (suf_tight6_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight6_le hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) rfl
      (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + (2^-39 + 2^-40)` (≈ `2^-38.4` for the last part). -/
theorem suf_ideal_closed_tight6_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 39)⁻¹ + ((2 : ℝ≥0∞) ^ 40)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight6_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight6_le2 hf hs hℓ hQc (NAll_le_82 hs) (k := 39) (m := 217) (k' := 40) (m' := 216)
      rfl rfl (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_closed_tight6_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (euf_tight6_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight6_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + 2^-59`. -/
theorem euf_ideal_closed_tight6_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (euf_tight6_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight6_le hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) rfl
      (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, per-arity FORS and WOTS counts, message blocks per signing query, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + (2^-39 + 2^-40)` (≈ `2^-38.4` for the last part). -/
theorem euf_ideal_closed_tight6_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 39)⁻¹ + ((2 : ℝ≥0∞) ^ 40)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight6_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight6_le2 hf hs hℓ hQc (NAll_le_82 hs) (k := 39) (m := 217) (k' := 40) (m' := 216)
      rfl rfl (by unfold polyP; norm_num)))


end Ideal

#print axioms Ideal.linT_le_QlinT6
#print axioms Ideal.QlinT6_le_QlinT5
#print axioms Ideal.suf_ideal_closed_tight6
#print axioms Ideal.euf_ideal_closed_tight6
#print axioms Ideal.tight6_le_tight5
#print axioms Ideal.suf_ideal_closed_tight6_2_20
#print axioms Ideal.suf_ideal_closed_tight6_2_40
#print axioms Ideal.suf_ideal_closed_tight6_2_64
#print axioms Ideal.euf_ideal_closed_tight6_2_20
#print axioms Ideal.euf_ideal_closed_tight6_2_40
#print axioms Ideal.euf_ideal_closed_tight6_2_64
