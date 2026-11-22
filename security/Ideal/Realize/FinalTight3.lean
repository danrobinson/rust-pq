import Ideal.Realize.FinalTight2
import Ideal.Realize.TcrCount3

/-!
# Third tightening: answer-storing class-TCR realisers (`status/TIGHT.md` §8, steps 1–2)

`suf_ideal_closed_tight2` charges the four class-TCR games `4·(qf + (qs+1)·(25135729 + x))`
compression queries (`x = ⌊(ℓ+56)/64⌋`): every realiser recomputes the honest signatures.  The
answer-storing realisers `Tcr.realizesTcr3S` / `Tcr.realizesTcr3E` (`Ideal/Realize/Tcr3.lean`,
`TcrCount3.lean`) realise the SAME adversary families `bTcrArM n (S.typed… g)` by an ideal-model
adversary whose second phase answers key regeneration and signing from the challenger's stored
phase-one answers, and makes at most `q₂T3 qf qs ℓ = qf + 86416 + (qs+1)·(x+3)` compression
queries (`Tcr.q₂T3_128s`), for all four arities.

* `sufRealizers3` / `eufRealizers3`: the bundles of `Final.lean` with the four class-TCR
  realisers replaced; `…_le`: the same `R.Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)`.
* `QlinT3 qf qs ℓ = 27·qf + (qs+1)·(87595076 + 45·⌊(ℓ+56)/64⌋)` (`QlinT3_le_QlinT2`: never
  larger than `QlinT2`; the per-signature constant drops from `187792316`).
* `suf_ideal_closed_tight3`, `euf_ideal_closed_tight3`: same hypotheses as `suf_ideal_closed`.
* Numeric points (messages `≤ 2^26` bytes): `qs ≤ 2^20, qf ≤ 2^60`: `2^-77 + 2^-132 + 2^-63`;
  `qs ≤ 2^40, qf ≤ 2^64`: `2^-63 + 2^-94 + (2^-59 + 2^-62)`; `qs ≤ 2^64, qf ≤ 2^64`:
  `2^-45 + 2^-46 + (2^-37 + 2^-44)`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

theorem tcrP3_le_all (qf qs ℓ : ℕ) : (Tcr.tcrP3 qf qs ℓ).Le (QcAll qf qs ℓ) (NAll qs) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := tcrP_le_all qf qs ℓ
  exact ⟨h1, h2, h3, h4, (Tcr.q₂T3_le_q₂T qf qs ℓ).trans h5⟩

section Bundles3

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

/-- **The eleven SUF realisers, answer-storing class TCR.** -/
noncomputable def sufRealizers3 : SufRealizers S (optRandU oR) ($ᵗ (Bytes 16)) :=
  { sufRealizersU S oR hqf hqs hlong hout with
    pF := Tcr.tcrP3 qf qs ℓ, pH := Tcr.tcrP3 qf qs ℓ, pL := Tcr.tcrP3 qf qs ℓ,
    pK := Tcr.tcrP3 qf qs ℓ
    tcrF := Tcr.realizesTcr3S S oR _ 1 hqf hqs hlong hout
    tcrH := Tcr.realizesTcr3S S oR _ 2 hqf hqs hlong hout
    tcrLen := Tcr.realizesTcr3S S oR _ Link.vp.params.len hqf hqs hlong hout
    tcrK := Tcr.realizesTcr3S S oR _ Link.vp.params.k hqf hqs hlong hout }

/-- **The eleven EUF realisers, answer-storing class TCR.** -/
noncomputable def eufRealizers3 : EufRealizers S (optRandU oR) ($ᵗ (Bytes 16)) :=
  { eufRealizersU S oR hqf hqs hlong hout with
    pF := Tcr.tcrP3 qf qs ℓ, pH := Tcr.tcrP3 qf qs ℓ, pL := Tcr.tcrP3 qf qs ℓ,
    pK := Tcr.tcrP3 qf qs ℓ
    tcrF := Tcr.realizesTcr3E S oR _ 1 hqf hqs hlong hout
    tcrH := Tcr.realizesTcr3E S oR _ 2 hqf hqs hlong hout
    tcrLen := Tcr.realizesTcr3E S oR _ Link.vp.params.len hqf hqs hlong hout
    tcrK := Tcr.realizesTcr3E S oR _ Link.vp.params.k hqf hqs hlong hout }

theorem sufRealizers3_le :
    (sufRealizers3 S oR hqf hqs hlong hout).Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) :=
  have h := sufRealizersU_le S oR hqf hqs hlong hout
  ⟨h.q, h.qO, h.qm, h.qOm, h.mlen, h.pD, h.pT, tcrP3_le_all qf qs ℓ, tcrP3_le_all qf qs ℓ,
    tcrP3_le_all qf qs ℓ, tcrP3_le_all qf qs ℓ, h.pU, h.pP, h.pW⟩

theorem eufRealizers3_le :
    (eufRealizers3 S oR hqf hqs hlong hout).Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) :=
  have h := eufRealizersU_le S oR hqf hqs hlong hout
  ⟨h.q, h.qO, h.qm, h.qOm, h.mlen, h.pD, h.pT, tcrP3_le_all qf qs ℓ, tcrP3_le_all qf qs ℓ,
    tcrP3_le_all qf qs ℓ, tcrP3_le_all qf qs ℓ, h.pU, h.pP, h.pW⟩

end Bundles3

/-! ## The coefficient -/

/-- **The `2^-128` coefficient with answer-storing class-TCR realisers**: `27` per forger
compression query, and per signing query `87595076 ≈ 2^26.38` compression queries of the
remaining reductions' own hashing (FORS, WOTS) plus `45` per message block. -/
def QlinT3 (qf qs ℓ : ℕ) : ℕ := 27 * qf + (qs + 1) * (87595076 + 45 * ((ℓ + 56) / 64))

theorem linT_le_QlinT3 (qf qs ℓ : ℕ) :
    linT (qf + (qs + 1) * (32272 + 2 * ((ℓ + 56) / 64)))
      (qf + (qs + 1) * (39438 + (ℓ + 56) / 64))
      (qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3))
      (qf + (qs + 1) * (86419 + (ℓ + 56) / 64))
      (Wots.QcW qf qs ℓ) ≤ QlinT3 qf qs ℓ := by
  unfold linT QlinT3 Wots.QcW
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

/-- `QlinT3 ≤ QlinT2`: never worse than the bound of `suf_ideal_closed_tight2`. -/
theorem QlinT3_le_QlinT2 (qf qs ℓ : ℕ) : QlinT3 qf qs ℓ ≤ QlinT2 qf qs ℓ := by
  unfold QlinT3 QlinT2
  generalize (ℓ + 56) / 64 = x
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

section Tight3

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem sufRealizers3_epsL_le :
    (sufRealizers3 S oR hqf hqs hlong hout).epsL
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ) γu ≤
      nf (QlinT3 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((sufRealizers3 S oR hqf hqs hlong hout).epsL_le_tight
    (sufRealizers3_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2Fors_eq qf qs ℓ).le
    rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Wots.pU_le qf qs ℓ).2.2.2.2 rfl (Wots.pP_le qf qs ℓ).2.2.2.2
    rfl (Wots.pW_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT3 qf qs ℓ) le_rfl)

theorem eufRealizers3_epsL_le :
    (eufRealizers3 S oR hqf hqs hlong hout).epsL
        (epsPrfM (Prf.qPrfM qf qs ℓ) (Prf.qPrf qf qs ℓ) (Prf.qOPrf qs))
        (epsMsgM (Msg.qMsgM qf qs ℓ) (Msg.qMsg qf qs ℓ) qs ℓ) γu ≤
      nf (QlinT3 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((eufRealizers3 S oR hqf hqs hlong hout).epsL_le_tight
    (eufRealizers3_le S oR hqf hqs hlong hout)
    (Prf.qPrfM_le qf qs ℓ) (Msg.qMsgM_le qf qs ℓ) rfl rfl (Fors.q2Fors_eq qf qs ℓ).le
    rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ) rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Tcr.q₂T3_le qf qs ℓ)
    rfl (Wots.pU_le qf qs ℓ).2.2.2.2 rfl (Wots.pP_le qf qs ℓ).2.2.2.2
    rfl (Wots.pW_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT3 qf qs ℓ) le_rfl)

/-- The SUF bound from any bound `εI` on the ITSR term, answer-storing class TCR. -/
theorem suf_tight3_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrSufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT3 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (suf_ideal_bound_legs hγ_uniform hI (sufRealizers3 S oR hqf hqs hlong hout)
    ((sufRealizers3_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfSuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfSuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgSuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgSuf_mark S oR _ hqf hqs hlong hout))).trans
    (add_le_add le_rfl (sufRealizers3_epsL_le S oR hqf hqs hlong hout))

/-- The EUF bound from any bound `εI` on the ITSR term, answer-storing class TCR. -/
theorem euf_tight3_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrEufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT3 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (euf_ideal_bound_legs hγ_uniform hI (eufRealizers3 S oR hqf hqs hlong hout)
    ((eufRealizers3_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)
    ((Prf.realizesPrfEuf S oR _ hqf hqs hlong hout).boundM
      (Prf.realizesPrfEuf_mark S oR _ hqf hqs hlong hout))
    ((Msg.realizesMsgEuf S oR _ hqf hqs hlong hout).boundM
      (Msg.realizesMsgEuf_mark S oR _ hqf hqs hlong hout))).trans
    (add_le_add le_rfl (eufRealizers3_epsL_le S oR hqf hqs hlong hout))

end Tight3

/-! ## The headlines -/

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only, with
shape marking for `PRF`/`PRF_msg` and answer-storing class-TCR realisers.**  Same hypotheses as
`suf_ideal_closed`; the `2^-128` coefficient is
`QlinT3 qf qs ℓ = 27·qf + (qs+1)·(87595076 + 45·⌊(ℓ+56)/64⌋)` (`QlinT3_le_QlinT2`). -/
theorem suf_ideal_closed_tight3 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT3 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact suf_tight3_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrSufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- **EUF-CMA analogue of `suf_ideal_closed_tight3`.** -/
theorem euf_ideal_closed_tight3 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT3 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact euf_tight3_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrEufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- The right-hand side of `suf_ideal_closed_tight3` is at most that of
`suf_ideal_closed_tight2`. -/
theorem tight3_le_tight2 (qf qs ℓ : ℕ) :
    epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT3 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT2 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  gcongr
  exact QlinT3_le_QlinT2 qf qs ℓ

/-! ## Numerics -/

/-- `a / 2^128 + b / 2^256 ≤ 2^-k + 2^-k'` as soon as `a · 2^128 + b ≤ 2^(256-k) + 2^(256-k')`. -/
theorem nf_le_inv_pow2 {a b : ℕ} (k m k' m' : ℕ) (hkm : m + k = 256) (hkm' : m' + k' = 256)
    (h : a * 2 ^ 128 + b ≤ 2 ^ m + 2 ^ m') :
    nf a b ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ + ((2 : ℝ≥0∞) ^ k')⁻¹ := by
  have e1 : nf a b = ((a * 2 ^ 128 + b : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    unfold nf
    rw [inv_pow_split 128 128]
    push_cast
    ring
  rw [e1, inv_pow_split m k, inv_pow_split m' k', hkm, hkm', ← add_mul]
  have h' : ((a * 2 ^ 128 + b : ℕ) : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ m + (2 : ℝ≥0∞) ^ m' := by
    have := Nat.cast_le (α := ℝ≥0∞) |>.mpr h
    simpa using this
  exact mul_le_mul_left h' _

theorem QlinT3_le {qf qs ℓ F₀ S₀ : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀) (hℓ : ℓ ≤ 2 ^ 26) :
    QlinT3 qf qs ℓ ≤ 27 * F₀ + (S₀ + 1) * (87595076 + 45 * 2 ^ 20) := by
  have := div64_le_2_20 hℓ
  unfold QlinT3
  gcongr

theorem eleven_tight3_le {qf qs ℓ F₀ S₀ Qc₀ N₀ k m : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hnum : (27 * F₀ + (S₀ + 1) * (87595076 + 45 * 2 ^ 20)) * 2 ^ 128 +
      polyP Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m) :
    nf (QlinT3 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (nf_mono (QlinT3_le hf hs hℓ) (polyP_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow k m hkm hnum)

theorem eleven_tight3_le2 {qf qs ℓ F₀ S₀ Qc₀ N₀ k m k' m' : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hkm' : m' + k' = 256)
    (hnum : (27 * F₀ + (S₀ + 1) * (87595076 + 45 * 2 ^ 20)) * 2 ^ 128 +
      polyP Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m + 2 ^ m') :
    nf (QlinT3 qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤
      ((2 : ℝ≥0∞) ^ k)⁻¹ + ((2 : ℝ≥0∞) ^ k')⁻¹ :=
  (nf_mono (QlinT3_le hf hs hℓ) (polyP_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow2 k m k' m' hkm hkm' hnum)

/-- SUF/EUF, answer-storing class TCR, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_closed_tight3_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (suf_tight3_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight3_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + (2^-59 + 2^-62)` (≈ `2^-58.8` for the last part). -/
theorem suf_ideal_closed_tight3_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + (((2 : ℝ≥0∞) ^ 59)⁻¹ + ((2 : ℝ≥0∞) ^ 62)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight3_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight3_le2 hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) (k' := 62) (m' := 194)
      rfl rfl (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + (2^-37 + 2^-44)` (≈ `2^-37.0` for the last part; was `2^-36`). -/
theorem suf_ideal_closed_tight3_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 37)⁻¹ + ((2 : ℝ≥0∞) ^ 44)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight3_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight3_le2 hf hs hℓ hQc (NAll_le_82 hs) (k := 37) (m := 219) (k' := 44) (m' := 212)
      rfl rfl (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, at `qs ≤ 2 ^ 20`, `qf ≤ 2 ^ 60`, messages `≤ 2^26` bytes: `2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_closed_tight3_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (euf_tight3_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight3_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, at `qs ≤ 2 ^ 40`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-63 + 2^-94 + (2^-59 + 2^-62)` (≈ `2^-58.8` for the last part). -/
theorem euf_ideal_closed_tight3_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ + (((2 : ℝ≥0∞) ^ 59)⁻¹ + ((2 : ℝ≥0∞) ^ 62)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 66 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight3_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight3_le2 hf hs hℓ hQc (NAll_le_81 hs) (k := 59) (m := 197) (k' := 62) (m' := 194)
      rfl rfl (by unfold polyP; norm_num)))

/-- SUF/EUF, answer-storing class TCR, at `qs ≤ 2 ^ 64`, `qf ≤ 2 ^ 64`, messages `≤ 2^26` bytes: `2^-45 + 2^-46 + (2^-37 + 2^-44)` (≈ `2^-37.0` for the last part; was `2^-36`). -/
theorem euf_ideal_closed_tight3_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + (((2 : ℝ≥0∞) ^ 37)⁻¹ + ((2 : ℝ≥0∞) ^ 44)⁻¹) := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight3_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight3_le2 hf hs hℓ hQc (NAll_le_82 hs) (k := 37) (m := 219) (k' := 44) (m' := 212)
      rfl rfl (by unfold polyP; norm_num)))


end Ideal

#print axioms Ideal.tcrP3_le_all
#print axioms Ideal.sufRealizers3_le
#print axioms Ideal.eufRealizers3_le
#print axioms Ideal.linT_le_QlinT3
#print axioms Ideal.QlinT3_le_QlinT2
#print axioms Ideal.suf_ideal_closed_tight3
#print axioms Ideal.euf_ideal_closed_tight3
#print axioms Ideal.tight3_le_tight2
#print axioms Ideal.suf_ideal_closed_tight3_2_20
#print axioms Ideal.suf_ideal_closed_tight3_2_40
#print axioms Ideal.suf_ideal_closed_tight3_2_64
#print axioms Ideal.euf_ideal_closed_tight3_2_20
#print axioms Ideal.euf_ideal_closed_tight3_2_40
#print axioms Ideal.euf_ideal_closed_tight3_2_64
