import Ideal.Realize.PrfReal
import Ideal.Realize.Itsr
import Ideal.Realize.ForsRealize
import Ideal.Realize.TcrCount
import Ideal.ComposeFinal

/-!
# The composed ideal-model bound from the realisers (WOTS realisers as parameters)

Assembles the eleven realisers of `SufRealizers` / `EufRealizers` from the agents' files
(`PrfReal`, `MsgReal`, `ForsRealize`, `TcrCount`), with the three WOTS realisers (SM-UD, SM-PRE,
SM-TCR on `F`) as PARAMETERS, and the ITSR realiser of `Itsr.lean`; proves `R.Le` at the closed
caps `QcAll qf qs ℓ`, `NAll qs`, `qs`, `ellB ℓ`; and derives the composed bounds.

`Ideal/Realize/Final.lean` instantiates the WOTS parameters.

* `QcAll qf qs ℓ = qf + (qs+1)·(2^25 + 2·⌊(ℓ+56)/64⌋)`: covers the compression queries of all
  realisers (`qPrf_le'`, `qMsg_le'`, `q₂T_le`, `q2Fors_eq`; WOTS: by hypothesis);
* `NAll qs = max 2^81 (2^18·(qs+1))`: challenge / collection / PRF-oracle queries
  (`qOPrf_le`, `openPreTargets_eq`, `tcrP_128s_consts`; WOTS: by hypothesis);
* `ellB ℓ = ⌊(ℓ+63)/64⌋`: messages of at most `64·ellB ℓ` bytes.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

/-! ## Caps -/

/-- The cap on the compression queries of the eleven realisers. -/
def QcAll (qf qs ℓ : ℕ) : ℕ := qf + (qs + 1) * (2 ^ 25 + 2 * ((ℓ + 56) / 64))

/-- The cap on the challenge, collection and PRF-oracle queries: `2^81` (above the fixed
target counts of the FORS, class-TCR and WOTS games) or the PRF-oracle count. -/
def NAll (qs : ℕ) : ℕ := max (2 ^ 81) (Prf.qOPrf qs)

/-- Messages in 64-byte blocks. -/
def ellB (ℓ : ℕ) : ℕ := (ℓ + 63) / 64

theorem two81_le_NAll (qs : ℕ) : 2 ^ 81 ≤ NAll qs := le_max_left _ _

theorem P3Le_mono {p : P3} {Qc N Qc' N' : ℕ} (h : p.Le Qc N) (hQ : Qc ≤ Qc') (hN : N ≤ N') :
    p.Le Qc' N' :=
  ⟨h.1.trans hQ, h.2.1.trans hN, h.2.2.trans hQ⟩

theorem P5Le_mono {p : P5} {Qc N Qc' N' : ℕ} (h : p.Le Qc N) (hQ : Qc ≤ Qc') (hN : N ≤ N') :
    p.Le Qc' N' :=
  ⟨h.1.trans hQ, h.2.1.trans hN, h.2.2.1.trans hN, h.2.2.2.1, h.2.2.2.2.trans hQ⟩

section LeMono

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

/-- `Realizers.Le` at larger caps. -/
theorem RealizersLe_mono {R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈}
    {Qc N qs ℓ Qc' N' qs' ℓ' : ℕ} (h : R.Le Qc N qs ℓ) (hQ : Qc ≤ Qc') (hN : N ≤ N')
    (hs : qs ≤ qs') (hl : ℓ ≤ ℓ') : R.Le Qc' N' qs' ℓ' where
  q := h.q.trans hQ
  qO := h.qO.trans hN
  qm := h.qm.trans hQ
  qOm := h.qOm.trans hs
  mlen := h.mlen.trans (Nat.mul_le_mul_left _ hl)
  pD := P3Le_mono h.pD hQ hN
  pT := P3Le_mono h.pT hQ hN
  pF := P5Le_mono h.pF hQ hN
  pH := P5Le_mono h.pH hQ hN
  pL := P5Le_mono h.pL hQ hN
  pK := P5Le_mono h.pK hQ hN
  pU := P5Le_mono h.pU hQ hN
  pP := P5Le_mono h.pP hQ hN
  pW := P5Le_mono h.pW hQ hN

end LeMono

/-! ## Each realiser's parameters under the caps -/

theorem qPrf_le_QcAll (qf qs ℓ : ℕ) : Prf.qPrf qf qs ℓ ≤ QcAll qf qs ℓ := by
  refine (Prf.qPrf_le' qf qs ℓ).trans ?_
  unfold QcAll
  have : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

theorem qMsg_le_QcAll (qf qs ℓ : ℕ) : Msg.qMsg qf qs ℓ ≤ QcAll qf qs ℓ := by
  refine (Prf.qMsg_le' qf qs ℓ).trans ?_
  unfold QcAll
  have : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

theorem qOPrf_le_NAll (qs : ℕ) : Prf.qOPrf qs ≤ NAll qs := le_max_right _ _

theorem tcrP_le_all (qf qs ℓ : ℕ) : (Tcr.tcrP qf qs ℓ).Le (QcAll qf qs ℓ) (NAll qs) := by
  refine Tcr.tcrP_le_of qf qs ℓ _ _ ((Tcr.q₂T_le qf qs ℓ).trans ?_)
    (Tcr.tcrP_128s_consts.1.le.trans ((Nat.pow_le_pow_right (by norm_num) (by norm_num)).trans
      (two81_le_NAll qs)))
  unfold QcAll
  have : (2 : ℕ) ^ 25 = 33554432 := by norm_num
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _

theorem pFors_le_all (qf qs ℓ : ℕ) : (Fors.pFors qf qs ℓ).Le (QcAll qf qs ℓ) (NAll qs) := by
  refine Fors.pFors_le ?_ ((by norm_num : (528905046081400263933952 : ℕ) ≤ 2 ^ 81).trans
    (two81_le_NAll qs))
  unfold QcAll
  nlinarith [Nat.zero_le qs, Nat.zero_le ((ℓ + 56) / 64)]

/-! ## The realiser bundles (WOTS realisers as parameters) -/

section Bundle

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
  {pU pP pW : P5}

/-- The SUF bundle: eight realisers of the agents, the three WOTS ones given. -/
noncomputable def sufRealizersW
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pW) :
    SufRealizers S (optRandU oR) ($ᵗ (Bytes 16)) where
  q := Prf.qPrf qf qs ℓ
  qO := Prf.qOPrf qs
  qm := Msg.qMsg qf qs ℓ
  qOm := qs
  mlen := ℓ
  pD := Fors.pFors qf qs ℓ
  pT := Fors.pFors qf qs ℓ
  pF := Tcr.tcrP qf qs ℓ
  pH := Tcr.tcrP qf qs ℓ
  pL := Tcr.tcrP qf qs ℓ
  pK := Tcr.tcrP qf qs ℓ
  pU := pU
  pP := pP
  pW := pW
  prf := Prf.realizesPrfSuf S oR _ hqf hqs hlong hout
  msg := Msg.realizesMsgSuf S oR _ hqf hqs hlong hout
  dspr := Fors.realizesDspr_S S oR _ hqf hqs hlong hout
  forsTcr := Fors.realizesForsTcr_S S oR _ hqf hqs hlong hout
  tcrF := Tcr.realizesTcrF_S S oR _ hqf hqs hlong hout
  tcrH := Tcr.realizesTcrH_S S oR _ hqf hqs hlong hout
  tcrLen := Tcr.realizesTcrLen_S S oR _ hqf hqs hlong hout
  tcrK := Tcr.realizesTcrK_S S oR _ hqf hqs hlong hout
  ud := RU
  pre := RP
  wotsTcr := RW

/-- The EUF bundle. -/
noncomputable def eufRealizersW
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pW) :
    EufRealizers S (optRandU oR) ($ᵗ (Bytes 16)) where
  q := Prf.qPrf qf qs ℓ
  qO := Prf.qOPrf qs
  qm := Msg.qMsg qf qs ℓ
  qOm := qs
  mlen := ℓ
  pD := Fors.pFors qf qs ℓ
  pT := Fors.pFors qf qs ℓ
  pF := Tcr.tcrP qf qs ℓ
  pH := Tcr.tcrP qf qs ℓ
  pL := Tcr.tcrP qf qs ℓ
  pK := Tcr.tcrP qf qs ℓ
  pU := pU
  pP := pP
  pW := pW
  prf := Prf.realizesPrfEuf S oR _ hqf hqs hlong hout
  msg := Msg.realizesMsgEuf S oR _ hqf hqs hlong hout
  dspr := Fors.realizesDspr_E S oR _ hqf hqs hlong hout
  forsTcr := Fors.realizesForsTcr_E S oR _ hqf hqs hlong hout
  tcrF := Tcr.realizesTcrF_E S oR _ hqf hqs hlong hout
  tcrH := Tcr.realizesTcrH_E S oR _ hqf hqs hlong hout
  tcrLen := Tcr.realizesTcrLen_E S oR _ hqf hqs hlong hout
  tcrK := Tcr.realizesTcrK_E S oR _ hqf hqs hlong hout
  ud := RU
  pre := RP
  wotsTcr := RW

theorem sufRealizersW_le
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs)) :
    (sufRealizersW S oR hqf hqs hlong hout RU RP RW).Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) where
  q := qPrf_le_QcAll qf qs ℓ
  qO := qOPrf_le_NAll qs
  qm := qMsg_le_QcAll qf qs ℓ
  qOm := le_rfl
  mlen := by show ℓ ≤ 64 * ((ℓ + 63) / 64); omega
  pD := pFors_le_all qf qs ℓ
  pT := pFors_le_all qf qs ℓ
  pF := tcrP_le_all qf qs ℓ
  pH := tcrP_le_all qf qs ℓ
  pL := tcrP_le_all qf qs ℓ
  pK := tcrP_le_all qf qs ℓ
  pU := hU
  pP := hP
  pW := hW

theorem eufRealizersW_le
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs)) :
    (eufRealizersW S oR hqf hqs hlong hout RU RP RW).Le (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) where
  q := qPrf_le_QcAll qf qs ℓ
  qO := qOPrf_le_NAll qs
  qm := qMsg_le_QcAll qf qs ℓ
  qOm := le_rfl
  mlen := by show ℓ ≤ 64 * ((ℓ + 63) / 64); omega
  pD := pFors_le_all qf qs ℓ
  pT := pFors_le_all qf qs ℓ
  pF := tcrP_le_all qf qs ℓ
  pH := tcrP_le_all qf qs ℓ
  pL := tcrP_le_all qf qs ℓ
  pK := tcrP_le_all qf qs ℓ
  pU := hU
  pP := hP
  pW := hW

end Bundle

/-! ## Arithmetic of the caps at the numeric points -/

theorem QcAll_le_of {qf qs ℓ a b : ℕ} (hs : qs ≤ 2 ^ a) (hℓ : ℓ ≤ 2 ^ 26)
    (hb : qf + (2 ^ a + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ b) : QcAll qf qs ℓ ≤ b := by
  have h1 : (ℓ + 56) / 64 ≤ 2 ^ 20 := by
    have := Nat.div_le_div_right (c := 64) (Nat.add_le_add_right hℓ 56)
    have h2 : (2 ^ 26 + 56) / 64 = 2 ^ 20 := by norm_num
    omega
  refine le_trans ?_ hb
  unfold QcAll
  gcongr

theorem ellB_le {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ 26) : ellB ℓ ≤ 2 ^ 20 := by
  unfold ellB
  have := Nat.div_le_div_right (c := 64) (Nat.add_le_add_right hℓ 63)
  have h2 : (2 ^ 26 + 63) / 64 = 2 ^ 20 := by norm_num
  omega

theorem NAll_le_81 {qs : ℕ} (hs : qs ≤ 2 ^ 40) : NAll qs ≤ 2 ^ 81 :=
  max_le le_rfl (by
    rw [Prf.qOPrf_128s]
    calc 17920 + qs * 182784 ≤ 17920 + 2 ^ 40 * 182784 := by gcongr
      _ ≤ 2 ^ 81 := by norm_num)

theorem NAll_le_82 {qs : ℕ} (hs : qs ≤ 2 ^ 64) : NAll qs ≤ 2 ^ 82 :=
  max_le (by norm_num) (by
    rw [Prf.qOPrf_128s]
    calc 17920 + qs * 182784 ≤ 17920 + 2 ^ 64 * 182784 := by gcongr
      _ ≤ 2 ^ 82 := by norm_num)

/-! ## The composed bounds (WOTS realisers as parameters) -/

section Composed

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
  {pU pP pW : P5}

include hqf hqs hlong hout

/-- SUF composed bound, WOTS realisers given. -/
theorem suf_ideal_closed_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 :=
  Itsr.suf_final_optRandU_itsr S oR hqf hqs hlong hout
    (sufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (sufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW) hQ

/-- EUF composed bound, WOTS realisers given. -/
theorem euf_ideal_closed_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 :=
  Itsr.euf_final_optRandU_itsr S oR hqf hqs hlong hout
    (eufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (eufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW) hQ

/-- SUF at `qs ≤ 2^20`, `qf + 2^46 ≤ 2^60`, `ℓ ≤ 2^26`: `≤ 2^-70 + 2^-128 + 2^-61`. -/
theorem suf_closed_2_60_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  Itsr.suf_final_2_60_2_20_itsr S oR hqf hqs hlong hout ((Nat.le_add_right _ _).trans hf) hs hℓ
    (sufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (RealizersLe_mono (sufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW)
      (QcAll_le_of hs hℓ (by
        have : (2 ^ 20 + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ (2 : ℕ) ^ 46 := by norm_num
        exact (Nat.add_le_add_left this qf).trans hf))
      (NAll_le_81 (hs.trans (by norm_num))) hs (ellB_le hℓ))

/-- EUF at `qs ≤ 2^20`, `qf + 2^46 ≤ 2^60`, `ℓ ≤ 2^26`: `≤ 2^-70 + 2^-128 + 2^-61`. -/
theorem euf_closed_2_60_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹ :=
  Itsr.euf_final_2_60_2_20_itsr S oR hqf hqs hlong hout ((Nat.le_add_right _ _).trans hf) hs hℓ
    (eufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (RealizersLe_mono (eufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW)
      (QcAll_le_of hs hℓ (by
        have : (2 ^ 20 + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ (2 : ℕ) ^ 46 := by norm_num
        exact (Nat.add_le_add_left this qf).trans hf))
      (NAll_le_81 (hs.trans (by norm_num))) hs (ellB_le hℓ))

/-- SUF at `qs ≤ 2^40`, `qf ≤ 2^64`, `ℓ ≤ 2^26`: `≤ 2^-50 + 2^-88 + 2^-41`. -/
theorem suf_closed_2_80_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  suf_final_2_80_2_40 (Itsr.realizesItsrS_2_80_2_40 S oR _ hqf hqs hlong hout hf hs hℓ)
    (sufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (RealizersLe_mono (sufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW)
      (QcAll_le_of hs hℓ (by
        have : 2 ^ 64 + (2 ^ 40 + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ (2 : ℕ) ^ 80 := by norm_num
        exact (Nat.add_le_add_right hf _).trans this))
      (NAll_le_81 hs) hs (ellB_le hℓ))

/-- The ITSR realiser (EUF) at the parameters of `suf_final_2_80_2_40`. -/
noncomputable def realizesItsrE_2_80_2_40
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    RealizesItsrF (fun g => Reduction.Lazy.bItsrL (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))
      (2 ^ 64) (2 ^ 64) (2 ^ 80) (2 ^ 62) (2 ^ 21) (2 ^ 40) (2 ^ 26) :=
  Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) (by omega)
    (by rw [Itsr.itsrQc_eq]; nlinarith) (Itsr.itsrLc_le_2_21 hℓ) hs hℓ

/-- EUF at `qs ≤ 2^40`, `qf ≤ 2^64`, `ℓ ≤ 2^26`: `≤ 2^-50 + 2^-88 + 2^-41`. -/
theorem euf_closed_2_80_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 40) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 50)⁻¹ + ((2 : ℝ≥0∞) ^ 88)⁻¹ + ((2 : ℝ≥0∞) ^ 41)⁻¹ :=
  euf_ideal_bound_pow
    ((itsrEufI_le_fine S (optRandU oR) _
      (realizesItsrE_2_80_2_40 S oR hqf hqs hlong hout hf hs hℓ)).trans
      (add_le_add (reuseSum_63_12_14_le_big _ (by norm_num))
        (natMul_inv_pow_le _ _ _ (by norm_num))))
    (eufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (RealizersLe_mono (eufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW)
      (QcAll_le_of hs hℓ (by
        have : 2 ^ 64 + (2 ^ 40 + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ (2 : ℕ) ^ 80 := by norm_num
        exact (Nat.add_le_add_right hf _).trans this))
      (NAll_le_81 hs) hs (ellB_le hℓ) : Realizers.Le _ (2 ^ 80) (2 ^ 81) (2 ^ 40) (2 ^ 20))
    (by norm_num) 41 215 rfl num_2_80

/-- SUF at `qs ≤ 2^64`, `qf ≤ 2^64`, `ℓ ≤ 2^26` (`N = 2^82`): `≤ 2^-44 + 2^-43 + 2^-31`. -/
theorem suf_closed_2_90_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  suf_final_2_90_2_64 (Itsr.realizesItsrS_2_90_2_64 S oR _ hqf hqs hlong hout hf hs hℓ)
    (sufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (RealizersLe_mono (sufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW)
      (QcAll_le_of hs hℓ (by
        have : 2 ^ 64 + (2 ^ 64 + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ (2 : ℕ) ^ 90 := by norm_num
        exact (Nat.add_le_add_right hf _).trans this))
      (NAll_le_82 hs) hs (ellB_le hℓ))

/-- EUF at `qs ≤ 2^64`, `qf ≤ 2^64`, `ℓ ≤ 2^26` (`N = 2^82`): `≤ 2^-44 + 2^-43 + 2^-31`. -/
theorem euf_closed_2_90_W
    (RU : RealizesUd ($ᵗ (Bytes 16)) (fun g => Reduction.rUd ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pU)
    (RP : RealizesPre ($ᵗ (Bytes 16)) (fun g => Reduction.rPre ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pP)
    (RW : RealizesWotsTcr ($ᵗ (Bytes 16)) (fun g => Reduction.rTcrT ($ᵗ (Bytes 16))
      (Reduction.Lazy.bWotsS (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g))) pW)
    (hU : pU.Le (QcAll qf qs ℓ) (NAll qs)) (hP : pP.Le (QcAll qf qs ℓ) (NAll qs))
    (hW : pW.Le (QcAll qf qs ℓ) (NAll qs))
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 44)⁻¹ + ((2 : ℝ≥0∞) ^ 43)⁻¹ + ((2 : ℝ≥0∞) ^ 31)⁻¹ :=
  euf_final_2_90_2_64 (Itsr.realizesItsrE_2_90_2_64 S oR _ hqf hqs hlong hout hf hs hℓ)
    (eufRealizersW S oR hqf hqs hlong hout RU RP RW)
    (RealizersLe_mono (eufRealizersW_le S oR hqf hqs hlong hout RU RP RW hU hP hW)
      (QcAll_le_of hs hℓ (by
        have : 2 ^ 64 + (2 ^ 64 + 1) * (2 ^ 25 + 2 * 2 ^ 20) ≤ (2 : ℕ) ^ 90 := by norm_num
        exact (Nat.add_le_add_right hf _).trans this))
      (NAll_le_82 hs) hs (ellB_le hℓ))

end Composed

end Ideal

#print axioms Ideal.RealizersLe_mono
#print axioms Ideal.sufRealizersW
#print axioms Ideal.sufRealizersW_le
#print axioms Ideal.eufRealizersW_le
#print axioms Ideal.QcAll_le_of
#print axioms Ideal.suf_ideal_closed_W
#print axioms Ideal.euf_ideal_closed_W
#print axioms Ideal.suf_closed_2_60_W
#print axioms Ideal.euf_closed_2_60_W
#print axioms Ideal.suf_closed_2_80_W
#print axioms Ideal.euf_closed_2_80_W
#print axioms Ideal.suf_closed_2_90_W
#print axioms Ideal.euf_closed_2_90_W
