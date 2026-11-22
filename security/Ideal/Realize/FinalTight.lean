import Ideal.Realize.Final

/-!
# A tighter closed ideal-compression bound for SLH-DSA-SHA2-128s

`suf_ideal_closed` / `euf_ideal_closed` (`Ideal/Realize/Final.lean`) bound the eleven non-ITSR
games through ONE cap `QcAll qf qs ℓ` on the compression queries of all realisers, with the
coefficient `66` of `Realizers.eps_le` (`Ideal/Compose128.lean`).  That coefficient contains
`2·q₁`/`q₁` terms (first-phase queries), and every realiser of `Final.lean` has `q₁ = 0`; and
`QcAll` charges every realiser the per-signature count of the largest one (class TCR, `≈ 2^24.6`
compressions per signature), while the three WOTS realisers make `≈ 2^20.4`.

Here the same proved realisers are evaluated term by term (`Realizers.eps_le_tight`), with each
realiser's own second-phase count.  Nothing about the realisers, the games or the forger is new;
this is arithmetic on proved statements.

* `QlinT qf qs ℓ = 27·qf + (qs+1)·(253924886 + 45·⌊(ℓ+56)/64⌋)` replaces
  `66·QcAll qf qs ℓ + 40 = 66·qf + (qs+1)·(66·2^25 + 132·⌊(ℓ+56)/64⌋) + 40`;
  the `2^-256` term and the ITSR term are unchanged.
* `suf_ideal_closed_tight`, `euf_ideal_closed_tight`: same hypotheses as `suf_ideal_closed`.
* Numeric points at the three settings of `Final.lean` (messages `≤ 2^26` bytes), with the
  ITSR term evaluated at the actual counts instead of rounded caps:
  - `qs ≤ 2^20`, `qf ≤ 2^60` (weaker than `qf + 2^46 ≤ 2^60`): `2^-77 + 2^-132 + 2^-63`
    (was `2^-70 + 2^-128 + 2^-61`);
  - `qs ≤ 2^40`, `qf ≤ 2^64`: `2^-63 + 2^-94 + 2^-58` (was `2^-50 + 2^-88 + 2^-41`);
  - `qs ≤ 2^64`, `qf ≤ 2^64`: `2^-45 + 2^-46 + 2^-35` (was `2^-44 + 2^-43 + 2^-31`).

Loss budget and what remains loose: `status/TIGHT.md`.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal TweakableHash

namespace Ideal

open Ideal.Realize

/-! ## Per-term bounds when the realiser makes no first-phase compression query -/

theorem epsPrf_le_t {q qO Q Qc N : ℕ} (hq : q ≤ Q) (hq' : q ≤ Qc) (hO : qO ≤ N) :
    epsPrf q qO ≤ nf Q ((Qc + N) ^ 2) := by
  have e : epsPrf q qO = nf q ((q + qO) ^ 2) := by
    unfold epsPrf nf
    simp only [div_eq_mul_inv]
  rw [e]
  exact nf_mono hq (Nat.pow_le_pow_left (by omega) 2)

theorem epsMsg_le_t {q qO mlen Q Qc qs ℓ : ℕ} (hq : q ≤ Q) (hq' : q ≤ Qc) (hO : qO ≤ qs)
    (hm : mlen ≤ 64 * ℓ) :
    epsMsg q qO mlen ≤ nf (2 * Q) ((Qc + qs * (ℓ + 1) + 2) ^ 2) := by
  have e : epsMsg q qO mlen = nf (2 * q) ((q + qO * ((mlen + 24) / 64 + 1) + 2) ^ 2) := by
    unfold epsMsg nf
    simp only [div_eq_mul_inv]
    push_cast
    ring
  rw [e]
  have h1 : qO * ((mlen + 24) / 64 + 1) ≤ qs * (ℓ + 1) := Nat.mul_le_mul hO (by omega)
  exact nf_mono (by omega) (Nat.pow_le_pow_left (by omega) 2)

theorem epsDspr_le_t {p : P3} {Qc N : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) :
    epsDspr γu p ≤ nf 0 (4 * Qc + 2 * N + 3) := by
  obtain ⟨h1, h2, _⟩ := h
  have e : epsDspr γu p = nf (2 * p.q₁) (4 * p.q₁ + 2 * p.qch + 3) := by
    unfold epsDspr nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsForsTcr_le_t {p : P3} {Qc N Q : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0)
    (hQ : p.q₂ ≤ Q) : epsForsTcr γu p ≤ nf (Q + 1) (2 * Qc + N + 2) := by
  obtain ⟨h1, h2, _⟩ := h
  have e : epsForsTcr γu p = nf (p.q₂ + 1 + p.q₁) (2 * p.q₁ + p.qch + 2) := by
    unfold epsForsTcr nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsTcr_le_t {p : P5} {Qc N Q : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : p.q₂ ≤ Q) :
    epsTcr γu p ≤ nf (Q + 1) (2 * Qc + 42 * N + 2) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcr γu p =
      nf (p.q₂ + 1 + p.q₁) (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2) := by
    unfold epsTcr nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsTcrLen_le_t {p : P5} {Qc N Q : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : p.q₂ ≤ Q) :
    epsTcrLen γu p ≤
      nf (Q + 22) (18 * (2 * Qc + 22 * N + 21) ^ 2 + 2 * Qc + 42 * N + 1) := by
  have hc1 := coll_le h (1 + max 9 p.L) 11 (by have := h.2.2.2.1; omega)
  have hc2 := coll_le h (1 + 2 * max 9 p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcrLen γu p = nf (p.q₂ + 22 + p.q₁)
      (18 * (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 9 p.L) + 21) ^ 2 + 2 * p.q₁ +
        (p.qch + p.qc) * (1 + 2 * max 9 p.L) + 1) := by
    unfold epsTcrLen nf
    push_cast
    ring
  rw [e]
  have hsq : (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 9 p.L) + 21) ^ 2 ≤
      (2 * Qc + 22 * N + 21) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact nf_mono (by omega) (by linarith)

theorem epsTcrK_le_t {p : P5} {Qc N Q : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : p.q₂ ≤ Q) :
    epsTcrK γu p ≤
      nf (Q + 10) (18 * (2 * Qc + 22 * N + 9) ^ 2 + 2 * Qc + 42 * N + 1) := by
  have hc1 := coll_le h (1 + max 3 p.L) 11 (by have := h.2.2.2.1; omega)
  have hc2 := coll_le h (1 + 2 * max 3 p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsTcrK γu p = nf (p.q₂ + 10 + p.q₁)
      (18 * (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 3 p.L) + 9) ^ 2 + 2 * p.q₁ +
        (p.qch + p.qc) * (1 + 2 * max 3 p.L) + 1) := by
    unfold epsTcrK nf
    push_cast
    ring
  rw [e]
  have hsq : (p.q₁ + p.q₂ + (p.qch + p.qc) * (1 + max 3 p.L) + 9) ^ 2 ≤
      (2 * Qc + 22 * N + 9) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  exact nf_mono (by omega) (by linarith)

theorem epsUd_le_t {p : P5} {Qc N Q : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : p.q₂ ≤ Q) :
    epsUd γu p ≤ nf Q (4 * Qc + 84 * N + 2) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsUd γu p =
      nf (p.q₂ + 2 * p.q₁) (2 * (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 1)) := by
    unfold epsUd nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

theorem epsPre_le_t {p : P5} {Qc N Q : ℕ} (h : p.Le Qc N) (h0 : p.q₁ = 0) (hQ : p.q₂ ≤ Q) :
    epsPre γu p ≤ nf (2 * (Q + 1)) (2 * Qc + 42 * N + 2) := by
  have hc := coll_le h (1 + 2 * p.L) 21 (by have := h.2.2.2.1; omega)
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have e : epsPre γu p =
      nf (2 * (p.q₂ + 1) + p.q₁) (2 * p.q₁ + (p.qch + p.qc) * (1 + 2 * p.L) + 2) := by
    unfold epsPre nf
    push_cast
    ring
  rw [e]
  exact nf_mono (by omega) (by omega)

/-! ## The eleven terms, realiser by realiser -/

/-- The `2^-128` coefficient of the eleven terms when no realiser makes a first-phase query:
`QP` (PRF), `QM` (PRF_msg), `QF` (FORS), `QT` (class TCR, four arities), `QW` (WOTS UD, PRE,
TCR) are the second-phase caps. -/
def linT (QP QM QF QT QW : ℕ) : ℕ := QP + 2 * QM + 3 * QF + 4 * QT + 17 * QW + 40

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

/-- **The eleven explicit bounds, term by term.**  Under the uniform caps `R.Le Qc N qs ℓ` (used
only in the `2^-256` part) and per-realiser second-phase caps with no first-phase queries, the
`2^-128` coefficient is `linT QP QM QF QT QW` instead of `66·Qc + 40`. -/
theorem Realizers.eps_le_tight (R : Realizers pkSeedDist B₁ B₂ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈)
    {Qc N qs ℓ QP QM QF QT QW : ℕ} (h : R.Le Qc N qs ℓ)
    (hP : R.q ≤ QP) (hM : R.qm ≤ QM)
    (hD : R.pD.q₁ = 0) (hT : R.pT.q₁ = 0) (hT2 : R.pT.q₂ ≤ QF)
    (hF : R.pF.q₁ = 0) (hF2 : R.pF.q₂ ≤ QT) (hH : R.pH.q₁ = 0) (hH2 : R.pH.q₂ ≤ QT)
    (hL : R.pL.q₁ = 0) (hL2 : R.pL.q₂ ≤ QT) (hK : R.pK.q₁ = 0) (hK2 : R.pK.q₂ ≤ QT)
    (hU : R.pU.q₁ = 0) (hU2 : R.pU.q₂ ≤ QW) (hR : R.pP.q₁ = 0) (hR2 : R.pP.q₂ ≤ QW)
    (hW : R.pW.q₁ = 0) (hW2 : R.pW.q₂ ≤ QW) :
    R.eps γu ≤ nf (linT QP QM QF QT QW) (polyP Qc N qs ℓ) := by
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
  unfold Realizers.eps
  gcongr
  · exact epsPrf_le_t hP h.q h.qO
  · exact epsMsg_le_t hM h.qm h.qOm h.mlen
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

/-! ## The tight coefficient at the realisers of `Final.lean` -/

/-- **The tight `2^-128` coefficient**: `27` per forger compression query, and per signing
query `253924886 ≈ 2^27.92` compression queries of the reductions' own hashing (summed over the
eleven realisers with their multiplicities) plus `45` per message block. -/
def QlinT (qf qs ℓ : ℕ) : ℕ := 27 * qf + (qs + 1) * (253924886 + 45 * ((ℓ + 56) / 64))

theorem linT_le_QlinT (qf qs ℓ : ℕ) :
    linT (qf + (qs + 1) * (22081242 + 2 * ((ℓ + 56) / 64)))
      (qf + (qs + 1) * (22081238 + (ℓ + 56) / 64))
      (qf + 2968229 + 21450308 * qs + (2 * qs + 1) * ((ℓ + 56) / 64 + 3))
      (qf + (qs + 1) * (25135729 + (ℓ + 56) / 64))
      (Wots.QcW qf qs ℓ) ≤ QlinT qf qs ℓ := by
  unfold linT QlinT Wots.QcW
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs]

/-- `QlinT ≤ 66·QcAll + 40`: the tight coefficient is never worse than the old one. -/
theorem QlinT_le_old (qf qs ℓ : ℕ) : QlinT qf qs ℓ ≤ 66 * QcAll qf qs ℓ + 40 := by
  unfold QlinT QcAll
  generalize (ℓ + 56) / 64 = x
  ring_nf
  nlinarith [Nat.zero_le (qs * x), Nat.zero_le x, Nat.zero_le qs, Nat.zero_le qf]

section Tight

variable (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
  (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
  (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
  (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
  (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)

include hqf hqs hlong hout

theorem sufRealizersU_eps_le :
    (sufRealizersU S oR hqf hqs hlong hout).eps γu ≤
      nf (QlinT qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((sufRealizersU S oR hqf hqs hlong hout).eps_le_tight
    (sufRealizersU_le S oR hqf hqs hlong hout)
    (Prf.qPrf_le' qf qs ℓ) (Prf.qMsg_le' qf qs ℓ) rfl rfl (Fors.q2Fors_eq qf qs ℓ).le
    rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Wots.pU_le qf qs ℓ).2.2.2.2 rfl (Wots.pP_le qf qs ℓ).2.2.2.2
    rfl (Wots.pW_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT qf qs ℓ) le_rfl)

theorem eufRealizersU_eps_le :
    (eufRealizersU S oR hqf hqs hlong hout).eps γu ≤
      nf (QlinT qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  ((eufRealizersU S oR hqf hqs hlong hout).eps_le_tight
    (eufRealizersU_le S oR hqf hqs hlong hout)
    (Prf.qPrf_le' qf qs ℓ) (Prf.qMsg_le' qf qs ℓ) rfl rfl (Fors.q2Fors_eq qf qs ℓ).le
    rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ) rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Tcr.q₂T_le qf qs ℓ)
    rfl (Wots.pU_le qf qs ℓ).2.2.2.2 rfl (Wots.pP_le qf qs ℓ).2.2.2.2
    rfl (Wots.pW_le qf qs ℓ).2.2.2.2).trans
    (nf_mono (linT_le_QlinT qf qs ℓ) le_rfl)

/-- The SUF bound from any bound `εI` on the ITSR term. -/
theorem suf_tight_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrSufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (suf_ideal_bound' hγ_uniform hI (sufRealizersU S oR hqf hqs hlong hout)
    ((sufRealizersU_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)).trans
    (add_le_add le_rfl (sufRealizersU_eps_le S oR hqf hqs hlong hout))

/-- The EUF bound from any bound `εI` on the ITSR term. -/
theorem euf_tight_of (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) {εI : ℝ≥0∞}
    (hI : itsrEufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ εI) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      εI + nf (QlinT qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) :=
  (euf_ideal_bound' hγ_uniform hI (eufRealizersU S oR hqf hqs hlong hout)
    ((eufRealizersU_le S oR hqf hqs hlong hout).pD.2.2.trans hQ)).trans
    (add_le_add le_rfl (eufRealizersU_eps_le S oR hqf hqs hlong hout))

end Tight

/-! ## The tight headlines -/

/-- **SUF-CMA of SLH-DSA-SHA2-128s in the ideal-compression model, forger caps only, tight
form.**  Same hypotheses as `suf_ideal_closed`; the `2^-128` coefficient `66·QcAll qf qs ℓ + 40`
is replaced by `QlinT qf qs ℓ = 27·qf + (qs+1)·(253924886 + 45·⌊(ℓ+56)/64⌋)`
(`QlinT_le_old`: never larger). -/
theorem suf_ideal_closed_tight (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact suf_tight_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrSufI_le_optRandU S oR _ hqf hqs hlong hout)

/-- **EUF-CMA analogue of `suf_ideal_closed_tight`.** -/
theorem euf_ideal_closed_tight (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256 := by
  rw [add_assoc]
  exact euf_tight_of S oR hqf hqs hlong hout hQ
    (Itsr.itsrEufI_le_optRandU S oR _ hqf hqs hlong hout)

/-! ## Numerics -/

/-- `reuseSum_63_12_14_le_of` with `n` measured in units of `2^(63-d)`: if `n ≤ r·2^(63-d)` and
`r·2^(63-d)·∏_{i<14}(i·2^d + r)·2^c ≤ 2^168·2^(14d)`, the coverage sum is at most `2^-c`. -/
theorem reuseSum_63_12_14_le_frac (n r d c : ℕ) (hd : d ≤ 63) (hn : n ≤ r * 2 ^ (63 - d))
    (hc : r * 2 ^ (63 - d) * (∏ i ∈ Finset.range 14, (i * 2 ^ d + r)) * 2 ^ c ≤
      2 ^ 168 * 2 ^ (14 * d)) :
    reuseSum 63 12 14 n ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := by
  have hA0 : (2 : ℝ≥0∞) ^ (63 - d) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hAt : (2 : ℝ≥0∞) ^ (63 - d) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have hB0 : (2 : ℝ≥0∞) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
  have hBt : (2 : ℝ≥0∞) ^ d ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h63 : ((2 : ℝ≥0∞) ^ 63)⁻¹ = ((2 : ℝ≥0∞) ^ (63 - d))⁻¹ * ((2 : ℝ≥0∞) ^ d)⁻¹ := by
    rw [← ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt), ← pow_add, Nat.sub_add_cancel hd]
  have hn' : (n : ℝ≥0∞) ≤ (r : ℝ≥0∞) * 2 ^ (63 - d) := by exact_mod_cast hn
  have hρ : (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 63)⁻¹ ≤ r * ((2 : ℝ≥0∞) ^ d)⁻¹ := by
    rw [h63]
    calc (n : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ (63 - d))⁻¹ * ((2 : ℝ≥0∞) ^ d)⁻¹)
        ≤ (r : ℝ≥0∞) * 2 ^ (63 - d) * (((2 : ℝ≥0∞) ^ (63 - d))⁻¹ * ((2 : ℝ≥0∞) ^ d)⁻¹) :=
          mul_le_mul hn' le_rfl zero_le zero_le
      _ = r * ((2 : ℝ≥0∞) ^ d)⁻¹ := by
          rw [mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ (63 - d)), ENNReal.mul_inv_cancel hA0 hAt,
            one_mul]
  have hfac : ∀ i : ℕ, (i : ℝ≥0∞) + r * ((2 : ℝ≥0∞) ^ d)⁻¹ =
      ((i * 2 ^ d + r : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ d)⁻¹ := by
    intro i
    push_cast
    rw [add_mul, mul_assoc, ENNReal.mul_inv_cancel hB0 hBt, mul_one]
  have hP : ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹) ≤
      ((∏ i ∈ Finset.range 14, (i * 2 ^ d + r) : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ d)⁻¹) ^ 14 := by
    calc ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹)
        ≤ ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + r * ((2 : ℝ≥0∞) ^ d)⁻¹) :=
          Finset.prod_le_prod (fun i _ => add_le_add le_rfl hρ)
      _ = ∏ i ∈ Finset.range 14, (((i * 2 ^ d + r : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ d)⁻¹) :=
          Finset.prod_congr rfl fun i _ => hfac i
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
          push_cast
          rfl
  have hpow : ((2 : ℝ≥0∞) ^ 168)⁻¹ * (((2 : ℝ≥0∞) ^ d)⁻¹) ^ 14 =
      ((2 : ℝ≥0∞) ^ (168 + 14 * d))⁻¹ := by
    rw [← ENNReal.inv_pow, ← pow_mul, pow_add,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ (by norm_num))) (Or.inl (ENNReal.pow_ne_top (by norm_num))),
      mul_comm d 14]
  calc reuseSum 63 12 14 n
      ≤ n * (((2 : ℝ≥0∞) ^ 12)⁻¹) ^ 14 *
          ∏ i ∈ Finset.range 14, ((i : ℝ≥0∞) + n * ((2 : ℝ≥0∞) ^ 63)⁻¹) := reuseSum_le_prod _ _ _ _
    _ ≤ ((r : ℝ≥0∞) * 2 ^ (63 - d)) * ((2 : ℝ≥0∞) ^ 168)⁻¹ *
          (((∏ i ∈ Finset.range 14, (i * 2 ^ d + r) : ℕ) : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ d)⁻¹) ^ 14) := by
        rw [inv12_pow14]
        exact mul_le_mul (mul_le_mul hn' le_rfl zero_le zero_le) hP zero_le zero_le
    _ = ((r * 2 ^ (63 - d) * ∏ i ∈ Finset.range 14, (i * 2 ^ d + r) : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞) ^ (168 + 14 * d))⁻¹ := by
        rw [← hpow]
        push_cast
        ring
    _ ≤ ((2 : ℝ≥0∞) ^ c)⁻¹ := natMul_inv_pow_le _ _ _ (hc.trans_eq (pow_add 2 168 (14 * d)).symm)

theorem polyP_mono {Qc N qs ℓ Qc' N' qs' ℓ' : ℕ} (h1 : Qc ≤ Qc') (h2 : N ≤ N') (h3 : qs ≤ qs')
    (h4 : ℓ ≤ ℓ') : polyP Qc N qs ℓ ≤ polyP Qc' N' qs' ℓ' := by
  unfold polyP
  gcongr

theorem div64_le_2_20 {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ 26) : (ℓ + 56) / 64 ≤ 2 ^ 20 := by
  have := Nat.div_le_div_right (c := 64) (Nat.add_le_add_right hℓ 56)
  have h2 : (2 ^ 26 + 56) / 64 = 2 ^ 20 := by norm_num
  omega

theorem QlinT_le {qf qs ℓ F₀ S₀ : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀) (hℓ : ℓ ≤ 2 ^ 26) :
    QlinT qf qs ℓ ≤ 27 * F₀ + (S₀ + 1) * (253924886 + 45 * 2 ^ 20) := by
  have := div64_le_2_20 hℓ
  unfold QlinT
  gcongr

/-- The eleven-game part at caps `qf ≤ F₀`, `qs ≤ S₀`, `ℓ ≤ 2^26`, `QcAll ≤ Qc₀`, `NAll ≤ N₀`. -/
theorem eleven_tight_le {qf qs ℓ F₀ S₀ Qc₀ N₀ k m : ℕ} (hf : qf ≤ F₀) (hs : qs ≤ S₀)
    (hℓ : ℓ ≤ 2 ^ 26) (hQc : QcAll qf qs ℓ ≤ Qc₀) (hN : NAll qs ≤ N₀) (hkm : m + k = 256)
    (hnum : (27 * F₀ + (S₀ + 1) * (253924886 + 45 * 2 ^ 20)) * 2 ^ 128 +
      polyP Qc₀ N₀ S₀ (2 ^ 20) ≤ 2 ^ m) :
    nf (QlinT qf qs ℓ) (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ)) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ :=
  (nf_mono (QlinT_le hf hs hℓ) (polyP_mono hQc hN hs (ellB_le hℓ))).trans
    (nf_le_inv_pow k m hkm hnum)

theorem itsrLc_le_2_20 {ℓ : ℕ} (hℓ : ℓ ≤ 2 ^ 26) : Itsr.itsrLc ℓ ≤ 2 ^ 20 + 1 := by
  rw [Itsr.itsrLc_eq]
  have := div64_le_2_20 hℓ
  exact max_le (by norm_num) (by omega)

/-- ITSR term at `qf ≤ 2^60`, `qs ≤ 2^20`, `ℓ ≤ 2^26` (raised parameters). -/
theorem epsItsrF_t20 :
    epsItsrF (2 ^ 60) (2 ^ 21) (2 ^ 60) (2007387 * 2 ^ 20) (2 ^ 20 + 1) (2 ^ 20) (2 ^ 26) ≤
      ((2 : ℝ≥0∞) ^ 77)⁻¹ + ((2 : ℝ≥0∞) ^ 132)⁻¹ :=
  add_le_add
    (reuseSum_63_12_14_le_frac _ 129 10 77 (by norm_num) (by norm_num)
      (by norm_num [Finset.prod_range_succ]))
    (natMul_inv_pow_le _ _ _ (by norm_num))

/-- ITSR term at `qf ≤ 2^64`, `qs ≤ 2^40`, `ℓ ≤ 2^26`. -/
theorem epsItsrF_t40 :
    epsItsrF (2 ^ 64) (2 ^ 41) (2 ^ 64) (2007387 * 2 ^ 40) (2 ^ 20 + 1) (2 ^ 40) (2 ^ 26) ≤
      ((2 : ℝ≥0∞) ^ 63)⁻¹ + ((2 : ℝ≥0∞) ^ 94)⁻¹ :=
  add_le_add
    (reuseSum_63_12_14_le_frac _ 2049 10 63 (by norm_num) (by norm_num)
      (by norm_num [Finset.prod_range_succ]))
    (natMul_inv_pow_le _ _ _ (by norm_num))

/-- ITSR term at `qf ≤ 2^64`, `qs ≤ 2^64`, `ℓ ≤ 2^26`. -/
theorem epsItsrF_t64 :
    epsItsrF (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ :=
  add_le_add
    (reuseSum_63_12_14_le_frac _ 10241 10 45 (by norm_num) (by norm_num)
      (by norm_num [Finset.prod_range_succ]))
    (natMul_inv_pow_le _ _ _ (by norm_num))

theorem itsrQc_le_of {qs a : ℕ} (ha : 19 ≤ a) (hs : qs ≤ 2 ^ a) :
    Itsr.itsrQc qs ≤ 2007387 * 2 ^ a := by
  rw [Itsr.itsrQc_eq]
  have h1 : 269824 ≤ 2 ^ a := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) ha)
  nlinarith

/-! ## The tight numeric points -/

/-- SUF, tight, at `qs ≤ 2^20` signatures, `qf ≤ 2^60` compression queries (weaker than the `qf + 2^46 ≤ 2^60` of `suf_ideal_closed_2_20`), messages `≤ 2^26` bytes:
`2^-77 + 2^-132 + 2^-63`. -/
theorem suf_ideal_closed_tight_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (suf_tight_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- EUF, tight, at `qs ≤ 2^20` signatures, `qf ≤ 2^60` compression queries (weaker than the `qf + 2^46 ≤ 2^60` of `suf_ideal_closed_2_20`), messages `≤ 2^26` bytes:
`2^-77 + 2^-132 + 2^-63`. -/
theorem euf_ideal_closed_tight_2_20 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (euf_tight_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t20)).trans
    (add_le_add le_rfl (eleven_tight_le hf hs hℓ hQc (NAll_le_81 (hs.trans (by norm_num))) (k := 63) (m := 193) rfl
      (by unfold polyP; norm_num)))

/-- SUF, tight, at `qs ≤ 2^40`, `qf ≤ 2^64`, messages `≤ 2^26` bytes:
`2^-63 + 2^-94 + 2^-58`. -/
theorem suf_ideal_closed_tight_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (suf_tight_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight_le hf hs hℓ hQc (NAll_le_81 hs) (k := 58) (m := 198) rfl
      (by unfold polyP; norm_num)))

/-- EUF, tight, at `qs ≤ 2^40`, `qf ≤ 2^64`, messages `≤ 2^26` bytes:
`2^-63 + 2^-94 + 2^-58`. -/
theorem euf_ideal_closed_tight_2_40 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
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
  exact (euf_tight_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t40)).trans
    (add_le_add le_rfl (eleven_tight_le hf hs hℓ hQc (NAll_le_81 hs) (k := 58) (m := 198) rfl
      (by unfold polyP; norm_num)))

/-- SUF, tight, at `qs ≤ 2^64`, `qf ≤ 2^64`, messages `≤ 2^26` bytes:
`2^-45 + 2^-46 + 2^-35`. -/
theorem suf_ideal_closed_tight_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 35)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedS (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrS S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (suf_tight_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrSufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight_le hf hs hℓ hQc (NAll_le_82 hs) (k := 35) (m := 221) rfl
      (by unfold polyP; norm_num)))

/-- EUF, tight, at `qs ≤ 2^64`, `qf ≤ 2^64`, messages `≤ 2^26` bytes:
`2^-45 + 2^-46 + 2^-35`. -/
theorem euf_ideal_closed_tight_2_64 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ}
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
    (hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
    (hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
    (hf : qf ≤ 2 ^ 64) (hs : qs ≤ 2 ^ 64) (hℓ : ℓ ≤ 2 ^ 26) :
    eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 45)⁻¹ + ((2 : ℝ≥0∞) ^ 46)⁻¹ + ((2 : ℝ≥0∞) ^ 35)⁻¹ := by
  have hQc : QcAll qf qs ℓ ≤ 2 ^ 90 := QcAll_le_of hs hℓ ((Nat.add_le_add_right hf _).trans (by norm_num))
  have RI : RealizesItsrF (fun g => Reduction.Lazy.bItsrL
      (S.typedE (optRandU oR) ($ᵗ (Bytes 16)) g)) (2 ^ 64) (2 ^ 65) (2 ^ 64) (2007387 * 2 ^ 64) (2 ^ 20 + 1) (2 ^ 64) (2 ^ 26) :=
    Itsr.raiseItsr (Itsr.realizesItsrE S oR _ hqf hqs hlong hout) hf (by omega) hf
      (itsrQc_le_of (by norm_num) hs) (itsrLc_le_2_20 hℓ) hs hℓ
  exact (euf_tight_of S oR hqf hqs hlong hout (hQc.trans (by norm_num))
    ((itsrEufI_le_fine S (optRandU oR) _ RI).trans epsItsrF_t64)).trans
    (add_le_add le_rfl (eleven_tight_le hf hs hℓ hQc (NAll_le_82 hs) (k := 35) (m := 221) rfl
      (by unfold polyP; norm_num)))

end Ideal

#print axioms Ideal.Realizers.eps_le_tight
#print axioms Ideal.linT_le_QlinT
#print axioms Ideal.QlinT_le_old
#print axioms Ideal.sufRealizersU_eps_le
#print axioms Ideal.eufRealizersU_eps_le
#print axioms Ideal.suf_ideal_closed_tight
#print axioms Ideal.euf_ideal_closed_tight
#print axioms Ideal.reuseSum_63_12_14_le_frac
#print axioms Ideal.epsItsrF_t20
#print axioms Ideal.epsItsrF_t40
#print axioms Ideal.epsItsrF_t64
#print axioms Ideal.suf_ideal_closed_tight_2_20
#print axioms Ideal.euf_ideal_closed_tight_2_20
#print axioms Ideal.suf_ideal_closed_tight_2_40
#print axioms Ideal.euf_ideal_closed_tight_2_40
#print axioms Ideal.suf_ideal_closed_tight_2_64
#print axioms Ideal.euf_ideal_closed_tight_2_64
