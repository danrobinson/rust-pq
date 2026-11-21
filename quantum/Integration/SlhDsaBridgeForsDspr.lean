import Integration.SlhDsaBridgeFors
import PQ.QROM.ForsPullback

/-!
# The FORS-leaf DSPR bridge (`dspr`), game side, tight

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

**Headline** `dspr_term`: for every port forger `F` over the fixed encoding `encΩ`, with
`1 ≤ c.tl` and every `q'`,

  `avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (B ω))) ≤
     avΩ c (fun ω ↦ qDsprFV_SPProbability (qToDspr (B ω))) + epsDsprTight q'`

(`B = internalΩ c optRand₀ pkSeedDist₀ encΩ F`; the hypothesis `hdspr` of
`composed_of_linear_eps` at `eDspr = epsDsprTight (q + r.dspr)`), under ONE hypothesis `hModel`:
for every world `ω₀`, first-phase state `st` and seed `pk`, the second phase of the reduction
(`(qToDspr …).guess st pk`) has a `q'`-query hybrid model over the port function, uniformly in
the `Thash` component of the world, which is ADDITIVE and satisfies the target-count-free rows
bound `RowsBound` (the two properties the tight DSPR bound uses; see `quantum/HANDOFF-qfors.md`).
`hModel` is NOT proved here.

Route: as `tcrFv_term` (`Integration/SlhDsaBridgeFors.lean`), with
`PQ.Interactive.dsprFv_row_avg_le` (generic: `markLaw_of_obs` + `dspr_embedded_tight`) and the
pullback lemmas `HybridModel.Additive.pullback`, `RowsBound.pullback`
(`PQ/QROM/ForsPullback.lean`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- `F` of the DSPR game at the world with the resampled row is the row. -/
theorem fors_eval_row_dspr (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : FRow) (a : Bytes 22)
    (x : BN) :
    (forsDsprProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      pkSeedDist₀).th.eval pk a x = R (a, x) :=
  fors_eval_row c pkSeedDist₀ hn ω pk R a x

/-- The success decision of the DSPR game at the resampled world. -/
noncomputable def dsprWinS (ω : Ω128 c) (pk : BN) (R : FRow)
    (r : Open.ForsP1State Link.vp (primsΩ ω) × TweakableHash.SM_DT_TCR_SourceFinalValidity.State
      (Bytes 22) BN) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (TweakableHash.SecondPreimageExists
      (forsDsprProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
        pkSeedDist₀).th pk tm.1 tm.2 ↔ jb.2 = true))

/-- The baseline decision of the DSPR game at the resampled world. -/
noncomputable def dsprWinP (ω : Ω128 c) (pk : BN) (R : FRow)
    (r : Open.ForsP1State Link.vp (primsΩ ω) × TweakableHash.SM_DT_TCR_SourceFinalValidity.State
      (Bytes 22) BN) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (TweakableHash.SecondPreimageExists
      (forsDsprProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
        pkSeedDist₀).th pk tm.1 tm.2))

theorem fors_spe_row (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : FRow) (tm : Bytes 22 × BN) :
    TweakableHash.SecondPreimageExists
      (forsDsprProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
        pkSeedDist₀).th pk tm.1 tm.2 ↔ fvSPE R tm := by
  unfold TweakableHash.SecondPreimageExists fvSPE
  simp only [fors_eval_row_dspr c pkSeedDist₀ hn]

open Classical in
theorem dsprWinS_eq (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : FRow) r jb :
    dsprWinS c pkSeedDist₀ ω pk R r jb =
      pure (decide (fvDsprS r.2.challenges r.2.valid R jb)) := by
  unfold dsprWinS
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprS, h]
  | some tm =>
    simp only
    congr 1
    simp only [fors_spe_row c pkSeedDist₀ hn ω pk R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprS, h, hv]

open Classical in
theorem dsprWinP_eq (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : FRow) r jb :
    dsprWinP c pkSeedDist₀ ω pk R r jb =
      pure (decide (fvDsprP r.2.challenges r.2.valid R jb)) := by
  unfold dsprWinP
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprP, h]
  | some tm =>
    simp only
    congr 1
    simp only [fors_spe_row c pkSeedDist₀ hn ω pk R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprP, h, hv]

theorem qToDspr_choose_row (ω : Ω128 c) (pk : BN) (R : FRow) :
    ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).choose :
      OracleComp (Open.ForsP1Spec (primsΩ ω)) (Open.ForsP1State Link.vp (primsΩ ω))) =
      Open.forsPhase1 Link.vp (primsΩ ω) := by
  have h2 := Open.toDspr_choose_eq (internalΩ c optRand₀ pkSeedDist₀ encΩ F
    (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R)))).toClassical
  have h3 : (Open.forsPhase1 Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk
      (frowEquiv R)))) : OracleComp (Open.ForsP1Spec (primsΩ ω)) _) =
      Open.forsPhase1 Link.vp (primsΩ ω) := by
    qtcr_kernel_rfl
  unfold qToDspr
  dsimp only
  exact h2.trans h3

theorem dsprSuccInner_row_eq (ω : Ω128 c) (pk : BN) (R : FRow) :
    dsprFvSuccInner (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles
          (fvWithEval (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀)
            (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
              pkSeedDist₀).th.eval) pk)
          (Open.forsPhase1 Link.vp (primsΩ ω))).run .initial) >>= fun r ↦
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).guess r.1 pk >>= fun jb ↦
        liftU (dsprWinS c pkSeedDist₀ ω pk R r jb)) F.ρ₀ := by
  unfold dsprFvSuccInner
  rw [qToDspr_choose_row]
  qtcr_kernel_rfl

theorem dsprSPInner_row_eq (ω : Ω128 c) (pk : BN) (R : FRow) :
    dsprFvSPInner (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles
          (fvWithEval (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀)
            (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
              pkSeedDist₀).th.eval) pk)
          (Open.forsPhase1 Link.vp (primsΩ ω))).run .initial) >>= fun r ↦
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).guess r.1 pk >>= fun jb ↦
        liftU (dsprWinP c pkSeedDist₀ ω pk R r jb)) F.ρ₀ := by
  unfold dsprFvSPInner
  rw [qToDspr_choose_row]
  qtcr_kernel_rfl

theorem fors_card_bn_ge_two : 2 ≤ Fintype.card BN := by
  rw [card_bytes_n]; exact Nat.le_self_pow (by norm_num) 2

/-- **Per world and seed**: row-averaged success at most row-averaged baseline plus the tight
DSPR term. -/
theorem dspr_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : Ω128 c) (pk : BN)
    (hModel : ∀ st : Open.ForsP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bool) q',
        Mo.Additive ∧ PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
        ∀ (T : ThTab c) (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (encΩ (ω.withThash T)) Ev =
            qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              (ω.withThash T))).guess st pk) F.ρ₀) :
    ∑ R : FRow, (Fintype.card FRow : ℝ≥0∞)⁻¹ *
      dsprFvSuccInner (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))) pk ≤
    ∑ R : FRow, (Fintype.card FRow : ℝ≥0∞)⁻¹ *
      dsprFvSPInner (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))) pk +
      ENNReal.ofReal (168 * (q' : ℝ) ^ 2 / Fintype.card BN) := by
  have hM : ∀ s : Open.ForsP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × BN) BN (ℕ × Bool) q',
        Mo.Additive ∧ PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
        ∀ R (Ev : ℕ × Bool → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).guess s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hadd, hrows, hMo⟩ := hModel s
    have hR := RowsBound.pullback (frowEmb c hn pk)
      (fun R ↦ encΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      (fors_encΩ_frow_local c hn ω pk) (fun H E ↦ (Mo.prob H E).toReal) hrows
    refine ⟨Mo.pullback (frowEmb c hn pk)
      (fun R ↦ encΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      (fors_encΩ_frow_local c hn ω pk),
      hadd.pullback _ _ _, hR, fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := dsprFv_row_avg_le (forsTcrProblem Link.vp (primsΩ ω) pkSeedDist₀) pk
    (fun R ↦ (forsTcrProblem Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ fors_eval_row c pkSeedDist₀ hn ω pk R t m)
    (Open.forsPhase1 Link.vp (primsΩ ω))
    (fun R s ↦ (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (frowEquiv R))))).guess s pk) F.ρ₀ q' hM
    fors_card_bn_ge_two le_rfl
    (dsprWinS c pkSeedDist₀ ω pk) (dsprWinP c pkSeedDist₀ ω pk)
    (dsprWinS_eq c pkSeedDist₀ hn ω pk) (dsprWinP_eq c pkSeedDist₀ hn ω pk)
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [dsprSuccInner_row_eq]
  · refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun R _ ↦ ?_) rfl
    rw [dsprSPInner_row_eq]

theorem fors_epsDsprTight_eq (q' : ℕ) :
    ENNReal.ofReal (168 * (q' : ℝ) ^ 2 / Fintype.card BN) = epsDsprTight q' := by
  rw [epsDsprTight, card_bytes_n, Nat.cast_pow, Nat.cast_ofNat]

/-- **The FORS-leaf DSPR term, tight** (`hdspr` of `composed_of_linear_eps`), for every port
forger over the fixed encoding, given the additive, rows-bounded hybrid model of the reduction's
second phase (`hModel`). -/
theorem dspr_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.ForsP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bool) q',
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qDsprFV_Success (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
      avΩ c (fun ω ↦ qDsprFV_SPProbability
        (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) + epsDsprTight q' := by
  set ε : ℝ≥0∞ := ENNReal.ofReal (168 * (q' : ℝ) ^ 2 / Fintype.card BN) with hε
  rw [← fors_epsDsprTight_eq, ← hε]
  simp only [qDsprFV_Success_eq_tsum, qDsprFV_SPProbability_eq_tsum]
  set gS : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    dsprFvSuccInner (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hgS
  set gP : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    dsprFvSPInner (qToDspr (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hgP
  have hsd : ∀ ω : Ω128 c,
      (forsDsprProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ := fun _ ↦ rfl
  change avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (forsDsprProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * gS ω pk) ≤
    avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (forsDsprProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * gP ω pk) + ε
  simp only [hsd]
  have hswap : ∀ g : Ω128 c → BN → ℝ≥0∞,
      avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
      ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk) := by
    intro g
    unfold avΩ
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap, hswap]
  have hpk : ∀ pk, avΩ c (fun ω ↦ gS ω pk) ≤ avΩ c (fun ω ↦ gP ω pk) + ε := by
    intro pk
    rw [fors_avΩ_resample_frow c hn pk (fun ω ↦ gS ω pk),
      fors_avΩ_resample_frow c hn pk (fun ω ↦ gP ω pk), ← avΩ_const c ε, ← avΩ_add]
    exact avΩ_mono c fun ω ↦
      dspr_row_inner_le c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ gS ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * (avΩ c (fun ω ↦ gP ω pk) + ε) :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ gP ω pk) +
          (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := by
        gcongr
        exact (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul ε).le

end inst

end Reduction

#print axioms Reduction.dsprWinS_eq
#print axioms Reduction.dsprWinP_eq
#print axioms Reduction.dsprSuccInner_row_eq
#print axioms Reduction.dsprSPInner_row_eq
#print axioms Reduction.dspr_row_inner_le
#print axioms Reduction.dspr_term
