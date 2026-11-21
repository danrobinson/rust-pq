import Integration.SlhDsaBridgeWotsRow
import PQ.Interactive.QromBridgeWotsPre

/-!
# The WOTS-chain PRE bridge (`qrPre`, term `pre`), game side

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

**Headline** `pre_term`: for every port forger `F` over `encΩ` and every `q'`, with `1 ≤ c.tl`,

  `avΩ c (fun ω ↦ qSM_DT_PRE_Advantage (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)))
     ≤ epsPre0 q'`

under ONE hypothesis `hModel` (machine side, NOT proved here): for every world `ω₀`, state
`st : Open.RState Link.vp (primsΩ ω₀)` and seed `pk`, the second phase `(qrPre …).invert st pk`
has a `q'`-query hybrid model over the port function, uniformly in the `Thash` component.
This is the fact `hpre` that `composed_of_linear_eps` consumes, with `ePre = epsPre0 (q + r.pre)`
(`pre_term_hpre`).

Route (no `PreValue`/`MixLE`): seed average (`qSM_DT_PRE_Advantage_eq_tsum`), resampling of the
`F`-row at the seed (`avΩ_wq_resample`), the forger-free first phase `Open.prePhase1`
(`Open.wotsPre_phase1_q1_zero` + kernel `rfl`), pull-back of the model along the row
(`wqRowEmb`, `encΩ_wq_row_local`), and the generic `PQ.Interactive.pre_row_avg_le` (lazy sampling
of the challenge messages, relabelling, `PQ.QROM.pre_embedded_obs_weighted_le`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

attribute [local irreducible] wotsChainTargets

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

/-- The first phase of `qrPre` at any world with the same non-`Thash` components is the
forger-free program `Open.prePhase1` at `ω`. -/
theorem qrPre_choose_eq (ω ω' : Ω128 c) (T : WqTab c) (hω : ω' = ω.wqWithThash T) :
    ((qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω')).choose :
      OracleComp (Open.preSpecC (Bytes 22) BN) (Open.RState Link.vp (primsΩ ω))) =
      Open.prePhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀ := by
  subst hω
  have h2 := Open.wotsPre_phase1_q1_zero (prims := primsΩ (ω.wqWithThash T))
    (pkSeedDist := pkSeedDist₀)
    (Open.hashFnsOf _) (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω.wqWithThash T)).toClassical
  have h3 : (Open.prePhase1 (vp := Link.vp) (prims := primsΩ (ω.wqWithThash T)) pkSeedDist₀ :
      OracleComp (Open.preSpecC (Bytes 22) BN) (Open.RState Link.vp (primsΩ ω))) =
      Open.prePhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀ := by
    wq_kernel_rfl
  unfold qrPre
  dsimp only
  exact h2.trans h3

theorem preInnerW_row_eq (ω : Ω128 c) (pk : BN) (R : Bytes 22 × BN → BN) :
    preInner (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.wqWithThash (wqRowT ω.thash pk R)))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_PRE_oracles
          (preWithEval (wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀)
            (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
              pkSeedDist₀).th.eval
            (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
              pkSeedDist₀).thColl.eval) pk)
          (Open.prePhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀)).run ([], [])) >>=
        fun r ↦
        (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.wqWithThash (wqRowT ω.thash pk R)))).invert r.1 pk >>= fun jm ↦
        liftU (match r.2.1[jm.1]? with
        | none => pure false
        | some tx =>
          pure (decide
            ((wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
              pkSeedDist₀).th.eval pk tx.1 ((wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀).emb jm.2) =
            (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
              pkSeedDist₀).th.eval pk tx.1
                ((wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀).emb tx.2))))) F.ρ₀ := by
  unfold preInner
  rw [qrPre_choose_eq c optRand₀ pkSeedDist₀ F ω _ _ rfl]
  wq_kernel_rfl

theorem pre_eval_row (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : Bytes 22 × BN → BN)
    (a : Bytes 22) (y : BN) :
    (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      pkSeedDist₀).th.eval pk a ((wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀).emb y) =
      R (a, y) := by
  exact wq_F_row c hn ω pk R a y

theorem pre_coll_row (ω : Ω128 c) (pk : BN) (R R' : Bytes 22 × BN → BN) (i : Unit)
    (a : Bytes 22) (xs : List BN) (h : ∀ m, R (a, m) = R' (a, m)) :
    (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      pkSeedDist₀).thColl.eval i pk a xs =
    (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R')))
      pkSeedDist₀).thColl.eval i pk a xs := by
  exact wq_thash_row_local c ω pk R R' a xs h

/-- **Per world and seed**, WOTS-chain PRE. -/
theorem pre_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : Ω128 c) (pk : BN)
    (hModel : ∀ st : Open.RState Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × BN) q',
        ∀ (T : WqTab c) (Ev : ℕ × BN → Prop) [DecidablePred Ev],
          Mo.prob (encΩ (ω.wqWithThash T)) Ev =
            qWeight Ev ((qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              (ω.wqWithThash T))).invert st pk) F.ρ₀) :
    ∑ R : Bytes 22 × BN → BN, (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞)⁻¹ *
      preInner (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.wqWithThash (wqRowT ω.thash pk R)))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card BN : ℝ≥0∞)⁻¹ + (Fintype.card BN : ℝ≥0∞)⁻¹) := by
  have hM : ∀ s : Open.RState Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × BN) BN (ℕ × BN) q',
        ∀ R (Ev : ℕ × BN → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.wqWithThash (wqRowT ω.thash pk R)))).invert s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (wqRowEmb c hn pk)
      (fun R ↦ encΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      (encΩ_wq_row_local c hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := pre_row_avg_le (wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀) pk
    (fun R ↦ (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ pre_eval_row c pkSeedDist₀ hn ω pk R t m)
    (fun R ↦ (wotsPreProblem Link.vp (primsΩ (ω.wqWithThash (wqRowT ω.thash pk R)))
      pkSeedDist₀).thColl.eval)
    (fun R R' i t x h ↦ pre_coll_row c pkSeedDist₀ ω pk R R' i t x h)
    (Open.prePhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀)
    (fun R s ↦ (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.wqWithThash (wqRowT ω.thash pk R)))).invert s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [preInnerW_row_eq]
  wq_kernel_rfl

/-- **The WOTS-chain PRE term** (`qrPre`), given the hybrid model of its second phase. -/
theorem pre_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) q',
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).invert st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_PRE_Advantage
      (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsPre0 q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 *
    ((Fintype.card BN : ℝ≥0∞)⁻¹ + (Fintype.card BN : ℝ≥0∞)⁻¹) with hε
  have hεe : ε = epsPre0 q' := by
    rw [hε, epsPre0, card_cast_N128 card_bytes_n]
  rw [← hεe]
  simp only [qSM_DT_PRE_Advantage_eq_tsum]
  set g : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    preInner (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hg
  have hsd : ∀ ω : Ω128 c,
      (wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (wotsPreProblem Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * g ω pk) ≤ ε
  simp only [hsd]
  have hswap : avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
      ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk) := by
    unfold avΩ
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap]
  have hpk : ∀ pk, avΩ c (fun ω ↦ g ω pk) ≤ ε := by
    intro pk
    rw [avΩ_wq_resample c hn pk]
    refine le_trans (avΩ_mono c fun ω ↦ ?_) (le_of_eq (avΩ_const c ε))
    exact pre_row_inner_le c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (wq_tsum_prob_le_one _) le_rfl
    _ = ε := one_mul ε

/-- **`hpre` of `composed_of_linear_eps`**: the PRE term at the composed theorem's count
`q + r.pre`, in exactly the form consumed (`ePre := epsPre0 (q + r.pre)`). -/
theorem pre_term_hpre (q : ℕ) (r : RedCounts) (htl : 35 ≤ c.tl)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) (q + r.pre),
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).invert st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_PRE_Advantage
      (qrPre (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsPre0 (q + r.pre) :=
  pre_term c optRand₀ pkSeedDist₀ F (by omega) _ hModel

end inst

end Reduction

#print axioms Reduction.qrPre_choose_eq
#print axioms Reduction.preInnerW_row_eq
#print axioms Reduction.pre_eval_row
#print axioms Reduction.pre_coll_row
#print axioms Reduction.pre_row_inner_le
#print axioms Reduction.pre_term
#print axioms Reduction.pre_term_hpre
