import Integration.SlhDsaSetFors
import Integration.SlhDsaSetWotsMach
namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker
set_option linter.unusedSectionVars false
variable (S : Sha2Set)
noncomputable def epsPreSet (q : ℕ) : ℝ≥0∞ :=
  (2 * (q : ℝ≥0∞) + 1)^2 * (((2 : ℝ≥0∞)^(8*S.vp.params.n))⁻¹ + ((2 : ℝ≥0∞)^(8*S.vp.params.n))⁻¹)
noncomputable def epsUdSet (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal (8 * (q : ℝ)^2 / 2^(8*S.vp.params.n))
section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem qrTcrT_choose_eq (ω ω' : FinFns S.vp.params c) (T : ThTab S c) (hω : ω' = ω.withThash T) :
    ((qrTcrT (internal S c optRand₀ pkSeedDist₀ F ω')).choose :
      OracleComp (Open.tcrSpecC (Bytes 22) S.Node) (Open.RState S.vp (worldPrims ω))) =
      Open.wotsTcrPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀ := by
  subst hω
  have h2 := Open.wotsTcrT_phase1_q1_zero (prims := worldPrims (ω.withThash T)) (pkSeedDist := pkSeedDist₀)
    (Open.hashFnsOf _) (internal S c optRand₀ pkSeedDist₀ F (ω.withThash T)).toClassical
  have h3 : (Open.wotsTcrPhase1 (vp := S.vp) (prims := worldPrims (ω.withThash T)) pkSeedDist₀ :
      OracleComp (Open.tcrSpecC (Bytes 22) S.Node) (Open.RState S.vp (worldPrims ω))) =
      Open.wotsTcrPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀ := by
    qtcr_kernel_rfl
  unfold qrTcrT
  dsimp only
  exact h2.trans h3

theorem tcrInnerT_row_eq (ω : FinFns S.vp.params c) (pk : S.Node) (R : Bytes 22 × S.Node → S.Node) :
    tcrInner (qrTcrT (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_oracles
          (tcrWithEval (wotsTcrProblemT S.vp (worldPrims ω) pkSeedDist₀)
            (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval
            (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).thColl.eval) pk)
          (Open.wotsTcrPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀)).run ([], [])) >>=
        fun r ↦
        (qrTcrT (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧
            (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval pk tm.1 jm.2 =
            (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval pk tm.1 tm.2))) F.ρ₀ := by
  unfold tcrInner
  rw [qrTcrT_choose_eq S c optRand₀ pkSeedDist₀ F ω _ _ rfl]
  qtcr_kernel_rfl

theorem wots_eval_row (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : Bytes 22 × S.Node → S.Node)
    (a : Bytes 22) (y : S.Node) :
    (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval pk a y = R (a, y) := by
  change (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))).Thash pk a [y] = R (a, y)
  rw [thash_thRowT, dite_eq_left (by simpa using hn)]
  exact thRowT_ofList S 1 hn ω.thash pk (frowEquiv S R) a ⟨[y], rfl⟩

theorem wots_coll_row (ω : FinFns S.vp.params c) (pk : S.Node) (R R' : Bytes 22 × S.Node → S.Node) (i : Unit)
    (a : Bytes 22) (xs : List S.Node) (h : ∀ m, R (a, m) = R' (a, m)) :
    (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).thColl.eval i pk a xs =
    (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R'))))
      pkSeedDist₀).thColl.eval i pk a xs := by
  change (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))).Thash pk a xs =
    (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R')))).Thash pk a xs
  rw [thash_thRowT, thash_thRowT]
  split_ifs with hl
  · unfold thRowT
    split_ifs with h2
    · exact h _
    · rfl
  · rfl

theorem tcrT_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node)
    (hModel : ∀ st : Open.RState S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) q',
        ∀ (T : ThTab S c) (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S (ω.withThash T)) Ev =
            qWeight Ev ((qrTcrT (internal S c optRand₀ pkSeedDist₀ F
              (ω.withThash T))).forge st pk) F.ρ₀) :
    ∑ R : Bytes 22 × S.Node → S.Node, (Fintype.card (Bytes 22 × S.Node → S.Node) : ℝ≥0∞)⁻¹ *
      tcrInner (qrTcrT (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card S.Node : ℝ≥0∞) := by
  have hM : ∀ s : Open.RState S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × S.Node) S.Node (ℕ × S.Node) q',
        ∀ R (Ev : ℕ × S.Node → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qrTcrT (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (frowEmb S c hn pk)
      (fun R ↦ oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      (fors_encΩ_frow_local S c hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcr_row_avg_le (wotsTcrProblemT S.vp (worldPrims ω) pkSeedDist₀) pk
    (fun R ↦ (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ wots_eval_row S c pkSeedDist₀ hn ω pk R t m)
    (fun R ↦ (wotsTcrProblemT S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).thColl.eval)
    (fun R R' i t x h ↦ wots_coll_row S c pkSeedDist₀ ω pk R R' i t x h)
    (Open.wotsTcrPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀)
    (fun R s ↦ (qrTcrT (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).forge s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [tcrInnerT_row_eq]
  qtcr_kernel_rfl

theorem tcrT_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : FinFns S.vp.params c) (st : Open.RState S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) q',
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avg S c (fun ω ↦ qSM_DT_TCR_Advantage
      (qrTcrT (internal S c optRand₀ pkSeedDist₀ F ω))) ≤ epsTcrSet S q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card S.Node : ℝ≥0∞) with hε
  have hεe : ε = epsTcrSet S q' := by
    rw [hε, epsTcrSet, card_bytes', pow_mul]; norm_num
  rw [← hεe]
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  set g : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    tcrInner (qrTcrT (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hg
  have hsd : ∀ ω : FinFns S.vp.params c,
      (wotsTcrProblemT S.vp (worldPrims ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (wotsTcrProblemT S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * g ω pk) ≤ ε
  simp only [hsd]
  have hswap : avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
      ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk) := by
    unfold avg
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap]
  have hpk : ∀ pk, avg S c (fun ω ↦ g ω pk) ≤ ε := by
    intro pk
    rw [fors_avΩ_resample_frow S c hn pk]
    refine le_trans (avg_mono S c fun ω ↦ ?_) (le_of_eq (avg_const S c ε))
    exact tcrT_row_inner_le S c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
    _ = ε := one_mul ε

end inst

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem tcrT_term_closed (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avg S c (fun ω ↦ qSM_DT_TCR_Advantage
      (qrTcrT (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
        epsTcrSet S (q + qmWotsTcrTHashes S.vp qs) := by
  exact tcrT_term S c optRand₀ pkSeedDist₀ F hn _
    (tcrT_hModel S c optRand₀ pkSeedDist₀ F q qs hq hqs)

end closed

attribute [local irreducible] wotsChainTargets

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem qrPre_choose_eq (ω ω' : FinFns S.vp.params c) (T : ThTab S c) (hω : ω' = ω.withThash T) :
    ((qrPre (internal S c optRand₀ pkSeedDist₀ F ω')).choose :
      OracleComp (Open.preSpecC (Bytes 22) S.Node) (Open.RState S.vp (worldPrims ω))) =
      Open.prePhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀ := by
  subst hω
  have h2 := Open.wotsPre_phase1_q1_zero (prims := worldPrims (ω.withThash T))
    (pkSeedDist := pkSeedDist₀)
    (Open.hashFnsOf _) (internal S c optRand₀ pkSeedDist₀ F (ω.withThash T)).toClassical
  have h3 : (Open.prePhase1 (vp := S.vp) (prims := worldPrims (ω.withThash T)) pkSeedDist₀ :
      OracleComp (Open.preSpecC (Bytes 22) S.Node) (Open.RState S.vp (worldPrims ω))) =
      Open.prePhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀ := by
    wq_kernel_rfl
  unfold qrPre
  dsimp only
  exact h2.trans h3

theorem preInnerW_row_eq (ω : FinFns S.vp.params c) (pk : S.Node) (R : Bytes 22 × S.Node → S.Node) :
    preInner (qrPre (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_PRE_oracles
          (preWithEval (wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀)
            (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval
            (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).thColl.eval) pk)
          (Open.prePhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀)).run ([], [])) >>=
        fun r ↦
        (qrPre (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).invert r.1 pk >>= fun jm ↦
        liftU (match r.2.1[jm.1]? with
        | none => pure false
        | some tx =>
          pure (decide
            ((wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval pk tx.1 ((wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀).emb jm.2) =
            (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval pk tx.1
                ((wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀).emb tx.2))))) F.ρ₀ := by
  unfold preInner
  rw [qrPre_choose_eq S c optRand₀ pkSeedDist₀ F ω _ _ rfl]
  wq_kernel_rfl

theorem pre_eval_row (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : Bytes 22 × S.Node → S.Node)
    (a : Bytes 22) (y : S.Node) :
    (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval pk a ((wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀).emb y) =
      R (a, y) := by
  exact wots_eval_row S c pkSeedDist₀ hn ω pk R a y

theorem pre_coll_row (ω : FinFns S.vp.params c) (pk : S.Node) (R R' : Bytes 22 × S.Node → S.Node) (i : Unit)
    (a : Bytes 22) (xs : List S.Node) (h : ∀ m, R (a, m) = R' (a, m)) :
    (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).thColl.eval i pk a xs =
    (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R'))))
      pkSeedDist₀).thColl.eval i pk a xs := by
  exact wots_coll_row S c pkSeedDist₀ ω pk R R' () a xs h

theorem pre_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node)
    (hModel : ∀ st : Open.RState S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) q',
        ∀ (T : ThTab S c) (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S (ω.withThash T)) Ev =
            qWeight Ev ((qrPre (internal S c optRand₀ pkSeedDist₀ F
              (ω.withThash T))).invert st pk) F.ρ₀) :
    ∑ R : Bytes 22 × S.Node → S.Node, (Fintype.card (Bytes 22 × S.Node → S.Node) : ℝ≥0∞)⁻¹ *
      preInner (qrPre (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 *
        ((Fintype.card S.Node : ℝ≥0∞)⁻¹ + (Fintype.card S.Node : ℝ≥0∞)⁻¹) := by
  have hM : ∀ s : Open.RState S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × S.Node) S.Node (ℕ × S.Node) q',
        ∀ R (Ev : ℕ × S.Node → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qrPre (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).invert s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (frowEmb S c hn pk)
      (fun R ↦ oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      (fors_encΩ_frow_local S c hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := pre_row_avg_le (wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀) pk
    (fun R ↦ (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ pre_eval_row S c pkSeedDist₀ hn ω pk R t m)
    (fun R ↦ (wotsPreProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).thColl.eval)
    (fun R R' i t x h ↦ pre_coll_row S c pkSeedDist₀ ω pk R R' i t x h)
    (Open.prePhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀)
    (fun R s ↦ (qrPre (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).invert s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [preInnerW_row_eq]
  wq_kernel_rfl

theorem pre_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : FinFns S.vp.params c) (st : Open.RState S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) q',
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrPre (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).invert st pk) F.ρ₀) :
    avg S c (fun ω ↦ qSM_DT_PRE_Advantage
      (qrPre (internal S c optRand₀ pkSeedDist₀ F ω))) ≤ epsPreSet S q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 *
    ((Fintype.card S.Node : ℝ≥0∞)⁻¹ + (Fintype.card S.Node : ℝ≥0∞)⁻¹) with hε
  have hεe : ε = epsPreSet S q' := by
    rw [hε, epsPreSet, card_bytes', pow_mul]; norm_num
  rw [← hεe]
  simp only [qSM_DT_PRE_Advantage_eq_tsum]
  set g : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    preInner (qrPre (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hg
  have hsd : ∀ ω : FinFns S.vp.params c,
      (wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (wotsPreProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * g ω pk) ≤ ε
  simp only [hsd]
  have hswap : avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
      ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk) := by
    unfold avg
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap]
  have hpk : ∀ pk, avg S c (fun ω ↦ g ω pk) ≤ ε := by
    intro pk
    rw [fors_avΩ_resample_frow S c hn pk]
    refine le_trans (avg_mono S c fun ω ↦ ?_) (le_of_eq (avg_const S c ε))
    exact pre_row_inner_le S c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (wq_tsum_prob_le_one _) le_rfl
    _ = ε := one_mul ε

end inst

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem qrUd_pick_eq (ω ω' : FinFns S.vp.params c) (T : ThTab S c) (hω : ω' = ω.withThash T) :
    ((qrUd (internal S c optRand₀ pkSeedDist₀ F ω')).pick :
      OracleComp (Open.udSpecC (Bytes 22) S.Node) (Open.RState S.vp (worldPrims ω))) =
      Open.udPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀ := by
  subst hω
  have h2 := Open.wotsUd_phase1_q1_zero (prims := worldPrims (ω.withThash T))
    (pkSeedDist := pkSeedDist₀)
    (Open.hashFnsOf _) (internal S c optRand₀ pkSeedDist₀ F (ω.withThash T)).toClassical
  have h3 : (Open.udPhase1 (vp := S.vp) (prims := worldPrims (ω.withThash T)) pkSeedDist₀ :
      OracleComp (Open.udSpecC (Bytes 22) S.Node) (Open.RState S.vp (worldPrims ω))) =
      Open.udPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀ := by
    wq_kernel_rfl
  unfold qrUd
  dsimp only
  exact h2.trans h3

theorem udInnerW_row_eq (world : TweakableHash.SM_DT_UD_World) (ω : FinFns S.vp.params c) (pk : S.Node)
    (R : Bytes 22 × S.Node → S.Node) :
    udInner world (qrUd (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_UD_oracles world
          (udWithEval (wotsUdProblem S.vp (worldPrims ω) pkSeedDist₀)
            (wotsUdProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval
            (wotsUdProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).thColl.eval) pk)
          (Open.udPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀)).run ([], [])) >>=
        fun r ↦
        (qrUd (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).distinguish r.1 pk) F.ρ₀ := by
  unfold udInner
  rw [qrUd_pick_eq S c optRand₀ pkSeedDist₀ F ω _ _ rfl]
  wq_kernel_rfl

theorem ud_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node)
    (hTight : ∀ st : Open.RState S.vp (worldPrims ω),
      ∃ f : (Input S c → (Output S)) → ℝ≥0∞, PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
        ∀ T : ThTab S c, f (oracle S (ω.withThash T)) =
          qWeight (· = true) ((qrUd (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash T))).distinguish st pk) F.ρ₀) :
    ∑ R : Bytes 22 × S.Node → S.Node, (Fintype.card (Bytes 22 × S.Node → S.Node) : ℝ≥0∞)⁻¹ *
      udInner .real (qrUd (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk ≤
      ∑ R : Bytes 22 × S.Node → S.Node, (Fintype.card (Bytes 22 × S.Node → S.Node) : ℝ≥0∞)⁻¹ *
        udInner .ideal (qrUd (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk +
      ENNReal.ofReal (8 * (q' : ℝ) ^ 2 / Fintype.card S.Node) := by
  have hT : ∀ s : Open.RState S.vp (worldPrims ω),
      ∃ f : (Bytes 22 × S.Node → S.Node) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
        ∀ R, f R = qWeight (· = true) ((qrUd (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).distinguish s pk) F.ρ₀ := by
    intro s
    obtain ⟨f, hf, hfe⟩ := hTight s
    refine ⟨fun R ↦ f (oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))),
      wq_tightAvgBound_pullback (fun H ↦ (f H).toReal) q' hf (frowEmb S c hn pk)
        (fun R ↦ oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))) (fors_encΩ_frow_local S c hn ω pk),
      fun R ↦ hfe _⟩
  have key := ud_row_avg_le (wotsUdProblem S.vp (worldPrims ω) pkSeedDist₀) pk
    (fun R ↦ (wotsUdProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ wots_eval_row S c pkSeedDist₀ hn ω pk R t m)
    (fun R ↦ (wotsUdProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).thColl.eval)
    (fun R R' i t x h ↦ wots_coll_row S c pkSeedDist₀ ω pk R R' () t x h) rfl rfl
    (Open.udPhase1 (vp := S.vp) (prims := worldPrims ω) pkSeedDist₀)
    (fun R s ↦ (qrUd (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).distinguish s pk) F.ρ₀ F.posSemidef
    F.trace_eq_one q' hT
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_))
    (le_trans key (add_le_add (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) le_rfl))
  · rw [udInnerW_row_eq]
  · rw [udInnerW_row_eq]

theorem ud_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hTight : ∀ (ω₀ : FinFns S.vp.params c) (st : Open.RState S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ f : (Input S c → (Output S)) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) q' ∧
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node),
          f (oracle S { ω₀ with thash := T }) =
            qWeight (· = true) ((qrUd (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀) :
    avg S c (fun ω ↦ qSM_DT_UD_RealSuccess
      (qrUd (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      avg S c (fun ω ↦ qSM_DT_UD_IdealSuccess
        (qrUd (internal S c optRand₀ pkSeedDist₀ F ω))) + epsUdSet S q' := by
  set δ : ℝ≥0∞ := ENNReal.ofReal (8 * (q' : ℝ) ^ 2 / Fintype.card S.Node) with hδ
  have hδe : δ = epsUdSet S q' := by
    have hc : (Fintype.card S.Node : ℝ) = 2 ^ (8*S.vp.params.n) := by
      rw [card_bytes', pow_mul]; norm_num
    rw [hδ, epsUdSet, hc]
  rw [← hδe]
  simp only [qSM_DT_UD_RealSuccess_eq_tsum, qSM_DT_UD_IdealSuccess_eq_tsum]
  set gR : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    udInner .real (qrUd (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hgR
  set gI : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    udInner .ideal (qrUd (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hgI
  have hsd : ∀ ω : FinFns S.vp.params c,
      (wotsUdProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (wotsUdProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * gR ω pk) ≤
    avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (wotsUdProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * gI ω pk) + δ
  simp only [hsd]
  have hswap : ∀ g : FinFns S.vp.params c → S.Node → ℝ≥0∞,
      avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
        ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk) := by
    intro g
    unfold avg
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap gR, hswap gI]
  have hpk : ∀ pk, avg S c (fun ω ↦ gR ω pk) ≤ avg S c (fun ω ↦ gI ω pk) + δ := by
    intro pk
    rw [fors_avΩ_resample_frow S c hn pk (fun ω ↦ gR ω pk), fors_avΩ_resample_frow S c hn pk (fun ω ↦ gI ω pk),
      ← avg_const S c δ, ← avg_add]
    exact avg_mono S c fun ω ↦
      ud_row_inner_le S c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hTight ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ gR ω pk)
      ≤ ∑' pk, (PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ gI ω pk) +
          PQ.Interactive.prob pkSeedDist₀ (· = pk) * δ) :=
        tsum_le_tsum fun pk ↦ by rw [← mul_add]; exact mul_le_mul' le_rfl (hpk pk)
    _ = ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ gI ω pk) +
          (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * δ := by
        rw [tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := by
        gcongr
        calc (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * δ ≤ 1 * δ :=
              mul_le_mul' (wq_tsum_prob_le_one _) le_rfl
          _ = δ := one_mul δ

end inst

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem pre_closed (q qs : ℕ) (htl : 1 ≤ c.tl)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avg S c (fun ω ↦ qSM_DT_PRE_Advantage
      (qrPre (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      epsPreSet S (q + qmWotsPreHashes S.vp qs) := by
  have h := wotsPre_hModel S c optRand₀ pkSeedDist₀ F q qs hq hqs
  exact pre_term S c optRand₀ pkSeedDist₀ F htl _ h

theorem wotsUd_hTight (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    ∀ (ω₀ : FinFns S.vp.params c) (st : Open.RState S.vp (worldPrims ω₀)) (pk : S.Node),
      ∃ f : (Input S c → (Output S)) → ℝ≥0∞,
        PQ.QROM.Tight.TightAvgBound (fun H ↦ (f H).toReal) (q + qmWotsUdHashes S.vp qs) ∧
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node),
          f (oracle S { ω₀ with thash := T }) =
            qWeight (· = true) ((qrUd (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).distinguish st pk) F.ρ₀ := by
  intro ω₀ st pk
  obtain ⟨ρ, hρ⟩ := exists_subState F.ρ₀ F.posSemidef F.trace_eq_one
  obtain ⟨Mach, hP, hE⟩ := wotsUd_mach_exists S c optRand₀ pkSeedDist₀ F ω₀ st pk q qs hq hqs
  obtain ⟨x, hx, hxe⟩ := hP.exists_prog_qprob
  refine ⟨fun H ↦ PQ.QROM.qprob LocalSig.Interp.instruments H x ρ (fun p ↦ p.2 = true),
    PQ.QROM.Tight.qprob_tightAvgBound LocalSig.Interp.instruments x ρ _ hx _, fun T ↦ ?_⟩
  show PQ.QROM.qprob LocalSig.Interp.instruments _ x ρ (fun p ↦ p.2 = true) = _
  rw [hxe (· = true) _ ρ, hE, hρ]

theorem ud_closed (q qs : ℕ) (htl : 1 ≤ c.tl)
    (hq : ∀ pk, CountBound isPort (F.main pk) q) (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avg S c (fun ω ↦ qSM_DT_UD_RealSuccess
      (qrUd (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      avg S c (fun ω ↦ qSM_DT_UD_IdealSuccess
        (qrUd (internal S c optRand₀ pkSeedDist₀ F ω))) +
        epsUdSet S (q + qmWotsUdHashes S.vp qs) :=
  ud_term S c optRand₀ pkSeedDist₀ F htl _
    (wotsUd_hTight S c optRand₀ pkSeedDist₀ F q qs hq hqs)

end inst

end Reduction.SetOracle

#print axioms Reduction.SetOracle.tcrT_term_closed
#print axioms Reduction.SetOracle.pre_closed
#print axioms Reduction.SetOracle.ud_closed
