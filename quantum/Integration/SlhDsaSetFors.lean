import Integration.SlhDsaSetTcr
import Integration.SlhDsaSetForsMach
namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder Kronecker
set_option linter.unusedSectionVars false
variable (S : Sha2Set)
noncomputable def epsTcrSet (q : ℕ) : ℝ≥0∞ := (2 * (q : ℝ≥0∞) + 1)^2 / 2^(8*S.vp.params.n)
noncomputable def epsDsprSet (q : ℕ) : ℝ≥0∞ := ENNReal.ofReal (168 * (q : ℝ)^2 / 2^(8*S.vp.params.n))
theorem avg_add (c : Caps) (f g : FinFns S.vp.params c → ℝ≥0∞) :
    avg S c (fun x => f x + g x) = avg S c f + avg S c g := by
  simp only [avg, mul_add, Finset.sum_add_distrib]

/-! ## The arity-one row of `Thash` (the row of `F`) -/

def am1Equiv : ArMsg S 1 ≃ S.Node where
  toFun xs := xs.1.head (List.ne_nil_of_length_eq_add_one xs.2)
  invFun x := ⟨[x], rfl⟩
  left_inv xs := by
    obtain ⟨l, hl⟩ := xs
    cases l with
    | nil => simp at hl
    | cons a t =>
      cases t with
      | nil => rfl
      | cons b t => simp at hl
  right_inv _ := rfl

abbrev FRow : Type := Bytes 22 × S.Node → S.Node

def frowEquiv : (FRow S) ≃ ThRow S 1 :=
  Equiv.arrowCongr (Equiv.prodCongr (Equiv.refl _) (am1Equiv S).symm) (Equiv.refl _)

theorem frowEquiv_apply (R : (FRow S)) (a : Bytes 22) (xs : ArMsg S 1) :
    frowEquiv S R (a, xs) = R (a, am1Equiv S xs) := rfl

theorem fors_avΩ_resample_frow (c : Caps) (hn : 1 ≤ c.tl) (pk : S.Node) (f : FinFns S.vp.params c → ℝ≥0∞) :
    avg S c f = avg S c fun ω ↦ ∑ R : (FRow S),
      (Fintype.card (FRow S) : ℝ≥0∞)⁻¹ * f (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))) := by
  rw [avg_row S c 1 hn pk f]
  refine congrArg (avg S c) (funext fun ω ↦ ?_)
  have hc : Fintype.card (ThRow S 1) = Fintype.card (FRow S) := Fintype.card_congr (frowEquiv S).symm
  unfold unifW
  rw [hc]
  exact (Equiv.sum_comp (frowEquiv S)
    (fun R ↦ (Fintype.card (FRow S) : ℝ≥0∞)⁻¹ * f (ω.withThash (thRowT S 1 ω.thash pk R)))).symm

def frowEmb (c : Caps) (hn : 1 ≤ c.tl) (pk : S.Node) : Bytes 22 × S.Node ↪ Input S c :=
  (Equiv.toEmbedding (Equiv.prodCongr (Equiv.refl _) (am1Equiv S).symm)).trans (thRowEmb S c 1 hn pk)

theorem fors_encΩ_frow_local (c : Caps) (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (H G : (FRow S))
    (x : Input S c)
    (h : oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S H))) x ≠
      oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S G))) x) :
    ∃ x', frowEmb S c hn pk x' = x ∧ H x' ≠ G x' := by
  obtain ⟨x'', hx, hne⟩ := encΩ_row_local S c 1 hn ω pk (frowEquiv S H) (frowEquiv S G) x h
  refine ⟨(x''.1, am1Equiv S x''.2), ?_, hne⟩
  rw [← hx]
  change thRowEmb S c 1 hn pk (x''.1, (am1Equiv S).symm (am1Equiv S x''.2)) = _
  rw [Equiv.symm_apply_apply]

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem fors_eval_row (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) (a : Bytes 22)
    (x : S.Node) :
    (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval pk a x = R (a, x) := by
  change (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))).Thash pk a [x] = R (a, x)
  rw [thash_thRowT, dite_eq_left (show [x].length ≤ c.tl from hn)]
  exact thRowT_ofList S 1 hn ω.thash pk (frowEquiv S R) a ⟨[x], rfl⟩

theorem tcrFvInner_row_eq (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) :
    tcrFvInner (qToTcr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles
          (fvWithEval (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀)
            (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval) pk)
          (Open.forsPhase1 S.vp (worldPrims ω))).run .initial) >>= fun r ↦
        (qToTcr (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).forge r.1 pk >>= fun jm ↦
        liftU (match r.2.challenges[jm.1]? with
          | none => pure false
          | some tm =>
            pure (r.2.valid && decide (jm.2 ≠ tm.2 ∧
              (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk
                (frowEquiv S R)))) pkSeedDist₀).th.eval pk tm.1 jm.2 =
              (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk
                (frowEquiv S R)))) pkSeedDist₀).th.eval pk tm.1 tm.2)))) F.ρ₀ := by
  have hch : ((qToTcr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).choose :
      OracleComp (Open.ForsP1Spec (worldPrims ω)) (Open.ForsP1State S.vp (worldPrims ω))) =
      Open.forsPhase1 S.vp (worldPrims ω) := by
    have h2 := Open.toTcr_choose_eq (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))).toClassical
    have h3 : (Open.forsPhase1 S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk
        (frowEquiv S R)))) : OracleComp (Open.ForsP1Spec (worldPrims ω)) _) =
        Open.forsPhase1 S.vp (worldPrims ω) := by
      qtcr_kernel_rfl
    unfold qToTcr
    dsimp only
    exact h2.trans h3
  unfold tcrFvInner
  rw [hch]
  qtcr_kernel_rfl

theorem tcrFv_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node)
    (hModel : ∀ st : Open.ForsP1State S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) q',
        ∀ (T : ThTab S c) (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S (ω.withThash T)) Ev =
            qWeight Ev ((qToTcr (internal S c optRand₀ pkSeedDist₀ F
              (ω.withThash T))).forge st pk) F.ρ₀) :
    ∑ R : (FRow S), (Fintype.card (FRow S) : ℝ≥0∞)⁻¹ *
      tcrFvInner (qToTcr (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card S.Node : ℝ≥0∞) := by
  have hM : ∀ s : Open.ForsP1State S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × S.Node) S.Node (ℕ × S.Node) q',
        ∀ R (Ev : ℕ × S.Node → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qToTcr (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (frowEmb S c hn pk)
      (fun R ↦ oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      (fors_encΩ_frow_local S c hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcrFv_row_avg_le (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀) pk
    (fun R ↦ (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ fors_eval_row S c pkSeedDist₀ hn ω pk R t m)
    (Open.forsPhase1 S.vp (worldPrims ω))
    (fun R s ↦ (qToTcr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).forge s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [tcrFvInner_row_eq]
  qtcr_kernel_rfl

theorem tcrFv_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : FinFns S.vp.params c) (st : Open.ForsP1State S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × S.Node) q',
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × S.Node → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToTcr (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avg S c (fun ω ↦ qTcrFV_Advantage (qToTcr (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      epsTcrSet S q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card S.Node : ℝ≥0∞) with hε
  have hεe : ε = epsTcrSet S q' := by
    rw [hε, epsTcrSet, card_bytes', pow_mul]; norm_num
  rw [← hεe]
  simp only [qTcrFV_Advantage_eq_tsum]
  set g : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    tcrFvInner (qToTcr (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hg
  have hsd : ∀ ω : FinFns S.vp.params c,
      (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ := fun _ ↦ rfl
  change avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * g ω pk) ≤ ε
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
    exact tcrFv_row_inner_le S c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
    _ = ε := one_mul ε

end inst

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem fors_eval_row_dspr (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) (a : Bytes 22)
    (x : S.Node) :
    (forsDsprProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval pk a x = R (a, x) :=
  fors_eval_row S c pkSeedDist₀ hn ω pk R a x

noncomputable def dsprWinS (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S))
    (r : Open.ForsP1State S.vp (worldPrims ω) × TweakableHash.SM_DT_TCR_SourceFinalValidity.State
      (Bytes 22) S.Node) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (TweakableHash.SecondPreimageExists
      (forsDsprProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
        pkSeedDist₀).th pk tm.1 tm.2 ↔ jb.2 = true))

noncomputable def dsprWinP (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S))
    (r : Open.ForsP1State S.vp (worldPrims ω) × TweakableHash.SM_DT_TCR_SourceFinalValidity.State
      (Bytes 22) S.Node) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (TweakableHash.SecondPreimageExists
      (forsDsprProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
        pkSeedDist₀).th pk tm.1 tm.2))

theorem fors_spe_row (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) (tm : Bytes 22 × S.Node) :
    TweakableHash.SecondPreimageExists
      (forsDsprProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
        pkSeedDist₀).th pk tm.1 tm.2 ↔ fvSPE R tm := by
  unfold TweakableHash.SecondPreimageExists fvSPE
  simp only [fors_eval_row_dspr S c pkSeedDist₀ hn]

open Classical in
theorem dsprWinS_eq (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) r jb :
    dsprWinS S c pkSeedDist₀ ω pk R r jb =
      pure (decide (fvDsprS r.2.challenges r.2.valid R jb)) := by
  unfold dsprWinS
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprS, h]
  | some tm =>
    simp only
    congr 1
    simp only [fors_spe_row S c pkSeedDist₀ hn ω pk R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprS, h, hv]

open Classical in
theorem dsprWinP_eq (hn : 1 ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) r jb :
    dsprWinP S c pkSeedDist₀ ω pk R r jb =
      pure (decide (fvDsprP r.2.challenges r.2.valid R jb)) := by
  unfold dsprWinP
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprP, h]
  | some tm =>
    simp only
    congr 1
    simp only [fors_spe_row S c pkSeedDist₀ hn ω pk R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprP, h, hv]

theorem qToDspr_choose_row (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) :
    ((qToDspr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).choose :
      OracleComp (Open.ForsP1Spec (worldPrims ω)) (Open.ForsP1State S.vp (worldPrims ω))) =
      Open.forsPhase1 S.vp (worldPrims ω) := by
  have h2 := Open.toDspr_choose_eq (internal S c optRand₀ pkSeedDist₀ F
    (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R)))).toClassical
  have h3 : (Open.forsPhase1 S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk
      (frowEquiv S R)))) : OracleComp (Open.ForsP1Spec (worldPrims ω)) _) =
      Open.forsPhase1 S.vp (worldPrims ω) := by
    qtcr_kernel_rfl
  unfold qToDspr
  dsimp only
  exact h2.trans h3

theorem dsprSuccInner_row_eq (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) :
    dsprFvSuccInner (qToDspr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles
          (fvWithEval (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀)
            (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval) pk)
          (Open.forsPhase1 S.vp (worldPrims ω))).run .initial) >>= fun r ↦
        (qToDspr (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).guess r.1 pk >>= fun jb ↦
        liftU (dsprWinS S c pkSeedDist₀ ω pk R r jb)) F.ρ₀ := by
  unfold dsprFvSuccInner
  rw [qToDspr_choose_row]
  qtcr_kernel_rfl

theorem dsprSPInner_row_eq (ω : FinFns S.vp.params c) (pk : S.Node) (R : (FRow S)) :
    dsprFvSPInner (qToDspr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_SourceFinalValidity.oracles
          (fvWithEval (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀)
            (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
              pkSeedDist₀).th.eval) pk)
          (Open.forsPhase1 S.vp (worldPrims ω))).run .initial) >>= fun r ↦
        (qToDspr (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).guess r.1 pk >>= fun jb ↦
        liftU (dsprWinP S c pkSeedDist₀ ω pk R r jb)) F.ρ₀ := by
  unfold dsprFvSPInner
  rw [qToDspr_choose_row]
  qtcr_kernel_rfl

theorem fors_card_bn_ge_two : 2 ≤ Fintype.card S.Node := by
  rw [card_bytes']; cases S <;> decide

theorem dspr_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node)
    (hModel : ∀ st : Open.ForsP1State S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × Bool) q',
        Mo.Additive ∧ PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
        ∀ (T : ThTab S c) (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (oracle S (ω.withThash T)) Ev =
            qWeight Ev ((qToDspr (internal S c optRand₀ pkSeedDist₀ F
              (ω.withThash T))).guess st pk) F.ρ₀) :
    ∑ R : (FRow S), (Fintype.card (FRow S) : ℝ≥0∞)⁻¹ *
      dsprFvSuccInner (qToDspr (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk ≤
    ∑ R : (FRow S), (Fintype.card (FRow S) : ℝ≥0∞)⁻¹ *
      dsprFvSPInner (qToDspr (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))) pk +
      ENNReal.ofReal (168 * (q' : ℝ) ^ 2 / Fintype.card S.Node) := by
  have hM : ∀ s : Open.ForsP1State S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × S.Node) S.Node (ℕ × Bool) q',
        Mo.Additive ∧ PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
        ∀ R (Ev : ℕ × Bool → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qToDspr (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).guess s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hadd, hrows, hMo⟩ := hModel s
    have hR := RowsBound.pullback (frowEmb S c hn pk)
      (fun R ↦ oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      (fors_encΩ_frow_local S c hn ω pk) (fun H E ↦ (Mo.prob H E).toReal) hrows
    refine ⟨Mo.pullback (frowEmb S c hn pk)
      (fun R ↦ oracle S (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      (fors_encΩ_frow_local S c hn ω pk),
      hadd.pullback _ _ _, hR, fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := dsprFv_row_avg_le (forsTcrProblem S.vp (worldPrims ω) pkSeedDist₀) pk
    (fun R ↦ (forsTcrProblem S.vp (worldPrims (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ fors_eval_row S c pkSeedDist₀ hn ω pk R t m)
    (Open.forsPhase1 S.vp (worldPrims ω))
    (fun R s ↦ (qToDspr (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S 1 ω.thash pk (frowEquiv S R))))).guess s pk) F.ρ₀ q' hM
    (fors_card_bn_ge_two S) le_rfl
    (dsprWinS S c pkSeedDist₀ ω pk) (dsprWinP S c pkSeedDist₀ ω pk)
    (dsprWinS_eq S c pkSeedDist₀ hn ω pk) (dsprWinP_eq S c pkSeedDist₀ hn ω pk)
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · refine Finset.sum_congr rfl fun R _ ↦ ?_
    rw [dsprSuccInner_row_eq]
  · refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun R _ ↦ ?_) rfl
    rw [dsprSPInner_row_eq]

theorem fors_epsDsprSet_eq (q' : ℕ) :
    ENNReal.ofReal (168 * (q' : ℝ) ^ 2 / Fintype.card S.Node) = epsDsprSet S q' := by
  rw [epsDsprSet, card_bytes', pow_mul]; norm_num

theorem dspr_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : FinFns S.vp.params c) (st : Open.ForsP1State S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × Bool) q',
        Mo.Additive ∧
        PQ.QROM.Rows.RowsBound (fun H E ↦ (Mo.prob H E).toReal) q' ∧
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × Bool → Prop) [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qToDspr (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).guess st pk) F.ρ₀) :
    avg S c (fun ω ↦ qDsprFV_Success (qToDspr (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      avg S c (fun ω ↦ qDsprFV_SPProbability
        (qToDspr (internal S c optRand₀ pkSeedDist₀ F ω))) + epsDsprSet S q' := by
  set ε : ℝ≥0∞ := ENNReal.ofReal (168 * (q' : ℝ) ^ 2 / Fintype.card S.Node) with hε
  rw [← fors_epsDsprSet_eq, ← hε]
  simp only [qDsprFV_Success_eq_tsum, qDsprFV_SPProbability_eq_tsum]
  set gS : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    dsprFvSuccInner (qToDspr (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hgS
  set gP : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    dsprFvSPInner (qToDspr (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hgP
  have hsd : ∀ ω : FinFns S.vp.params c,
      (forsDsprProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ := fun _ ↦ rfl
  change avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (forsDsprProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * gS ω pk) ≤
    avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
      (forsDsprProblem S.vp (worldPrims ω) pkSeedDist₀).th.seedGen (· = pk) * gP ω pk) + ε
  simp only [hsd]
  have hswap : ∀ g : FinFns S.vp.params c → S.Node → ℝ≥0∞,
      avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * g ω pk) =
      ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk) := by
    intro g
    unfold avg
    simp only [← ENNReal.tsum_mul_left, Finset.mul_sum]
    rw [← Summable.tsum_finsetSum (fun _ _ ↦ CompleteLattice.summable)]
    refine tsum_congr fun pk ↦ Finset.sum_congr rfl fun ω _ ↦ by ring
  rw [hswap, hswap]
  have hpk : ∀ pk, avg S c (fun ω ↦ gS ω pk) ≤ avg S c (fun ω ↦ gP ω pk) + ε := by
    intro pk
    rw [fors_avΩ_resample_frow S c hn pk (fun ω ↦ gS ω pk),
      fors_avΩ_resample_frow S c hn pk (fun ω ↦ gP ω pk), ← avg_const S c ε, ← avg_add]
    exact avg_mono S c fun ω ↦
      dspr_row_inner_le S c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ gS ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * (avg S c (fun ω ↦ gP ω pk) + ε) :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ gP ω pk) +
          (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := by
        simp only [mul_add]
        rw [tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := by
        gcongr
        exact (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul ε).le

end inst

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem tcrFv_term_closed (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avg S c (fun ω ↦ qTcrFV_Advantage (qToTcr (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      epsTcrSet S (q + forsMHashes S.vp qs) := by
  exact tcrFv_term S c optRand₀ pkSeedDist₀ F hn _
    (forsTcr_hModel S c optRand₀ pkSeedDist₀ F q qs hq hqs)

end closed

section closed

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem dspr_term_closed (hn : 1 ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hqs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avg S c (fun ω ↦ qDsprFV_Success (qToDspr (internal S c optRand₀ pkSeedDist₀ F ω))) ≤
      avg S c (fun ω ↦ qDsprFV_SPProbability
        (qToDspr (internal S c optRand₀ pkSeedDist₀ F ω))) +
        epsDsprSet S (q + forsMHashes S.vp qs) := by
  exact dspr_term S c optRand₀ pkSeedDist₀ F hn _
    (forsDspr_hModel' S c optRand₀ pkSeedDist₀ F q qs hq hqs)

end closed

end Reduction.SetOracle

#print axioms Reduction.SetOracle.tcrFv_term_closed
#print axioms Reduction.SetOracle.dspr_term_closed
