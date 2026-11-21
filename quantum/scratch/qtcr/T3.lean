import Integration.SlhDsaBridgeTcr
import Reduction.Open.Phase1Wots

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

attribute [local irreducible] arityTargets tcrTargets wotsStepTargetsT wotsStepTargets

/-- Arity-one messages are single values. -/
def msg1Equiv : ArMsg 1 ≃ BN where
  toFun xs := xs.1.headD default
  invFun y := ⟨[y], rfl⟩
  left_inv := by
    rintro ⟨xs, h⟩
    match xs, h with
    | [y], _ => rfl
  right_inv _ := rfl

/-- `F`-rows (message type `BN`) as arity-one rows. -/
def fRowEquiv : (Bytes 22 × BN → BN) ≃ ThRow 1 :=
  Equiv.arrowCongr (Equiv.prodCongr (Equiv.refl _) msg1Equiv.symm) (Equiv.refl _)

lemma fRowEquiv_apply (R : Bytes 22 × BN → BN) (a : Bytes 22) (xs : ArMsg 1) :
    fRowEquiv R (a, xs) = R (a, msg1Equiv xs) := rfl

/-- Resampling one `F`-row. -/
theorem avΩ_resample_frow (c : Caps) (hn : 1 ≤ c.tl) (pk : BN) (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ R : Bytes 22 × BN → BN,
      (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞)⁻¹ *
        f (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))) := by
  rw [avΩ_resample_row c 1 hn pk f]
  refine congrArg (avΩ c) (funext fun ω ↦ ?_)
  have hcard : Fintype.card (Bytes 22 × BN → BN) = Fintype.card (ThRow 1) :=
    Fintype.card_congr fRowEquiv
  rw [hcard]
  exact (Equiv.sum_comp fRowEquiv fun R ↦
    (Fintype.card (ThRow 1) : ℝ≥0∞)⁻¹ * f (ω.withThash (thRowT 1 ω.thash pk R))).symm

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

theorem qrTcrT_choose_eq (ω ω' : Ω128 c) (T : ThTab c) (hω : ω' = ω.withThash T) :
    ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω')).choose :
      OracleComp (Open.tcrSpecC (Bytes 22) BN) (Open.RState Link.vp (primsΩ ω))) =
      Open.wotsTcrPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀ := by
  subst hω
  have h2 := Open.wotsTcrT_phase1_q1_zero (prims := primsΩ (ω.withThash T)) (pkSeedDist := pkSeedDist₀)
    (Open.hashFnsOf _) (internalΩ c optRand₀ pkSeedDist₀ encΩ F (ω.withThash T)).toClassical
  have h3 : (Open.wotsTcrPhase1 (vp := Link.vp) (prims := primsΩ (ω.withThash T)) pkSeedDist₀ :
      OracleComp (Open.tcrSpecC (Bytes 22) BN) (Open.RState Link.vp (primsΩ ω))) =
      Open.wotsTcrPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀ := by
    qtcr_kernel_rfl
  unfold qrTcrT
  dsimp only
  exact h2.trans h3

theorem tcrInnerT_row_eq (ω : Ω128 c) (pk : BN) (R : Bytes 22 × BN → BN) :
    tcrInner (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_oracles
          (tcrWithEval (wotsTcrProblemT Link.vp (primsΩ ω) pkSeedDist₀)
            (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
              pkSeedDist₀).th.eval
            (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
              pkSeedDist₀).thColl.eval) pk)
          (Open.wotsTcrPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀)).run ([], [])) >>=
        fun r ↦
        (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))).forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧
            (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
              pkSeedDist₀).th.eval pk tm.1 jm.2 =
            (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
              pkSeedDist₀).th.eval pk tm.1 tm.2))) F.ρ₀ := by
  unfold tcrInner
  rw [qrTcrT_choose_eq c optRand₀ pkSeedDist₀ F ω _ _ rfl]
  qtcr_kernel_rfl

theorem wots_eval_row (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : Bytes 22 × BN → BN)
    (a : Bytes 22) (y : BN) :
    (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
      pkSeedDist₀).th.eval pk a y = R (a, y) := by
  change (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R)))).Thash pk a [y] = R (a, y)
  rw [thash_thRowT, dif_pos (by simpa using hn)]
  exact thRowT_ofList 1 hn ω.thash pk (fRowEquiv R) a ⟨[y], rfl⟩

theorem wots_coll_row (ω : Ω128 c) (pk : BN) (R R' : Bytes 22 × BN → BN) (i : Unit)
    (a : Bytes 22) (xs : List BN) (h : ∀ m, R (a, m) = R' (a, m)) :
    (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
      pkSeedDist₀).thColl.eval i pk a xs =
    (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R'))))
      pkSeedDist₀).thColl.eval i pk a xs := by
  change (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R)))).Thash pk a xs =
    (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R')))).Thash pk a xs
  rw [thash_thRowT, thash_thRowT]
  split_ifs with hl
  · unfold thRowT
    split_ifs with h2
    · exact h _
    · rfl
  · rfl

/-- The `F`-row embedding into the port domain. -/
def fRowEmb (hn : 1 ≤ c.tl) (pk : BN) : Bytes 22 × BN ↪ EncX c :=
  (Equiv.prodCongr (Equiv.refl _) msg1Equiv.symm).toEmbedding.trans (thRowEmb c 1 hn pk)

theorem encΩ_frow_local (hn : 1 ≤ c.tl) (ω : Ω128 c) (pk : BN) (H G : Bytes 22 × BN → BN)
    (x : EncX c)
    (h : encΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv H))) x ≠
      encΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv G))) x) :
    ∃ x', fRowEmb c hn pk x' = x ∧ H x' ≠ G x' := by
  obtain ⟨x', hx, hne⟩ := encΩ_row_local c 1 hn ω pk (fRowEquiv H) (fRowEquiv G) x h
  refine ⟨(x'.1, msg1Equiv x'.2), ?_, hne⟩
  rw [← hx]
  change thRowEmb c 1 hn pk (x'.1, msg1Equiv.symm (msg1Equiv x'.2)) = _
  rw [Equiv.symm_apply_apply]

/-- **Per world and seed**, WOTS-chain TCR. -/
theorem tcrT_row_inner_le (hn : 1 ≤ c.tl) (q' : ℕ) (ω : Ω128 c) (pk : BN)
    (hModel : ∀ st : Open.RState Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × BN) q',
        ∀ (T : ThTab c) (Ev : ℕ × BN → Prop) [DecidablePred Ev],
          Mo.prob (encΩ (ω.withThash T)) Ev =
            qWeight Ev ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              (ω.withThash T))).forge st pk) F.ρ₀) :
    ∑ R : Bytes 22 × BN → BN, (Fintype.card (Bytes 22 × BN → BN) : ℝ≥0∞)⁻¹ *
      tcrInner (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) := by
  have hM : ∀ s : Open.RState Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × BN) BN (ℕ × BN) q',
        ∀ R (Ev : ℕ × BN → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (fRowEmb c hn pk)
      (fun R ↦ encΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
      (encΩ_frow_local c hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcr_row_avg_le (wotsTcrProblemT Link.vp (primsΩ ω) pkSeedDist₀) pk
    (fun R ↦ (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
      pkSeedDist₀).th.eval)
    (fun R t m ↦ wots_eval_row c pkSeedDist₀ hn ω pk R t m)
    (fun R ↦ (wotsTcrProblemT Link.vp (primsΩ (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))
      pkSeedDist₀).thColl.eval)
    (fun R R' i t x h ↦ wots_coll_row c pkSeedDist₀ ω pk R R' i t x h)
    (Open.wotsTcrPhase1 (vp := Link.vp) (prims := primsΩ ω) pkSeedDist₀)
    (fun R s ↦ (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT 1 ω.thash pk (fRowEquiv R))))).forge s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [tcrInnerT_row_eq]
  qtcr_kernel_rfl

/-- **The WOTS-chain TCR term** (`qrTcrT`), given the hybrid model of its second phase. -/
theorem tcrT_term (hn : 1 ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.RState Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × Bytes Link.vp.params.n) q',
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × Bytes Link.vp.params.n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) with hε
  have hεe : ε = epsTcr0 q' := by
    rw [hε, epsTcr0, card_cast_N128 card_bytes_n]
  rw [← hεe]
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  set g : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    tcrInner (qrTcrT (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hg
  have hsd : ∀ ω : Ω128 c,
      (wotsTcrProblemT Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (wotsTcrProblemT Link.vp (primsΩ ω) pkSeedDist₀).th.seedGen (· = pk) * g ω pk) ≤ ε
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
    rw [avΩ_resample_frow c hn pk]
    refine le_trans (avΩ_mono c fun ω ↦ ?_) (le_of_eq (avΩ_const c ε))
    exact tcrT_row_inner_le c optRand₀ pkSeedDist₀ F hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
    _ = ε := one_mul ε

end inst

end Reduction

#print axioms Reduction.tcrT_term
#print axioms Reduction.tcr_term
