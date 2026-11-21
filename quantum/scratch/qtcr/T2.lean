import Integration.SlhDsaComposedEnc
import Reduction.Open.Phase1Tcr
import PQ.Interactive.QromBridgeTcr
import PQ.QROM.HybridPullback

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace Reduction

attribute [local irreducible] arityTargets tcrTargets

/-! ## Rows of the `Thash` component -/

/-- Replace the `Thash` component. -/
abbrev FinFns.withThash {p : Params} {c : Caps} (ω : FinFns p c)
    (T : Bytes p.n → Bytes 22 → BList (Bytes p.n) c.tl → Bytes p.n) : FinFns p c :=
  { ω with thash := T }

/-- Messages of arity `n`. -/
abbrev ArMsg (n : ℕ) : Type := {xs : List BN // xs.length = n}

instance (n : ℕ) : Fintype (ArMsg n) := inferInstanceAs (Fintype (List.Vector BN n))

/-- A row of `Thash` at one seed and arity: tweak and arity-`n` message to value. -/
abbrev ThRow (n : ℕ) : Type := Bytes 22 × ArMsg n → BN

/-- `Thash` tables of the bounded world. -/
abbrev ThTab (c : Caps) : Type := BN → Bytes 22 → BList BN c.tl → BN

lemma BList.ofList_ofFn {α : Type} {L : ℕ} (b : BList α L) (h : (List.ofFn b.2).length ≤ L) :
    BList.ofList (List.ofFn b.2) h = b := by
  obtain ⟨⟨k, hk⟩, f⟩ := b
  unfold BList.ofList
  have hl : (List.ofFn f).length = k := List.length_ofFn
  refine Sigma.ext (Fin.ext hl) ?_
  refine (Fin.heq_fun_iff hl).2 fun i ↦ ?_
  simp

/-- The table `T` with its row at seed `pk`, arity `n`, replaced by `R`. -/
def rowT {c : Caps} (n : ℕ) (T : ThTab c) (pk : BN) (R : ThRow n) : ThTab c :=
  fun pk' a b ↦
    if h : pk' = pk ∧ (List.ofFn b.2).length = n then R (a, ⟨List.ofFn b.2, h.2⟩) else T pk' a b

/-- The row of `T` at seed `pk`, arity `n`. -/
def rowOf {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) : ThRow n :=
  fun x ↦ T pk x.1 (BList.ofList x.2.1 (x.2.2.trans_le hn))

lemma rowT_ofList {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) (R : ThRow n)
    (a : Bytes 22) (xs : ArMsg n) :
    rowT n T pk R pk a (BList.ofList xs.1 (xs.2.trans_le hn)) = R (a, xs) := by
  have hx : List.ofFn (BList.ofList (L := c.tl) xs.1 (xs.2.trans_le hn)).2 = xs.1 := BList.ofFn_ofList _ _
  unfold rowT
  rw [dif_pos ⟨rfl, by rw [hx]; exact xs.2⟩]
  congr 2
  exact Subtype.ext hx

lemma rowOf_rowT {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) (R : ThRow n) :
    rowOf n hn (rowT n T pk R) pk = R := by
  funext x
  exact rowT_ofList n hn T pk R x.1 x.2

lemma rowT_rowOf {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) (R : ThRow n) :
    rowT n (rowT n T pk R) pk (rowOf n hn T pk) = T := by
  funext pk' a b
  unfold rowT
  by_cases h : pk' = pk ∧ (List.ofFn b.2).length = n
  · rw [dif_pos h]
    obtain ⟨rfl, h2⟩ := h
    unfold rowOf
    dsimp only
    rw [BList.ofList_ofFn]
  · rw [dif_neg h, dif_neg h]

/-- Resampling one row of `Thash` does not change a uniform average. -/
theorem avΩ_resample_row (c : Caps) (n : ℕ) (hn : n ≤ c.tl) (pk : BN) (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ R : ThRow n,
      (Fintype.card (ThRow n) : ℝ≥0∞)⁻¹ * f (ω.withThash (rowT n ω.thash pk R)) := by
  classical
  unfold avΩ
  set u : ℝ≥0∞ := (Fintype.card (Ω128 c) : ℝ≥0∞)⁻¹ with hu
  have hw : ∀ ω : Ω128 c, unifW (Ω128 c) ω = u := fun _ ↦ rfl
  simp only [hw]
  set cG : ℝ≥0∞ := (Fintype.card (ThRow n) : ℝ≥0∞) with hcG
  have hne : cG ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hnt : cG ≠ ⊤ := ENNReal.natCast_ne_top _
  let Φ : Ω128 c × ThRow n → Ω128 c × ThRow n :=
    fun p ↦ (p.1.withThash (rowT n p.1.thash pk p.2), rowOf n hn p.1.thash pk)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨ω, R⟩
    simp only [Φ, FinFns.withThash, rowOf_rowT, rowT_rowOf]
  have h := Equiv.sum_comp hΦ.toPerm fun p : Ω128 c × ThRow n ↦ f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h' : ∑ ω : Ω128 c, ∑ R : ThRow n, f (ω.withThash (rowT n ω.thash pk R)) =
      cG * ∑ ω : Ω128 c, f ω := by
    refine h.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum, hcG]
  calc ∑ ω : Ω128 c, u * f ω = u * (cG⁻¹ * (cG * ∑ ω : Ω128 c, f ω)) := by
        rw [← mul_assoc cG⁻¹, ENNReal.inv_mul_cancel hne hnt, one_mul, Finset.mul_sum]
    _ = _ := by
        rw [← h', Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ω _ ↦ ?_
        rw [Finset.mul_sum, Finset.mul_sum]

elab "qtcr_kernel_rfl" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let t := (← Lean.instantiateMVars (← g.getType)).consumeMData
  let some (_, a, _) := t.eq? | throwError "qtcr_kernel_rfl: not an equality"
  let pf ← Lean.Meta.mkEqRefl a
  g.assign pf
  Lean.Elab.Tactic.replaceMainGoal []

/-- The winning weight of an SM-TCR adversary at a fixed seed. -/
noncomputable def tcrInner {W : Type} [Fintype W] {ι PkSeed Tweak M Y : Type} [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {P : TweakableHash.SM_DT_TCR_Problem ι PkSeed Tweak M Y}
    (adv : QSM_DT_TCR_Adversary W P) (pk : PkSeed) : ℝ≥0∞ :=
  qWeight (· = true)
    (liftU ((simulateQ (TweakableHash.SM_DT_TCR_oracles P pk) adv.choose).run ([], [])) >>= fun r ↦
      adv.forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧ P.th.eval pk tm.1 jm.2 = P.th.eval pk tm.1 tm.2))) adv.ρ₀

theorem qSM_DT_TCR_Advantage_eq_tsum {W : Type} [Fintype W] {ι PkSeed Tweak M Y : Type}
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {P : TweakableHash.SM_DT_TCR_Problem ι PkSeed Tweak M Y} (adv : QSM_DT_TCR_Adversary W P) :
    qSM_DT_TCR_Advantage adv = ∑' pk, PQ.Interactive.prob P.th.seedGen (· = pk) * tcrInner adv pk := by
  unfold qSM_DT_TCR_Advantage qSM_DT_TCR_Experiment
  rw [qWeight_liftU_bind_tsum]
  rfl

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

theorem tcrInner_row_eq (n : ℕ) (ω : Ω128 c) (pk : BN) (R : ThRow n) :
    tcrInner (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (rowT n ω.thash pk R)))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_oracles
          (tcrWithEval (thashArityProblemT Link.vp (primsΩ ω) pkSeedDist₀ n)
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) pkSeedDist₀ n).th.eval
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) pkSeedDist₀ n).thColl.eval) pk)
          (Open.tcrPhase1 Link.vp (primsΩ ω) n)).run ([], [])) >>= fun r ↦
        (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.withThash (rowT n ω.thash pk R)))).forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) pkSeedDist₀ n).th.eval pk tm.1 jm.2 =
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) pkSeedDist₀ n).th.eval pk tm.1 tm.2))) F.ρ₀ := by
  have hch : ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (rowT n ω.thash pk R)))).choose :
      OracleComp (Open.TcrP1Spec (primsΩ ω) n) (Open.TcrP1State Link.vp (primsΩ ω))) =
      Open.tcrPhase1 Link.vp (primsΩ ω) n := by
    have h2 := Open.bTcrArM_choose_eq n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (rowT n ω.thash pk R))).toClassical
    have h3 : (Open.tcrPhase1 Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) n :
        OracleComp (Open.TcrP1Spec (primsΩ ω) n) _) = Open.tcrPhase1 Link.vp (primsΩ ω) n := by
      qtcr_kernel_rfl
    unfold qbTcrArM qTcrOfClassical
    dsimp only
    exact h2.trans h3
  unfold tcrInner
  rw [hch]
  qtcr_kernel_rfl

theorem thash_row (ω : Ω128 c) (n : ℕ) (pk : BN) (R : ThRow n) (pk' : BN) (a : Bytes 22)
    (xs : List BN) :
    (primsΩ (ω.withThash (rowT n ω.thash pk R))).Thash pk' a xs =
      if h : xs.length ≤ c.tl then rowT n ω.thash pk R pk' a (BList.ofList xs h) else default :=
  rfl

theorem arity_eval_row (n : ℕ) (hn : n ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : ThRow n)
    (a : Bytes 22) (m : ArMsg n) :
    (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) pkSeedDist₀ n).th.eval
      pk a m = R (a, m) := by
  change (primsΩ (ω.withThash (rowT n ω.thash pk R))).Thash pk a m.1 = R (a, m)
  rw [thash_row, dif_pos (m.2.trans_le hn)]
  exact rowT_ofList n hn ω.thash pk R a m

theorem arity_coll_row (n : ℕ) (ω : Ω128 c) (pk : BN) (R R' : ThRow n) (i : Unit)
    (a : Bytes 22) (xs : List BN) (h : ∀ m, R (a, m) = R' (a, m)) :
    (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R))) pkSeedDist₀ n).thColl.eval
      i pk a xs =
    (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R'))) pkSeedDist₀ n).thColl.eval
      i pk a xs := by
  change (primsΩ (ω.withThash (rowT n ω.thash pk R))).Thash pk a xs =
    (primsΩ (ω.withThash (rowT n ω.thash pk R'))).Thash pk a xs
  rw [thash_row, thash_row]
  split_ifs with hl
  · unfold rowT
    split_ifs with h2
    · exact h _
    · rfl
  · rfl

/-- The row embedding into the port domain. -/
def rowEmb (n : ℕ) (hn : n ≤ c.tl) (pk : BN) : Bytes 22 × ArMsg n ↪ EncX c where
  toFun x := Sum.inl (pk, x.1, BList.ofList x.2.1 (x.2.2.trans_le hn))
  inj' := by
    rintro ⟨a, xs⟩ ⟨b, ys⟩ h
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, h⟩ := h
    have h1 := congrArg (fun z : BList BN c.tl ↦ List.ofFn z.2) h
    simp only [BList.ofFn_ofList] at h1
    rw [Subtype.ext h1]

theorem encΩ_row_local (n : ℕ) (hn : n ≤ c.tl) (ω : Ω128 c) (pk : BN) (H G : ThRow n)
    (x : EncX c)
    (h : encΩ (ω.withThash (rowT n ω.thash pk H)) x ≠ encΩ (ω.withThash (rowT n ω.thash pk G)) x) :
    ∃ x', rowEmb c n hn pk x' = x ∧ H x' ≠ G x' := by
  rcases x with ⟨pk', a, b⟩ | x | x | x
  · change (rowT n ω.thash pk H pk' a b, (0 : Bytes Link.vp.params.m)) ≠
      (rowT n ω.thash pk G pk' a b, 0) at h
    unfold rowT at h
    split_ifs at h with hc
    · obtain ⟨rfl, hl⟩ := hc
      refine ⟨(a, ⟨List.ofFn b.2, hl⟩), ?_, fun he ↦ h (by rw [he])⟩
      change Sum.inl (pk', a, BList.ofList (List.ofFn b.2) _) = Sum.inl (pk', a, b)
      rw [BList.ofList_ofFn]
    · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h
  · exact absurd rfl h

/-- **Per world and seed**: the row-average of the arity-`n` game's winning weight at the seed. -/
theorem tcr_row_inner_le (n : ℕ) (hn : n ≤ c.tl) (q' : ℕ) (ω : Ω128 c) (pk : BN)
    (hModel : ∀ st : Open.TcrP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY (ℕ × ArMsg n) q',
        ∀ (T : ThTab c) (Ev : ℕ × ArMsg n → Prop) [DecidablePred Ev],
          Mo.prob (encΩ (ω.withThash T)) Ev =
            qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              (ω.withThash T))).forge st pk) F.ρ₀) :
    ∑ R : ThRow n, (Fintype.card (ThRow n) : ℝ≥0∞)⁻¹ *
      tcrInner (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
        (ω.withThash (rowT n ω.thash pk R)))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) := by
  have hM : ∀ s : Open.TcrP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × ArMsg n) BN (ℕ × ArMsg n) q',
        ∀ R (Ev : ℕ × ArMsg n → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.withThash (rowT n ω.thash pk R)))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (rowEmb c n hn pk) (fun R ↦ encΩ (ω.withThash (rowT n ω.thash pk R)))
      (encΩ_row_local c n hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcr_row_avg_le (thashArityProblemT Link.vp (primsΩ ω) pkSeedDist₀ n) pk
    (fun R ↦ (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R)))
      pkSeedDist₀ n).th.eval)
    (fun R t m ↦ arity_eval_row c pkSeedDist₀ n hn ω pk R t m)
    (fun R ↦ (thashArityProblemT Link.vp (primsΩ (ω.withThash (rowT n ω.thash pk R)))
      pkSeedDist₀ n).thColl.eval)
    (fun R R' i t x h ↦ arity_coll_row c pkSeedDist₀ n ω pk R R' i t x h)
    (Open.tcrPhase1 Link.vp (primsΩ ω) n)
    (fun R s ↦ (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (rowT n ω.thash pk R)))).forge s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [tcrInner_row_eq]
  qtcr_kernel_rfl

/-- **The class-TCR term at arity `n`**, for every port forger over the fixed encoding, given the
hybrid model of the reduction's second phase (`hModel`). -/
theorem tcr_term (n : ℕ) (hn : n ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : Ω128 c) (st : Open.TcrP1State Link.vp (primsΩ ω₀))
        (pk : Bytes Link.vp.params.n),
      ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY
          (ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n}) q',
        ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
            Bytes Link.vp.params.n)
          (Ev : ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = n} → Prop)
          [DecidablePred Ev],
          Mo.prob (encΩ { ω₀ with thash := T }) Ev =
            qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
      (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 q' := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) with hε
  have hεe : ε = epsTcr0 q' := by
    rw [hε, epsTcr0, card_cast_N128 card_bytes_n]
  rw [← hεe]
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  set g : Ω128 c → BN → ℝ≥0∞ := fun ω pk ↦
    tcrInner (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)) pk with hg
  have hsd : ∀ ω : Ω128 c,
      (thashArityProblemT Link.vp (primsΩ ω) pkSeedDist₀ n).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avΩ c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (thashArityProblemT Link.vp (primsΩ ω) pkSeedDist₀ n).th.seedGen (· = pk) * g ω pk) ≤ ε
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
    rw [avΩ_resample_row c n hn pk]
    refine le_trans (avΩ_mono c fun ω ↦ ?_) (le_of_eq (avΩ_const c ε))
    exact tcr_row_inner_le c optRand₀ pkSeedDist₀ F n hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avΩ c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
    _ = ε := one_mul ε

end inst

end Reduction
#print axioms Reduction.tcr_term
