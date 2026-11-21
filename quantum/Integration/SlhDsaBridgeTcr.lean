import Integration.SlhDsaComposedEnc
import Reduction.Open.Phase1Tcr
import PQ.Interactive.QromBridgeTcr
import PQ.QROM.HybridPullback

/-!
# The class-TCR bridge (arity `1`, `2`, `len`, `k`), game side

NOT part of the default target; compiled as `scripts/check-integration.sh` step 3 does.

**Headline** `tcr_term`: for every port forger `F` over the fixed encoding `encΩ`, every arity
`n ≤ c.tl` and every `q'`,

  `avΩ c (fun ω ↦ qSM_DT_TCR_Advantage (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω)))
     ≤ epsTcr0 q'`

under ONE hypothesis `hModel`: for every world `ω₀`, first-phase state `st` and seed `pk`, the
second phase of the reduction (`(qbTcrArM n …).forge st pk`) has a `q'`-query hybrid model over
the port function, uniformly in the `Thash` component `T` of the world
(`Mo.prob (encΩ {ω₀ with thash := T}) Ev = qWeight Ev (forge at T) F.ρ₀`).  `hModel` is the
machine-side statement (agent `qmach`); it is NOT proved here.  The seed distribution
`pkSeedDist₀` is arbitrary.

`tcr_terms_four` packages the four arities `1, 2, len, k` in the form consumed by
`composed_of_linear_eps` (`h1`, `h2`, `hLen`, `hK` with `e· = epsTcr0 (q + r.tcr·)`), under the
single hypothesis "`hModel` at the four arities with counts `q + r.tcr·`" and `35 ≤ c.tl`.

Route (no `TcrValue`/`MixLE`):
1. `qSM_DT_TCR_Advantage_eq_tsum` (seed average), exchange with `avΩ`;
2. `avΩ_resample_row`: resample the `Thash` row at `(pk, arity n)` (`thRowT`, `thRowOf`);
3. the first phase is the forger-free program `Open.tcrPhase1` (`Open.bTcrArM_choose_eq`,
   kernel-checked `rfl` for the `Thash`-independence), the game oracles at the resampled world are
   `tcrWithEval` of the game at `ω` with the row as hash (`arity_eval_row`) and a collection that
   reads the row only at its own tweak (`arity_coll_row`);
4. the model is pulled back along `T ↦ encΩ {ω with thash := T}` restricted to the row
   (`HybridModel.pullback`, locality `encΩ_row_local`);
5. `PQ.Interactive.tcr_row_avg_le` (generic: invariance of the first phase under non-target
   row changes + `spr_embedded_obs_weighted_le`), `card_bytes_n`.
-/

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
def thRowT {c : Caps} (n : ℕ) (T : ThTab c) (pk : BN) (R : ThRow n) : ThTab c :=
  fun pk' a b ↦
    if h : pk' = pk ∧ (List.ofFn b.2).length = n then R (a, ⟨List.ofFn b.2, h.2⟩) else T pk' a b

/-- The row of `T` at seed `pk`, arity `n`. -/
def thRowOf {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) : ThRow n :=
  fun x ↦ T pk x.1 (BList.ofList x.2.1 (x.2.2.trans_le hn))

lemma thRowT_ofList {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) (R : ThRow n)
    (a : Bytes 22) (xs : ArMsg n) :
    thRowT n T pk R pk a (BList.ofList xs.1 (xs.2.trans_le hn)) = R (a, xs) := by
  have hx : List.ofFn (BList.ofList (L := c.tl) xs.1 (xs.2.trans_le hn)).2 = xs.1 := BList.ofFn_ofList _ _
  unfold thRowT
  rw [dif_pos ⟨rfl, by rw [hx]; exact xs.2⟩]
  congr 2
  exact Subtype.ext hx

lemma thRowOf_thRowT {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) (R : ThRow n) :
    thRowOf n hn (thRowT n T pk R) pk = R := by
  funext x
  exact thRowT_ofList n hn T pk R x.1 x.2

lemma thRowT_thRowOf {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab c) (pk : BN) (R : ThRow n) :
    thRowT n (thRowT n T pk R) pk (thRowOf n hn T pk) = T := by
  funext pk' a b
  unfold thRowT
  by_cases h : pk' = pk ∧ (List.ofFn b.2).length = n
  · rw [dif_pos h]
    obtain ⟨rfl, h2⟩ := h
    unfold thRowOf
    dsimp only
    rw [BList.ofList_ofFn]
  · rw [dif_neg h, dif_neg h]

/-- Resampling one row of `Thash` does not change a uniform average. -/
theorem avΩ_resample_row (c : Caps) (n : ℕ) (hn : n ≤ c.tl) (pk : BN) (f : Ω128 c → ℝ≥0∞) :
    avΩ c f = avΩ c fun ω ↦ ∑ R : ThRow n,
      (Fintype.card (ThRow n) : ℝ≥0∞)⁻¹ * f (ω.withThash (thRowT n ω.thash pk R)) := by
  classical
  unfold avΩ
  set u : ℝ≥0∞ := (Fintype.card (Ω128 c) : ℝ≥0∞)⁻¹ with hu
  have hw : ∀ ω : Ω128 c, unifW (Ω128 c) ω = u := fun _ ↦ rfl
  simp only [hw]
  set cG : ℝ≥0∞ := (Fintype.card (ThRow n) : ℝ≥0∞) with hcG
  have hne : cG ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hnt : cG ≠ ⊤ := ENNReal.natCast_ne_top _
  let Φ : Ω128 c × ThRow n → Ω128 c × ThRow n :=
    fun p ↦ (p.1.withThash (thRowT n p.1.thash pk p.2), thRowOf n hn p.1.thash pk)
  have hΦ : Function.Involutive Φ := by
    rintro ⟨ω, R⟩
    simp only [Φ, FinFns.withThash, thRowOf_thRowT, thRowT_thRowOf]
  have h := Equiv.sum_comp hΦ.toPerm fun p : Ω128 c × ThRow n ↦ f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  have h' : ∑ ω : Ω128 c, ∑ R : ThRow n, f (ω.withThash (thRowT n ω.thash pk R)) =
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

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes Link.vp.params.n → Bytes Link.vp.params.n → ProbComp (Bytes Link.vp.params.n))
  (pkSeedDist₀ : ProbComp (Bytes Link.vp.params.n))
  (F : PortForger (EncX c) EncY E)

theorem tcrInner_row_eq (n : ℕ) (ω : Ω128 c) (pk : BN) (R : ThRow n) :
    tcrInner (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT n ω.thash pk R)))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_oracles
          (tcrWithEval (thashArityProblemT Link.vp (primsΩ ω) pkSeedDist₀ n)
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) pkSeedDist₀ n).th.eval
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) pkSeedDist₀ n).thColl.eval) pk)
          (Open.tcrPhase1 Link.vp (primsΩ ω) n)).run ([], [])) >>= fun r ↦
        (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
          (ω.withThash (thRowT n ω.thash pk R)))).forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) pkSeedDist₀ n).th.eval pk tm.1 jm.2 =
            (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) pkSeedDist₀ n).th.eval pk tm.1 tm.2))) F.ρ₀ := by
  have hch : ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT n ω.thash pk R)))).choose :
      OracleComp (Open.TcrP1Spec (primsΩ ω) n) (Open.TcrP1State Link.vp (primsΩ ω))) =
      Open.tcrPhase1 Link.vp (primsΩ ω) n := by
    have h2 := Open.bTcrArM_choose_eq n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT n ω.thash pk R))).toClassical
    have h3 : (Open.tcrPhase1 Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) n :
        OracleComp (Open.TcrP1Spec (primsΩ ω) n) _) = Open.tcrPhase1 Link.vp (primsΩ ω) n := by
      qtcr_kernel_rfl
    unfold qbTcrArM qTcrOfClassical
    dsimp only
    exact h2.trans h3
  unfold tcrInner
  rw [hch]
  qtcr_kernel_rfl

theorem thash_thRowT (ω : Ω128 c) (n : ℕ) (pk : BN) (R : ThRow n) (pk' : BN) (a : Bytes 22)
    (xs : List BN) :
    (primsΩ (ω.withThash (thRowT n ω.thash pk R))).Thash pk' a xs =
      if h : xs.length ≤ c.tl then thRowT n ω.thash pk R pk' a (BList.ofList xs h) else default :=
  rfl

theorem arity_eval_row (n : ℕ) (hn : n ≤ c.tl) (ω : Ω128 c) (pk : BN) (R : ThRow n)
    (a : Bytes 22) (m : ArMsg n) :
    (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) pkSeedDist₀ n).th.eval
      pk a m = R (a, m) := by
  change (primsΩ (ω.withThash (thRowT n ω.thash pk R))).Thash pk a m.1 = R (a, m)
  rw [thash_thRowT, dif_pos (m.2.trans_le hn)]
  exact thRowT_ofList n hn ω.thash pk R a m

theorem arity_coll_row (n : ℕ) (ω : Ω128 c) (pk : BN) (R R' : ThRow n) (i : Unit)
    (a : Bytes 22) (xs : List BN) (h : ∀ m, R (a, m) = R' (a, m)) :
    (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R))) pkSeedDist₀ n).thColl.eval
      i pk a xs =
    (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R'))) pkSeedDist₀ n).thColl.eval
      i pk a xs := by
  change (primsΩ (ω.withThash (thRowT n ω.thash pk R))).Thash pk a xs =
    (primsΩ (ω.withThash (thRowT n ω.thash pk R'))).Thash pk a xs
  rw [thash_thRowT, thash_thRowT]
  split_ifs with hl
  · unfold thRowT
    split_ifs with h2
    · exact h _
    · rfl
  · rfl

/-- The row embedding into the port domain. -/
def thRowEmb (n : ℕ) (hn : n ≤ c.tl) (pk : BN) : Bytes 22 × ArMsg n ↪ EncX c where
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
    (h : encΩ (ω.withThash (thRowT n ω.thash pk H)) x ≠ encΩ (ω.withThash (thRowT n ω.thash pk G)) x) :
    ∃ x', thRowEmb c n hn pk x' = x ∧ H x' ≠ G x' := by
  rcases x with ⟨pk', a, b⟩ | x | x | x
  · change (thRowT n ω.thash pk H pk' a b, (0 : Bytes Link.vp.params.m)) ≠
      (thRowT n ω.thash pk G pk' a b, 0) at h
    unfold thRowT at h
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
        (ω.withThash (thRowT n ω.thash pk R)))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card BN : ℝ≥0∞) := by
  have hM : ∀ s : Open.TcrP1State Link.vp (primsΩ ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × ArMsg n) BN (ℕ × ArMsg n) q',
        ∀ R (Ev : ℕ × ArMsg n → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
            (ω.withThash (thRowT n ω.thash pk R)))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (thRowEmb c n hn pk) (fun R ↦ encΩ (ω.withThash (thRowT n ω.thash pk R)))
      (encΩ_row_local c n hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcr_row_avg_le (thashArityProblemT Link.vp (primsΩ ω) pkSeedDist₀ n) pk
    (fun R ↦ (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R)))
      pkSeedDist₀ n).th.eval)
    (fun R t m ↦ arity_eval_row c pkSeedDist₀ n hn ω pk R t m)
    (fun R ↦ (thashArityProblemT Link.vp (primsΩ (ω.withThash (thRowT n ω.thash pk R)))
      pkSeedDist₀ n).thColl.eval)
    (fun R R' i t x h ↦ arity_coll_row c pkSeedDist₀ n ω pk R R' i t x h)
    (Open.tcrPhase1 Link.vp (primsΩ ω) n)
    (fun R s ↦ (qbTcrArM n (internalΩ c optRand₀ pkSeedDist₀ encΩ F
      (ω.withThash (thRowT n ω.thash pk R)))).forge s pk) F.ρ₀ q' hM
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

theorem len_eq_35 : Link.vp.params.len = 35 := rfl
theorem k_eq_14 : Link.vp.params.k = 14 := rfl

/-- **The four class-TCR terms** (arities `1`, `2`, `len`, `k`) in the form consumed by
`composed_of_linear_eps` (`h1`, `h2`, `hLen`, `hK`), under the single hypothesis `hModel`: the
second phase of `qbTcrArM n` has a hybrid model with `q + r.tcr·` queries at each of the four
arities, and `35 ≤ c.tl`. -/
theorem tcr_terms_four (q : ℕ) (r : RedCounts) (htl : 35 ≤ c.tl)
    (hModel : ∀ nq ∈ [(1, q + r.tcr1), (2, q + r.tcr2), (Link.vp.params.len, q + r.tcrLen),
        (Link.vp.params.k, q + r.tcrK)],
      ∀ (ω₀ : Ω128 c) (st : Open.TcrP1State Link.vp (primsΩ ω₀)) (pk : Bytes Link.vp.params.n),
        ∃ Mo : PQ.QROM.HybridModel (EncX c) EncY
            (ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = nq.1}) nq.2,
          ∀ (T : Bytes Link.vp.params.n → Bytes 22 → BList (Bytes Link.vp.params.n) c.tl →
              Bytes Link.vp.params.n)
            (Ev : ℕ × {xs : List (Bytes Link.vp.params.n) // xs.length = nq.1} → Prop)
            [DecidablePred Ev],
            Mo.prob (encΩ { ω₀ with thash := T }) Ev =
              qWeight Ev ((qbTcrArM nq.1 (internalΩ c optRand₀ pkSeedDist₀ encΩ F
                { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM 1 (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 (q + r.tcr1) ∧
      avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM 2 (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤ epsTcr0 (q + r.tcr2) ∧
      avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM Link.vp.params.len (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
          epsTcr0 (q + r.tcrLen) ∧
      avΩ c (fun ω ↦ qSM_DT_TCR_Advantage
        (qbTcrArM Link.vp.params.k (internalΩ c optRand₀ pkSeedDist₀ encΩ F ω))) ≤
          epsTcr0 (q + r.tcrK) :=
  ⟨tcr_term c optRand₀ pkSeedDist₀ F 1 (by omega) _ (hModel (1, q + r.tcr1) (by simp)),
    tcr_term c optRand₀ pkSeedDist₀ F 2 (by omega) _ (hModel (2, q + r.tcr2) (by simp)),
    tcr_term c optRand₀ pkSeedDist₀ F Link.vp.params.len (by rw [len_eq_35]; exact htl) _
      (hModel (Link.vp.params.len, q + r.tcrLen) (by simp)),
    tcr_term c optRand₀ pkSeedDist₀ F Link.vp.params.k (by rw [k_eq_14]; omega) _
      (hModel (Link.vp.params.k, q + r.tcrK) (by simp))⟩

end inst

end Reduction

#print axioms Reduction.avΩ_resample_row
#print axioms Reduction.tcrInner_row_eq
#print axioms Reduction.arity_eval_row
#print axioms Reduction.arity_coll_row
#print axioms Reduction.encΩ_row_local
#print axioms Reduction.tcr_row_inner_le
#print axioms Reduction.tcr_term
#print axioms Reduction.tcr_terms_four
