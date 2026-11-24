import Integration.SlhDsaSetTcrMach
import Integration.SlhDsaSetPrf

namespace Reduction.SetOracle
open MLink OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal PQ.Interactive PQ.QROM Quantum
open scoped ComplexOrder
attribute [local irreducible] arityTargets tcrTargets
variable (S : Sha2Set)

noncomputable def avg (c : Caps) (f : FinFns S.vp.params c → ℝ≥0∞) := ∑ g, unifW _ g * f g
theorem avg_mono (c : Caps) {f g : FinFns S.vp.params c → ℝ≥0∞} (h : ∀ w, f w ≤ g w) :
    avg S c f ≤ avg S c g := Finset.sum_le_sum fun w _ => mul_le_mul' le_rfl (h w)
theorem avg_const (c : Caps) (v : ℝ≥0∞) : avg S c (fun _ => v) = v := by
  simp only [avg, ← Finset.sum_mul, sum_unifW, one_mul]

/-- Messages of arity `n`. -/
abbrev ArMsg (n : ℕ) : Type := {xs : List S.Node // xs.length = n}

instance (n : ℕ) : Fintype (ArMsg S n) := inferInstanceAs (Fintype (List.Vector S.Node n))

/-- A row of `Thash` at one seed and arity: tweak and arity-`n` message to value. -/
abbrev ThRow (n : ℕ) : Type := Bytes 22 × ArMsg S n → S.Node

/-- `Thash` tables of the bounded world. -/
abbrev ThTab (c : Caps) : Type := S.Node → Bytes 22 → BList S.Node c.tl → S.Node

/-- The table `T` with its row at seed `pk`, arity `n`, replaced by `R`. -/
def thRowT {c : Caps} (n : ℕ) (T : ThTab S c) (pk : S.Node) (R : ThRow S n) : ThTab S c :=
  fun pk' a b ↦
    if h : pk' = pk ∧ (List.ofFn b.2).length = n then R (a, ⟨List.ofFn b.2, h.2⟩) else T pk' a b

/-- The row of `T` at seed `pk`, arity `n`. -/
def thRowOf {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab S c) (pk : S.Node) : ThRow S n :=
  fun x ↦ T pk x.1 (BList.ofList x.2.1 (x.2.2.trans_le hn))

lemma thRowT_ofList {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab S c) (pk : S.Node) (R : ThRow S n)
    (a : Bytes 22) (xs : ArMsg S n) :
    thRowT S n T pk R pk a (BList.ofList xs.1 (xs.2.trans_le hn)) = R (a, xs) := by
  have hx : List.ofFn (BList.ofList (L := c.tl) xs.1 (xs.2.trans_le hn)).2 = xs.1 := BList.ofFn_ofList _ _
  unfold thRowT
  rw [dite_eq_left ⟨rfl, by rw [hx]; exact xs.2⟩]
  congr 2
  exact Subtype.ext hx

lemma thRowOf_thRowT {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab S c) (pk : S.Node) (R : ThRow S n) :
    thRowOf S n hn (thRowT S n T pk R) pk = R := by
  funext x
  exact thRowT_ofList S n hn T pk R x.1 x.2

lemma thRowT_thRowOf {c : Caps} (n : ℕ) (hn : n ≤ c.tl) (T : ThTab S c) (pk : S.Node) (R : ThRow S n) :
    thRowT S n (thRowT S n T pk R) pk (thRowOf S n hn T pk) = T := by
  funext pk' a b
  unfold thRowT
  by_cases h : pk' = pk ∧ (List.ofFn b.2).length = n
  · rw [dite_eq_left h]
    obtain ⟨rfl, h2⟩ := h
    unfold thRowOf
    dsimp only
    rw [BList.ofList_ofFn]
  · rw [dite_eq_right h, dite_eq_right h]

theorem avg_row (c : Caps) (n : ℕ) (hn : n ≤ c.tl) (pk : S.Node) (f : FinFns S.vp.params c → ℝ≥0∞) :
    avg S c f = avg S c fun g ↦ ∑ r : ThRow S n, unifW _ r * f (g.withThash (thRowT S n g.thash pk r)) :=
  avg_resample (Ω := FinFns S.vp.params c) (T := ThRow S n) (fun g r ↦ g.withThash (thRowT S n g.thash pk r)) (fun g ↦ thRowOf S n hn g.thash pk)
    (by
      rintro ⟨g,r⟩
      change (g.withThash (thRowT S n (thRowT S n g.thash pk r) pk (thRowOf S n hn g.thash pk)),
        thRowOf S n hn (thRowT S n g.thash pk r) pk) = (g,r)
      rw [thRowT_thRowOf S, thRowOf_thRowT S]) f

section inst

variable {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : S.Node → S.Node → ProbComp S.Node)
  (pkSeedDist₀ : ProbComp S.Node)
  (F : PortForger (Input S c) (Output S) E)

theorem tcrInner_row_eq (n : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node) (R : ThRow S n) :
    tcrInner (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S n ω.thash pk R)))) pk =
    qWeight (· = true)
      (liftU ((simulateQ (TweakableHash.SM_DT_TCR_oracles
          (tcrWithEval (thashArityProblemT S.vp (worldPrims ω) pkSeedDist₀ n)
            (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) pkSeedDist₀ n).th.eval
            (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) pkSeedDist₀ n).thColl.eval) pk)
          (Open.tcrPhase1 S.vp (worldPrims ω) n)).run ([], [])) >>= fun r ↦
        (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
          (ω.withThash (thRowT S n ω.thash pk R)))).forge r.1 pk >>= fun jm ↦
        match r.2.1[jm.1]? with
        | none => pure false
        | some tm =>
          pure (decide (jm.2 ≠ tm.2 ∧
            (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) pkSeedDist₀ n).th.eval pk tm.1 jm.2 =
            (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) pkSeedDist₀ n).th.eval pk tm.1 tm.2))) F.ρ₀ := by
  have hch : ((qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S n ω.thash pk R)))).choose :
      OracleComp (Open.TcrP1Spec (worldPrims ω) n) (Open.TcrP1State S.vp (worldPrims ω))) =
      Open.tcrPhase1 S.vp (worldPrims ω) n := by
    have h2 := Open.bTcrArM_choose_eq n (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S n ω.thash pk R))).toClassical
    have h3 : (Open.tcrPhase1 S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) n :
        OracleComp (Open.TcrP1Spec (worldPrims ω) n) _) = Open.tcrPhase1 S.vp (worldPrims ω) n := by
      qtcr_kernel_rfl
    unfold qbTcrArM qTcrOfClassical
    dsimp only
    exact h2.trans h3
  unfold tcrInner
  rw [hch]
  qtcr_kernel_rfl

theorem thash_thRowT (ω : FinFns S.vp.params c) (n : ℕ) (pk : S.Node) (R : ThRow S n) (pk' : S.Node) (a : Bytes 22)
    (xs : List S.Node) :
    (worldPrims (ω.withThash (thRowT S n ω.thash pk R))).Thash pk' a xs =
      if h : xs.length ≤ c.tl then thRowT S n ω.thash pk R pk' a (BList.ofList xs h) else default :=
  rfl

theorem arity_eval_row (n : ℕ) (hn : n ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (R : ThRow S n)
    (a : Bytes 22) (m : ArMsg S n) :
    (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) pkSeedDist₀ n).th.eval
      pk a m = R (a, m) := by
  change (worldPrims (ω.withThash (thRowT S n ω.thash pk R))).Thash pk a m.1 = R (a, m)
  rw [thash_thRowT, dite_eq_left (m.2.trans_le hn)]
  exact thRowT_ofList S n hn ω.thash pk R a m

theorem arity_coll_row (n : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node) (R R' : ThRow S n) (i : Unit)
    (a : Bytes 22) (xs : List S.Node) (h : ∀ m, R (a, m) = R' (a, m)) :
    (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R))) pkSeedDist₀ n).thColl.eval
      i pk a xs =
    (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R'))) pkSeedDist₀ n).thColl.eval
      i pk a xs := by
  change (worldPrims (ω.withThash (thRowT S n ω.thash pk R))).Thash pk a xs =
    (worldPrims (ω.withThash (thRowT S n ω.thash pk R'))).Thash pk a xs
  rw [thash_thRowT, thash_thRowT]
  split_ifs with hl
  · unfold thRowT
    split_ifs with h2
    · exact h _
    · rfl
  · rfl

/-- The row embedding into the port domain. -/
def thRowEmb (n : ℕ) (hn : n ≤ c.tl) (pk : S.Node) : Bytes 22 × ArMsg S n ↪ Input S c where
  toFun x := Sum.inl (pk, x.1, BList.ofList x.2.1 (x.2.2.trans_le hn))
  inj' := by
    rintro ⟨a, xs⟩ ⟨b, ys⟩ h
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl, h⟩ := h
    have h1 := congrArg (fun z : BList S.Node c.tl ↦ List.ofFn z.2) h
    simp only [BList.ofFn_ofList] at h1
    rw [Subtype.ext h1]

theorem encΩ_row_local (n : ℕ) (hn : n ≤ c.tl) (ω : FinFns S.vp.params c) (pk : S.Node) (H G : ThRow S n)
    (x : Input S c)
    (h : oracle S (ω.withThash (thRowT S n ω.thash pk H)) x ≠ oracle S (ω.withThash (thRowT S n ω.thash pk G)) x) :
    ∃ x', thRowEmb S c n hn pk x' = x ∧ H x' ≠ G x' := by
  rcases x with ⟨pk', a, b⟩ | x | x | x
  · change (thRowT S n ω.thash pk H pk' a b, (0 : Bytes S.vp.params.m)) ≠
      (thRowT S n ω.thash pk G pk' a b, 0) at h
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
theorem tcr_row_inner_le (n : ℕ) (hn : n ≤ c.tl) (q' : ℕ) (ω : FinFns S.vp.params c) (pk : S.Node)
    (hModel : ∀ st : Open.TcrP1State S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S) (ℕ × ArMsg S n) q',
        ∀ (T : ThTab S c) (Ev : ℕ × ArMsg S n → Prop) [DecidablePred Ev],
          Mo.prob (oracle S (ω.withThash T)) Ev =
            qWeight Ev ((qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
              (ω.withThash T))).forge st pk) F.ρ₀) :
    ∑ R : ThRow S n, (Fintype.card (ThRow S n) : ℝ≥0∞)⁻¹ *
      tcrInner (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
        (ω.withThash (thRowT S n ω.thash pk R)))) pk ≤
      (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card S.Node : ℝ≥0∞) := by
  have hM : ∀ s : Open.TcrP1State S.vp (worldPrims ω),
      ∃ Mo : PQ.QROM.HybridModel (Bytes 22 × ArMsg S n) S.Node (ℕ × ArMsg S n) q',
        ∀ R (Ev : ℕ × ArMsg S n → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev ((qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
            (ω.withThash (thRowT S n ω.thash pk R)))).forge s pk) F.ρ₀ := by
    intro s
    obtain ⟨Mo, hMo⟩ := hModel s
    refine ⟨Mo.pullback (thRowEmb S c n hn pk) (fun R ↦ oracle S (ω.withThash (thRowT S n ω.thash pk R)))
      (encΩ_row_local S c n hn ω pk), fun R Ev _ ↦ ?_⟩
    rw [HybridModel.pullback_prob]
    exact hMo _ Ev
  have key := tcr_row_avg_le (thashArityProblemT S.vp (worldPrims ω) pkSeedDist₀ n) pk
    (fun R ↦ (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R)))
      pkSeedDist₀ n).th.eval)
    (fun R t m ↦ arity_eval_row S c pkSeedDist₀ n hn ω pk R t m)
    (fun R ↦ (thashArityProblemT S.vp (worldPrims (ω.withThash (thRowT S n ω.thash pk R)))
      pkSeedDist₀ n).thColl.eval)
    (fun R R' i t x h ↦ arity_coll_row S c pkSeedDist₀ n ω pk R R' i t x h)
    (Open.tcrPhase1 S.vp (worldPrims ω) n)
    (fun R s ↦ (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
      (ω.withThash (thRowT S n ω.thash pk R)))).forge s pk) F.ρ₀ q' hM
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun R _ ↦ ?_)) key
  rw [tcrInner_row_eq]
  qtcr_kernel_rfl

/-- **The class-TCR term at arity `n`**, for every port forger over the fixed encoding, given the
hybrid model of the reduction's second phase (`hModel`). -/
theorem tcr_term (n : ℕ) (hn : n ≤ c.tl) (q' : ℕ)
    (hModel : ∀ (ω₀ : FinFns S.vp.params c) (st : Open.TcrP1State S.vp (worldPrims ω₀))
        (pk : S.Node),
      ∃ Mo : PQ.QROM.HybridModel (Input S c) (Output S)
          (ℕ × {xs : List (S.Node) // xs.length = n}) q',
        ∀ (T : S.Node → Bytes 22 → BList (S.Node) c.tl →
            S.Node)
          (Ev : ℕ × {xs : List (S.Node) // xs.length = n} → Prop)
          [DecidablePred Ev],
          Mo.prob (oracle S { ω₀ with thash := T }) Ev =
            qWeight Ev ((qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F
              { ω₀ with thash := T })).forge st pk) F.ρ₀) :
    avg S c (fun ω ↦ qSM_DT_TCR_Advantage
      (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F ω))) ≤ ((2 * (q' : ℝ≥0∞) + 1)^2 / 2^(8*S.vp.params.n)) := by
  set ε : ℝ≥0∞ := (2 * (q' : ℝ≥0∞) + 1) ^ 2 / (Fintype.card S.Node : ℝ≥0∞) with hε
  have hεe : ε = ((2 * (q' : ℝ≥0∞) + 1)^2 / 2^(8*S.vp.params.n)) := by
    rw [hε, card_bytes', pow_mul]; norm_num
  rw [← hεe]
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  set g : FinFns S.vp.params c → S.Node → ℝ≥0∞ := fun ω pk ↦
    tcrInner (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F ω)) pk with hg
  have hsd : ∀ ω : FinFns S.vp.params c,
      (thashArityProblemT S.vp (worldPrims ω) pkSeedDist₀ n).th.seedGen = pkSeedDist₀ :=
    fun _ ↦ rfl
  change avg S c (fun ω ↦ ∑' pk, PQ.Interactive.prob
    (thashArityProblemT S.vp (worldPrims ω) pkSeedDist₀ n).th.seedGen (· = pk) * g ω pk) ≤ ε
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
    rw [avg_row S c n hn pk]
    refine le_trans (avg_mono S c fun ω ↦ ?_) (le_of_eq (avg_const S c ε))
    exact tcr_row_inner_le S c optRand₀ pkSeedDist₀ F n hn q' ω pk (fun st ↦ hModel ω st pk)
  calc ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * avg S c (fun ω ↦ g ω pk)
      ≤ ∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk) * ε :=
        tsum_le_tsum fun pk ↦ mul_le_mul' le_rfl (hpk pk)
    _ = (∑' pk, PQ.Interactive.prob pkSeedDist₀ (· = pk)) * ε := ENNReal.tsum_mul_right
    _ ≤ 1 * ε := mul_le_mul' (tsum_prob_eq_le_one _) le_rfl
    _ = ε := one_mul ε

/-- All four class-TCR calls in the signature reduction have this bound at their
respective arities and the same key generation, signing and verification query cost. -/
theorem class_tcr_le (n : ℕ) (hn : n ≤ c.tl) (q qs : ℕ)
    (hq : ∀ pk, CountBound isPort (F.main pk) q)
    (hs : ∀ pk, CountBound isSign (F.main pk) qs) :
    avg S c (fun g => qSM_DT_TCR_Advantage (qbTcrArM n (internal S c optRand₀ pkSeedDist₀ F g))) ≤
      (2 * ((q + tcrMHashes S.vp qs : ℕ) : ℝ≥0∞) + 1)^2 / 2^(8*S.vp.params.n) :=
  tcr_term S c optRand₀ pkSeedDist₀ F n hn _ (tcr_hModel S c optRand₀ pkSeedDist₀ F n q qs hq hs)

end inst
end Reduction.SetOracle

#print axioms Reduction.SetOracle.class_tcr_le
