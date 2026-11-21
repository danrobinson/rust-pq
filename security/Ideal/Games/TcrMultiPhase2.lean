import Ideal.Games.TcrMultiBasic

/-!
# Multi-block SM-TCR in the ideal-compression model: phase two

`tcr_multi_phase2_le`: from a cache satisfying the phase-one invariant `MInv` with at most `N`
cells, the draw of `cv` followed by phase two of the game returns `true` with probability at most
`(q₂ + 2L + 4)·δ + O((q₂ + L)·(N + q₂ + L))/|St|`.

Proof.  `MP2.Good` is the good predicate of phase two: the cache is injective, no cached value
is `IV` or `cv`, every target's block list is complete and no other complete block list with the
target's tweak and `L` continuation blocks has the target's output.  A fresh sample `u` at a cell
`x` keeps `Good` unless `u` is `IV`, `cv`, a cached value, the row of a cached public cell or of
`x`, or has the output of the unique target whose tweak is carried by the unique block list
ending at `x` (`MP2.Good.update`, `MP2.prEvent_not_good_update_le`).  The capped step bound
`MP2.prEvent_bad_le_of_step_cap` sums this over the compression queries of phase two.  If the
final cache is good the game returns `false` (`MP2.not_good_of_win`): every routed evaluation
leaves its chain in the cache (`MP2.evalPub_settle`).
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash

variable {St Blk PkSeed Tweak M Y ι : Type}

namespace MP2

/-! ## The capped step bound -/

section StepBound

variable {ι₀ : Type} {spec : OracleSpec ι₀} {σ α : Type}

/-- **Step bound with a size cap.**  `sz s k` says that the state `s` has size at most `k`; a
`p`-step grows the size by at most one and the other steps do not grow it.  If from a non-bad
state of size at most `N` a `p`-step ends in a bad state with probability at most `ε`, and a
non-`p`-step never does, a computation making at most `n` `p`-queries, run from a non-bad state
of size `k` with `k + n ≤ N`, ends in a bad state with probability at most `n * ε`. -/
theorem prEvent_bad_le_of_step_cap (so : QueryImpl spec (StateT σ ProbComp)) (bad : σ → Prop)
    (sz : σ → ℕ → Prop) (p : ι₀ → Prop) [DecidablePred p] (ε : ℝ≥0∞) (N : ℕ)
    (hp : ∀ t s k, ¬ bad s → p t → sz s k → k ≤ N → Pr{let z ← (so t).run s}[bad z.2] ≤ ε)
    (hszp : ∀ t s k, sz s k → ∀ z ∈ support ((so t).run s), sz z.2 (k + 1))
    (hnp : ∀ t s, ¬ bad s → ¬ p t → ∀ z ∈ support ((so t).run s), ¬ bad z.2)
    (hsznp : ∀ t s k, ¬ p t → sz s k → ∀ z ∈ support ((so t).run s), sz z.2 k)
    (oa : OracleComp spec α) (n : ℕ) (hn : IsQueryBoundP oa p n) (s : σ) (k : ℕ)
    (hs : ¬ bad s) (hk : sz s k) (hcap : k + n ≤ N) :
    Pr{let z ← (simulateQ so oa).run s}[bad z.2] ≤ n * ε := by
  classical
  induction oa using OracleComp.inductionOn generalizing n s k with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure]
    simp only [hs, ↓reduceIte]
    exact zero_le
  | query_bind t f ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [run_simulateQ_query_bind]
    by_cases hpt : p t
    · simp only [hpt, ↓reduceIte] at hn
      have hn0 : 0 < n := by simpa using hn.1
      refine (prEvent_bind_le_prEvent_add_of_support ((so t).run s)
        (fun us => (simulateQ so (f us.1)).run us.2) (fun us => bad us.2) (fun z => bad z.2)
        (ε := (n - 1 : ℕ) * ε) fun us hmem hus =>
          ih us.1 (n - 1) (hn.2 us.1) us.2 (k + 1) hus (hszp t s k hk us hmem)
            (by omega)).trans ?_
      refine (add_le_add_left (hp t s k hs hpt hk (by omega)) _).trans (le_of_eq ?_)
      obtain ⟨k', rfl⟩ : ∃ k', n = k' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
    · simp only [hpt, ↓reduceIte] at hn
      exact prEvent_bind_le_of_forall_le_of_support _ _ _ fun us hus =>
        ih us.1 n (hn.2 us.1) us.2 k (hnp t s hs hpt us hus) (hsznp t s k hpt hk us hus) hcap

end StepBound

/-! ## Chains in a cache -/

section Chains

variable {κ κ' : Cell St Blk → Option St}

theorem walk_mono (h : CLe κ κ') {c : St} {bs : List Blk} {v : St}
    (hw : walk κ c bs = some v) : walk κ' c bs = some v := by
  induction bs generalizing c with
  | nil => exact hw
  | cons b bs ih =>
    simp only [walk, Option.bind_eq_some_iff] at hw ⊢
    obtain ⟨c', hc', hw⟩ := hw
    exact ⟨c', h _ _ hc', ih hw⟩

theorem chainVal_mono (h : CLe κ κ') {X : Blk × List Blk} {v : St}
    (hw : chainVal κ X = some v) : chainVal κ' X = some v := by
  simp only [chainVal, Option.bind_eq_some_iff] at hw ⊢
  obtain ⟨c, hc, hw⟩ := hw
  exact ⟨c, h _ _ hc, walk_mono h hw⟩

theorem walk_inj (hκ : CInj κ) {c c' : St} {bs bs' : List Blk} {v : St}
    (hlen : bs.length = bs'.length) (hw : walk κ c bs = some v)
    (hw' : walk κ c' bs' = some v) : c = c' ∧ bs = bs' := by
  induction bs generalizing c c' bs' with
  | nil =>
    cases bs' with
    | nil =>
      simp only [walk, Option.some.injEq] at hw hw'
      exact ⟨hw.trans hw'.symm, rfl⟩
    | cons b' bs' => simp at hlen
  | cons b bs ih =>
    cases bs' with
    | nil => simp at hlen
    | cons b' bs' =>
      simp only [walk, Option.bind_eq_some_iff] at hw hw'
      obtain ⟨c₁, hc₁, hw⟩ := hw
      obtain ⟨c₁', hc₁', hw'⟩ := hw'
      obtain ⟨rfl, rfl⟩ := ih (by simpa using hlen) hw hw'
      have := hκ _ _ _ hc₁ hc₁'
      simp only [Sum.inl.injEq, Prod.mk.injEq] at this
      exact ⟨this.1, by rw [this.2]⟩

theorem chainVal_inj (hκ : CInj κ) {X X' : Blk × List Blk} {v : St}
    (hlen : X.2.length = X'.2.length) (hw : chainVal κ X = some v)
    (hw' : chainVal κ X' = some v) : X = X' := by
  simp only [chainVal, Option.bind_eq_some_iff] at hw hw'
  obtain ⟨c, hc, hw⟩ := hw
  obtain ⟨c', hc', hw'⟩ := hw'
  obtain ⟨rfl, h2⟩ := walk_inj hκ hlen hw hw'
  have := hκ _ _ _ hc hc'
  simp only [Sum.inr.injEq] at this
  exact Prod.ext this h2

/-- The block list `X` ends at the cell `x`: its last cell is `x` and the cells before are
cached. -/
def EndsAt (κ : Cell St Blk → Option St) (x : Cell St Blk) (X : Blk × List Blk) : Prop :=
  (x = .inr X.1 ∧ X.2 = []) ∨
    ∃ pre b c₀, X.2 = pre ++ [b] ∧ chainVal κ (X.1, pre) = some c₀ ∧ x = .inl (c₀, b)

theorem EndsAt.unique (hκ : CInj κ) {x : Cell St Blk} {X X' : Blk × List Blk}
    (h : EndsAt κ x X) (h' : EndsAt κ x X') (hlen : X.2.length = X'.2.length) : X = X' := by
  rcases h with ⟨hx, hX⟩ | ⟨pre, b, c₀, hX, hv, hx⟩ <;>
    rcases h' with ⟨hx', hX'⟩ | ⟨pre', b', c₀', hX', hv', hx'⟩
  · rw [hx] at hx'
    simp only [Sum.inr.injEq] at hx'
    exact Prod.ext hx' (hX.trans hX'.symm)
  · rw [hx] at hx'; simp at hx'
  · rw [hx] at hx'; simp at hx'
  · rw [hx] at hx'
    simp only [Sum.inl.injEq, Prod.mk.injEq] at hx'
    obtain ⟨rfl, rfl⟩ := hx'
    have hl : pre.length = pre'.length := by
      rw [hX, hX'] at hlen
      simpa using hlen
    have := chainVal_inj hκ (X := (X.1, pre)) (X' := (X'.1, pre')) hl hv hv'
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1 (by rw [hX, hX', this.2])

variable [DecidableEq St] [DecidableEq Blk]

theorem CLe_update {x : Cell St Blk} (hx : κ x = none) (u : St) :
    CLe κ (Function.update κ x (some u)) := by
  intro y v hy
  have : y ≠ x := fun e => by rw [e, hx] at hy; exact absurd hy (by simp)
  rw [Function.update_of_ne this]
  exact hy

/-- A walk in a cache extended by a fresh cell `x` with a value `u` that is the row of no cached
public cell and not the row of `x` is a walk in the old cache or ends at `x`. -/
theorem walk_update {x : Cell St Blk} {u : St}
    (hrow : ∀ b, κ (.inl (u, b)) = none) (hxrow : ∀ b, x ≠ .inl (u, b))
    {c : St} {bs : List Blk} {w : St}
    (hw : walk (Function.update κ x (some u)) c bs = some w) :
    walk κ c bs = some w ∨
      ∃ pre b c₀, bs = pre ++ [b] ∧ walk κ c pre = some c₀ ∧ x = .inl (c₀, b) ∧ w = u := by
  induction bs generalizing c with
  | nil => exact .inl hw
  | cons b bs ih =>
    simp only [walk, Option.bind_eq_some_iff] at hw
    obtain ⟨c₁, hc₁, hw⟩ := hw
    by_cases hx : (Sum.inl (c, b) : Cell St Blk) = x
    · rw [← hx, Function.update_self, Option.some.injEq] at hc₁
      subst hc₁
      cases bs with
      | nil =>
        simp only [walk, Option.some.injEq] at hw
        exact .inr ⟨[], b, c, rfl, rfl, hx.symm, hw.symm⟩
      | cons b₂ bs =>
        simp only [walk, Option.bind_eq_some_iff] at hw
        obtain ⟨c₂, hc₂, -⟩ := hw
        rw [Function.update_of_ne (fun e => hxrow b₂ e.symm), hrow] at hc₂
        exact absurd hc₂ (by simp)
    · rw [Function.update_of_ne hx] at hc₁
      rcases ih hw with h | ⟨pre, b', c₀, rfl, hpre, hx', hwu⟩
      · refine .inl ?_
        simp only [walk, Option.bind_eq_some_iff]
        exact ⟨c₁, hc₁, h⟩
      · refine .inr ⟨b :: pre, b', c₀, rfl, ?_, hx', hwu⟩
        simp only [walk, Option.bind_eq_some_iff]
        exact ⟨c₁, hc₁, hpre⟩

theorem chainVal_update {x : Cell St Blk} {u : St}
    (hrow : ∀ b, κ (.inl (u, b)) = none) (hxrow : ∀ b, x ≠ .inl (u, b))
    {X : Blk × List Blk} {w : St}
    (hw : chainVal (Function.update κ x (some u)) X = some w) :
    chainVal κ X = some w ∨ (EndsAt κ x X ∧ w = u) := by
  simp only [chainVal, Option.bind_eq_some_iff] at hw
  obtain ⟨c, hc, hw⟩ := hw
  by_cases hx : (Sum.inr X.1 : Cell St Blk) = x
  · rw [← hx, Function.update_self, Option.some.injEq] at hc
    subst hc
    rcases hX : X.2 with _ | ⟨b₂, bs⟩
    · rw [hX] at hw
      simp only [walk, Option.some.injEq] at hw
      exact .inr ⟨.inl ⟨hx.symm, hX⟩, hw.symm⟩
    · rw [hX] at hw
      simp only [walk, Option.bind_eq_some_iff] at hw
      obtain ⟨c₂, hc₂, -⟩ := hw
      rw [Function.update_of_ne (fun e => hxrow b₂ e.symm), hrow] at hc₂
      exact absurd hc₂ (by simp)
  · rw [Function.update_of_ne hx] at hc
    rcases walk_update hrow hxrow hw with h | ⟨pre, b, c₀, hX, hpre, hx', hwu⟩
    · refine .inl ?_
      simp only [chainVal, Option.bind_eq_some_iff]
      exact ⟨c, hc, h⟩
    · refine .inr ⟨.inr ⟨pre, b, c₀, hX, ?_, hx'⟩, hwu⟩
      simp only [chainVal, Option.bind_eq_some_iff]
      exact ⟨c, hc, hpre⟩

theorem CFin.update {n : ℕ} (h : CFin κ n) (x : Cell St Blk) (u : St) :
    CFin (Function.update κ x (some u)) (n + 1) := by
  obtain ⟨l, hl, hmem⟩ := h
  refine ⟨x :: l, by simpa using hl, fun y hy => ?_⟩
  by_cases hyx : y = x
  · simp [hyx]
  · rw [Function.update_of_ne hyx] at hy
    exact List.mem_cons_of_mem _ (hmem y hy)

omit [DecidableEq St] [DecidableEq Blk] in
theorem CFin.mono {n m : ℕ} (h : CFin κ n) (hnm : n ≤ m) : CFin κ m := by
  obtain ⟨l, hl, hmem⟩ := h
  exact ⟨l, hl.trans hnm, hmem⟩

end Chains

/-! ## The good predicate of phase two -/

/-- The good predicate of phase two. -/
structure Good (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak) (L : ℕ)
    (qs : List (Tweak × M)) (cv : St) (κ : Cell St Blk → Option St) : Prop where
  inj : CInj κ
  nov : ∀ x, κ x ≠ some F.IV ∧ κ x ≠ some cv
  tgt : ∀ t m, (t, m) ∈ qs → ∃ v, chainVal κ (F.tch t m) = some v ∧
    ∀ (X : Blk × List Blk) (w : St), X.2.length = L → btw X.1 = t → X ≠ F.tch t m →
      chainVal κ X = some w → F.out w ≠ F.out v

section GoodLemmas

variable {F : THFam St Blk PkSeed Tweak M Y ι} {btw : Blk → Tweak} {L : ℕ}
  {qs : List (Tweak × M)} {cv : St} {κ : Cell St Blk → Option St}

theorem Good.of_mInv (h : MInv F btw L qs κ) (hcv : ∀ x, κ x ≠ some cv) :
    Good F btw L qs cv κ := by
  refine ⟨h.inj, fun x => ⟨h.noIV x, hcv x⟩, fun t m hm => ?_⟩
  obtain ⟨hsome, huniq⟩ := h.tgt t m hm
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hsome
  exact ⟨v, hv, fun X w hX hbt hne hw => absurd (huniq X hX hbt (by rw [hw]; rfl)) hne⟩

/-- The row of a cell. -/
def rowOf : Cell St Blk → Option St
  | .inl q => some q.1
  | .inr _ => none

/-- The fresh value `u` at the cell `x` has the output of a target whose tweak is carried by a
block list ending at `x`. -/
def Risk (F : THFam St Blk PkSeed Tweak M Y ι) (btw : Blk → Tweak) (L : ℕ)
    (qs : List (Tweak × M)) (κ : Cell St Blk → Option St) (x : Cell St Blk) (u : St) : Prop :=
  ∃ (X : Blk × List Blk) (m : M) (v : St), EndsAt κ x X ∧ X.2.length = L ∧
    (btw X.1, m) ∈ qs ∧ chainVal κ (F.tch (btw X.1) m) = some v ∧ F.out u = F.out v

variable [DecidableEq St] [DecidableEq Blk]

/-- Caching a fresh value keeps the good predicate unless the value is special. -/
theorem Good.update (hG : Good F btw L qs cv κ) {x : Cell St Blk} (hx : κ x = none) {u : St}
    (hIV : u ≠ F.IV) (hcv : u ≠ cv) (hval : ∀ y, κ y ≠ some u)
    (hrow : ∀ b, κ (.inl (u, b)) = none) (hxrow : ∀ b, x ≠ .inl (u, b))
    (hrisk : ¬ Risk F btw L qs κ x u) :
    Good F btw L qs cv (Function.update κ x (some u)) := by
  have hle := CLe_update hx u
  refine ⟨?_, ?_, ?_⟩
  · intro y y' v hy hy'
    by_cases h1 : y = x <;> by_cases h2 : y' = x
    · rw [h1, h2]
    · rw [h1, Function.update_self, Option.some.injEq] at hy
      rw [Function.update_of_ne h2, ← hy] at hy'
      exact absurd hy' (hval y')
    · rw [h2, Function.update_self, Option.some.injEq] at hy'
      rw [Function.update_of_ne h1, ← hy'] at hy
      exact absurd hy (hval y)
    · rw [Function.update_of_ne h1] at hy
      rw [Function.update_of_ne h2] at hy'
      exact hG.inj _ _ _ hy hy'
  · intro y
    by_cases h1 : y = x
    · rw [h1, Function.update_self]
      exact ⟨fun e => hIV (Option.some.inj e), fun e => hcv (Option.some.inj e)⟩
    · rw [Function.update_of_ne h1]
      exact hG.nov y
  · intro t m hm
    obtain ⟨v, hv, hrest⟩ := hG.tgt t m hm
    refine ⟨v, chainVal_mono hle hv, fun X w hX hbt hne hw => ?_⟩
    rcases chainVal_update hrow hxrow hw with h | ⟨hend, rfl⟩
    · exact hrest X w hX hbt hne h
    · intro hout
      exact hrisk ⟨X, m, v, hend, hX, by rw [hbt]; exact hm, by rw [hbt]; exact hv, hout⟩

end GoodLemmas

/-! ## Probabilities -/

section Prob

variable [Fintype St] [SampleableType St]

theorem prEvent_uniform_mem_le (l : List St) :
    Pr{let u ← ($ᵗ St : ProbComp St)}[u ∈ l] ≤ (l.length : ℝ≥0∞) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  induction l with
  | nil =>
    rw [prEvent_eq_zero_of_forall_not _ _ (by simp)]
    exact zero_le
  | cons a l ih =>
    refine (prEvent_mono _ _ (fun u => u = a ∨ u ∈ l) (by simp)).trans ?_
    refine (prEvent_or_le _ _ _).trans ?_
    rw [SampleableType.prEvent_uniformSample_eq_singleton]
    refine (add_le_add_right ih _).trans (le_of_eq ?_)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

variable {F : THFam St Blk PkSeed Tweak M Y ι} {btw : Blk → Tweak} {L : ℕ}
  {qs : List (Tweak × M)} {cv : St} {κ : Cell St Blk → Option St}
  [DecidableEq St] [DecidableEq Blk]

/-- Caching a fresh uniform value at a cell breaks the good predicate with probability at most
`δ + (2n + 3)/|St|`, `n` a bound on the number of cached cells. -/
theorem prEvent_not_good_update_le (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (htw : ∀ t m m', (t, m) ∈ qs → (t, m') ∈ qs → m = m')
    (hG : Good F btw L qs cv κ) {n : ℕ} (hfin : CFin κ n) {x : Cell St Blk} (hx : κ x = none) :
    Pr{let u ← ($ᵗ St : ProbComp St)}[¬ Good F btw L qs cv (Function.update κ x (some u))] ≤
      δ + (2 * n + 3 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  obtain ⟨l, hl, hmem⟩ := hfin
  let big : List St := F.IV :: cv :: (l.filterMap κ ++ l.filterMap rowOf ++ (rowOf x).toList)
  have hbig : big.length ≤ 2 * n + 3 := by
    have h1 := List.length_filterMap_le κ l
    have h2 := List.length_filterMap_le rowOf l
    have h3 : (rowOf x).toList.length ≤ 1 := by cases rowOf x <;> simp
    simp only [big, List.length_cons, List.length_append]
    omega
  refine (prEvent_mono _ _ (fun u => Risk F btw L qs κ x u ∨ u ∈ big) fun u hu => ?_).trans ?_
  · by_contra hne
    rw [not_or] at hne
    obtain ⟨hrisk, hnb⟩ := hne
    simp only [big, List.mem_cons, List.mem_append, List.mem_filterMap, Option.mem_toList,
      not_or, not_exists, not_and] at hnb
    obtain ⟨hIV, hcv, ⟨hval, hrow⟩, hxrow⟩ := hnb
    refine hu (hG.update hx hIV hcv (fun y hy => ?_) (fun b => ?_) (fun b hb => ?_) hrisk)
    · exact hval y (hmem y (by rw [hy]; rfl)) hy
    · by_contra hb
      exact hrow (.inl (u, b)) (hmem _ (Option.isSome_iff_ne_none.mpr hb)) rfl
    · exact hxrow (by rw [hb]; rfl)
  · refine (prEvent_or_le _ _ _).trans (add_le_add ?_ ?_)
    · by_cases hex : ∃ (X : Blk × List Blk) (m : M) (v : St), EndsAt κ x X ∧ X.2.length = L ∧
          (btw X.1, m) ∈ qs ∧ chainVal κ (F.tch (btw X.1) m) = some v
      · obtain ⟨X₀, m₀, v₀, hend₀, hlen₀, hm₀, hv₀⟩ := hex
        refine (prEvent_mono _ _ (fun u => F.out u = F.out v₀) fun u hu => ?_).trans (hδ _)
        obtain ⟨X, m, v, hend, hlen, hm, hv, hout⟩ := hu
        obtain rfl := EndsAt.unique hG.inj hend hend₀ (hlen.trans hlen₀.symm)
        obtain rfl := htw _ _ _ hm hm₀
        rw [hv₀] at hv
        rw [hout, Option.some.inj hv]
      · rw [prEvent_eq_zero_of_forall_not _ _ fun u hu => hex ?_]
        · exact zero_le
        · obtain ⟨X, m, v, hend, hlen, hm, hv, -⟩ := hu
          exact ⟨X, m, v, hend, hlen, hm, hv⟩
    · refine (prEvent_uniform_mem_le big).trans ?_
      gcongr

end Prob

/-! ## Phase-two steps -/

section Route

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-- The answer `v` of the routed query `q` is recorded in the cache `κ`. -/
def Ans (IV : St) (sbs : Blk) (cv : St) (κ : Cell St Blk → Option St) (q : St × Blk)
    (v : St) : Prop :=
  (q = (IV, sbs) ∧ v = cv) ∨ (q ≠ (IV, sbs) ∧ q.1 = cv ∧ κ (.inr q.2) = some v) ∨
    (q ≠ (IV, sbs) ∧ q.1 ≠ cv ∧ κ (.inl q) = some v)

/-- A routed compression query is answered from the cache, or samples one fresh cell. -/
theorem routeRO_run_shape (IV : St) (sbs : Blk) (cv : St) (q : St × Blk) (s : Cache St Blk) :
    (∃ v, (routeRO IV sbs cv (.inr q)).run s = pure (v, s) ∧ Ans IV sbs cv (look s) q v) ∨
    (∃ x, look s x = none ∧ (routeRO IV sbs cv (.inr q)).run s =
        (fun u => (u, ofLook (Function.update (look s) x (some u)))) <$> ($ᵗ St : ProbComp St) ∧
      ∀ u, Ans IV sbs cv (Function.update (look s) x (some u)) q u) := by
  by_cases h1 : q = (IV, sbs)
  · subst h1
    exact .inl ⟨cv, routeRO_run_seed IV sbs cv s, .inl ⟨rfl, rfl⟩⟩
  · by_cases h2 : q.1 = cv
    · obtain ⟨c', B⟩ := q
      subst h2
      rw [routeRO_run_row _ _ _ _ _ h1]
      rcases randomOracle_run_row_cases B s with ⟨v, hv, h⟩ | ⟨hnone, h⟩
      · exact .inl ⟨v, h, .inr (.inl ⟨h1, rfl, hv⟩)⟩
      · refine .inr ⟨.inr B, hnone, ?_, fun u => .inr (.inl ⟨h1, rfl, Function.update_self ..⟩)⟩
        simp only [ofLook_update_inr, ofLook_look]
        exact h
    · rw [routeRO_run_pub _ _ _ _ _ h1 h2]
      rcases randomOracle_run_pub_cases q s with ⟨v, hv, h⟩ | ⟨hnone, h⟩
      · exact .inl ⟨v, h, .inr (.inr ⟨h1, h2, hv⟩)⟩
      · refine .inr ⟨.inl q, hnone, ?_, fun u => .inr (.inr ⟨h1, h2, Function.update_self ..⟩)⟩
        simp only [ofLook_update_inl, ofLook_look]
        exact h

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem CLe.refl (κ : Cell St Blk → Option St) : CLe κ κ := fun _ _ h => h

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] in
theorem CLe.trans {κ₁ κ₂ κ₃ : Cell St Blk → Option St} (h : CLe κ₁ κ₂) (h' : CLe κ₂ κ₃) :
    CLe κ₁ κ₃ := fun x v hx => h' x v (h x v hx)

theorem routeRO_support {IV : St} {sbs : Blk} {cv : St} {q : St × Blk} {s : Cache St Blk}
    {z : St × Cache St Blk} (hz : z ∈ support ((routeRO IV sbs cv (.inr q)).run s)) :
    CLe (look s) (look z.2) ∧ Ans IV sbs cv (look z.2) q z.1 ∧
      ∀ k, CFin (look s) k → CFin (look z.2) (k + 1) := by
  rcases routeRO_run_shape IV sbs cv q s with ⟨v, h, ha⟩ | ⟨x, hx, h, ha⟩
  · rw [h, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨CLe.refl _, ha, fun k hk => CFin.mono hk (Nat.le_succ k)⟩
  · rw [h, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    simp only [look_ofLook]
    exact ⟨CLe_update hx u, ha u, fun k hk => CFin.update hk x u⟩

theorem routeRO_inl_support {IV : St} {sbs : Blk} {cv : St} {n : ℕ} {s : Cache St Blk}
    {z : Fin (n + 1) × Cache St Blk} (hz : z ∈ support ((routeRO IV sbs cv (.inl n)).run s)) :
    z.2 = s := by
  rw [routeRO_run_inl, support_map] at hz
  obtain ⟨u, -, rfl⟩ := hz
  rfl

variable [Fintype St] {F : THFam St Blk PkSeed Tweak M Y ι} {btw : Blk → Tweak} {L : ℕ}
  {qs : List (Tweak × M)} {cv : St}

/-- A routed compression query breaks the good predicate with probability at most
`δ + (2n + 3)/|St|`. -/
theorem prEvent_routeRO_not_good_le (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (htw : ∀ t m m', (t, m) ∈ qs → (t, m') ∈ qs → m = m') (sbs : Blk)
    (s : Cache St Blk) (hG : Good F btw L qs cv (look s)) {n : ℕ} (hfin : CFin (look s) n)
    (q : St × Blk) :
    Pr{let z ← (routeRO F.IV sbs cv (.inr q)).run s}[¬ Good F btw L qs cv (look z.2)] ≤
      δ + (2 * n + 3 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  rcases routeRO_run_shape F.IV sbs cv q s with ⟨v, h, -⟩ | ⟨x, hx, h, -⟩
  · rw [h, prEvent_pure]
    simp only [hG, not_true_eq_false, ↓reduceIte]
    exact zero_le
  · rw [h, prEvent_map]
    refine (prEvent_mono _ _ _ fun u hu => ?_).trans
      (prEvent_not_good_update_le δ hδ htw hG hfin hx)
    simpa only [Function.comp_apply, look_ofLook] using hu

/-- A phase-two computation making at most `n` compression queries, run from a good cache with
at most `N` cells, ends in a cache that is not good with probability at most
`n * (δ + (2 (N + n) + 3)/|St|)`. -/
theorem prEvent_run_not_good_le (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (htw : ∀ t m m', (t, m) ∈ qs → (t, m') ∈ qs → m = m') (sbs : Blk) {α : Type}
    (oa : OracleComp (unifSpec + hS St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (s : Cache St Blk) (N : ℕ)
    (hG : Good F btw L qs cv (look s)) (hfin : CFin (look s) N) :
    Pr{let z ← (simulateQ (routeRO F.IV sbs cv) oa).run s}[¬ Good F btw L qs cv (look z.2)] ≤
      n * (δ + (2 * (N + n) + 3 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  classical
  refine prEvent_bad_le_of_step_cap _ (fun s => ¬ Good F btw L qs cv (look s))
    (fun s k => CFin (look s) k) _ _ (N + n) ?_ ?_ ?_ ?_ oa n hn s N (not_not.mpr hG) hfin le_rfl
  · rintro (m | q) s k hs ht hk hkN
    · simp at ht
    · refine (prEvent_routeRO_not_good_le δ hδ htw sbs s (not_not.mp hs) hk q).trans ?_
      gcongr
  · rintro (m | q) s k hk z hz
    · rw [routeRO_inl_support hz]
      exact CFin.mono hk (Nat.le_succ k)
    · exact (routeRO_support hz).2.2 k hk
  · rintro (m | q) s hs ht z hz
    · rw [routeRO_inl_support hz]
      exact hs
    · simp at ht
  · rintro (m | q) s k ht hk z hz
    · rw [routeRO_inl_support hz]
      exact hk
    · simp at ht

/-! ## The final check -/

omit [Fintype St] in
/-- A routed fold of compression queries leaves its chain in the cache. -/
theorem fold_settle (IV : St) (sbs : Blk) (cv : St) (bs : List Blk) (a : St) (s : Cache St Blk)
    {z : St × Cache St Blk}
    (hz : z ∈ support ((simulateQ (routeRO IV sbs cv)
      (bs.foldlM (fun c b => (unifSpec + hS St Blk).query (.inr (c, b))) a)).run s)) :
    CLe (look s) (look z.2) ∧ ∀ κ', CLe (look z.2) κ' →
      (∀ x, κ' x ≠ some IV ∧ κ' x ≠ some cv) → a ≠ IV → a ≠ cv → walk κ' a bs = some z.1 := by
  induction bs generalizing a s with
  | nil =>
    simp only [List.foldlM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    subst hz
    exact ⟨CLe.refl _, fun _ _ _ _ _ => rfl⟩
  | cons b bs ih =>
    simp only [List.foldlM_cons, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨y, hy, hz⟩ := hz
    have hy' : y ∈ support ((routeRO IV sbs cv (.inr (a, b))).run s) := by simpa using hy
    obtain ⟨hle1, hans, -⟩ := routeRO_support hy'
    obtain ⟨hle2, hrest⟩ := ih _ _ hz
    refine ⟨CLe.trans hle1 hle2, fun κ' hκ' hnov haIV hacv => ?_⟩
    rcases hans with ⟨he, -⟩ | ⟨-, he, -⟩ | ⟨-, -, hv⟩
    · exact absurd (Prod.mk.inj he).1 haIV
    · exact absurd he hacv
    · have hv' := hκ' _ _ (hle2 _ _ hv)
      simp only [walk, Option.bind_eq_some_iff]
      exact ⟨y.1, hv', hrest κ' hκ' hnov (fun e => (hnov _).1 (e ▸ hv'))
        (fun e => (hnov _).2 (e ▸ hv'))⟩

omit [Fintype St] in
/-- A routed evaluation of the attacked member leaves its chain in the cache. -/
theorem evalPub_settle (seed : PkSeed) (hcv : cv ≠ F.IV) (t : Tweak) (m : M)
    (s : Cache St Blk) {z : Y × Cache St Blk}
    (hz : z ∈ support ((simulateQ (routeRO F.IV (F.sb seed) cv) (evalPub F seed t m)).run s)) :
    CLe (look s) (look z.2) ∧ ∀ κ', CLe (look z.2) κ' →
      (∀ x, κ' x ≠ some F.IV ∧ κ' x ≠ some cv) →
      ∃ w, chainVal κ' (F.tch t m) = some w ∧ z.1 = F.out w := by
  simp only [evalPub, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, routeRO_run_seed,
    pure_bind, simulateQ_pure, StateT.run_pure, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hz
  obtain ⟨y, hy, y', hy', rfl⟩ := hz
  obtain ⟨hle1, hans, -⟩ := routeRO_support hy
  obtain ⟨hle2, hrest⟩ := fold_settle _ _ _ _ _ _ hy'
  refine ⟨CLe.trans hle1 hle2, fun κ' hκ' hnov => ?_⟩
  rcases hans with ⟨he, -⟩ | ⟨-, -, hv⟩ | ⟨-, he, -⟩
  · exact absurd (Prod.mk.inj he).1 hcv
  · have hv' := hκ' _ _ (hle2 _ _ hv)
    refine ⟨y'.1, ?_, rfl⟩
    simp only [chainVal, Option.bind_eq_some_iff]
    exact ⟨y.1, hv', hrest κ' hκ' hnov (fun e => (hnov _).1 (e ▸ hv'))
      (fun e => (hnov _).2 (e ▸ hv'))⟩
  · exact absurd rfl he

omit [Fintype St] in
/-- If phase two returns `true`, the final cache is not good. -/
theorem not_good_of_win [DecidableEq M] [DecidableEq Y]
    (hlen : ∀ t m, (F.tch t m).2.length = L) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', F.tch t m = F.tch t m' → m = m') (seed : PkSeed) (hcv : cv ≠ F.IV)
    (A : TcrAdv F) (x : A.State × SM_DT_TCR_State Tweak M) (s : Cache St Blk)
    {z : Bool × Cache St Blk}
    (hz : z ∈ support ((simulateQ (routeRO F.IV (F.sb seed) cv) (tcrP₂ A seed x)).run s))
    (hw : z.1 = true) : ¬ Good F btw L x.2.1 cv (look z.2) := by
  unfold tcrP₂ at hz
  rw [simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at hz
  obtain ⟨⟨⟨j, m⟩, c₂⟩, -, hz⟩ := hz
  dsimp only at hz
  cases hj : x.2.1[j]? with
  | none =>
    rw [hj] at hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    subst hz
    simp at hw
  | some tm =>
    obtain ⟨t, mj⟩ := tm
    rw [hj] at hz
    simp only [simulateQ_bind, StateT.run_bind, simulateQ_pure, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨y, hy, y', hy', rfl⟩ := hz
    intro hG
    obtain ⟨-, h1⟩ := evalPub_settle seed hcv t m c₂ hy
    obtain ⟨hle, h2⟩ := evalPub_settle seed hcv t mj y.2 hy'
    obtain ⟨w, hw1, hy1⟩ := h1 _ hle hG.nov
    obtain ⟨w', hw2, hy2⟩ := h2 _ (CLe.refl _) hG.nov
    obtain ⟨hne, heq⟩ := of_decide_eq_true hw
    obtain ⟨v, hv, hrest⟩ := hG.tgt t mj (List.mem_of_getElem? hj)
    rw [hw2] at hv
    obtain rfl := Option.some.inj hv
    refine hrest (F.tch t m) w (hlen t m) (hbtwT t m) (fun e => hne (hinj t m mj e)) hw1 ?_
    rw [← hy1, ← hy2]
    exact heq

/-! ## Query counts -/

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] in
theorem isQueryBoundP_foldlM (bs : List Blk) (c : St) :
    IsQueryBoundP
      (bs.foldlM (m := OracleComp (unifSpec + hS St Blk))
        (fun c b => liftM ((unifSpec + hS St Blk).query (.inr (c, b)))) c)
      (fun i => Sum.isRight i = true) bs.length := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldlM_cons, isQueryBoundP_query_bind_iff]
    refine ⟨Or.inr (by simp), fun u => ?_⟩
    simpa using ih u

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] in
theorem isQueryBoundP_evalPub (seed : PkSeed) (t : Tweak) (m : M) :
    IsQueryBoundP (evalPub F seed t m) (fun i => Sum.isRight i = true)
      ((F.tch t m).2.length + 2) := by
  unfold evalPub
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by omega), fun u => ?_⟩
  simp only [Sum.isRight_inr, ite_true]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inr (by omega), fun u' => ?_⟩
  simp only [Sum.isRight_inr, ite_true]
  exact (isQueryBoundP_bind (isQueryBoundP_foldlM _ _)
    (fun _ _ => isQueryBoundP_pure _ _ 0)).mono (by omega)

omit [DecidableEq St] [DecidableEq Blk] [SampleableType St] [Fintype St] in
theorem isQueryBoundP_tcrP₂ [DecidableEq M] [DecidableEq Y]
    (hlen : ∀ t m, (F.tch t m).2.length = L) (A : TcrAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂)
    (seed : PkSeed) (x : A.State × SM_DT_TCR_State Tweak M) :
    IsQueryBoundP (tcrP₂ A seed x) (fun i => Sum.isRight i = true) (q₂ + 2 * L + 4) := by
  unfold tcrP₂
  refine (isQueryBoundP_bind (p := fun i => Sum.isRight i = true)
    (m := (L + 2) + ((L + 2) + 0)) (hq₂ x.1 seed)
    fun jm _ => ?_).mono (by omega)
  obtain ⟨j, m⟩ := jm
  dsimp only
  cases x.2.1[j]? with
  | none => exact isQueryBoundP_pure _ _ _
  | some tm =>
    obtain ⟨t, mj⟩ := tm
    dsimp only
    refine isQueryBoundP_bind ((isQueryBoundP_evalPub seed t m).mono (by rw [hlen])) fun _ _ => ?_
    exact isQueryBoundP_bind ((isQueryBoundP_evalPub seed t mj).mono (by rw [hlen]))
      fun _ _ => isQueryBoundP_pure _ _ 0

end Route

end MP2

/-- **Phase two of the multi-block SM-TCR game.**  From a cache with at most `N` cells satisfying
the phase-one invariant `MInv`, the draw of `cv` followed by phase two returns `true` with
probability at most `(q₂ + 2L + 4)·δ + ((q₂ + 2L + 4)(2(N + q₂ + 2L + 4) + 3) + N + 1)/|St|`. -/
theorem tcr_multi_phase2_le [Fintype St] [DecidableEq St] [DecidableEq Blk] [SampleableType St]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {F : THFam St Blk PkSeed Tweak M Y ι}
    (L : ℕ) (hlen : ∀ t m, (F.tch t m).2.length = L)
    (btw : Blk → Tweak) (hbtwT : ∀ t m, btw (F.tch t m).1 = t)
    (hinj : ∀ t m m', F.tch t m = F.tch t m' → m = m')
    (δ : ℝ≥0∞) (hδ : ∀ y, Pr{let u ← $ᵗ St}[F.out u = y] ≤ δ)
    (A : TcrAdv F) (q₂ : ℕ) (hq₂ : A.ForgeBound q₂)
    (x : A.State × SM_DT_TCR_State Tweak M) (c : Cache St Blk) (seed : PkSeed) (N : ℕ)
    (hInv : MInv F btw L x.2.1 (look c)) (hfin : CFin (look c) N) :
    Pr{let cv ← ($ᵗ St : ProbComp St);
       let b ← (simulateQ (routeRO F.IV (F.sb seed) cv) (tcrP₂ A seed x)).run' c}[b = true] ≤
      (q₂ + 2 * L + 4 : ℕ) * δ +
        ((q₂ + 2 * L + 4) * (2 * (N + q₂ + 2 * L + 4) + 3) + N + 1 : ℕ) *
          (Fintype.card St : ℝ≥0∞)⁻¹ := by
  classical
  obtain ⟨l, hl, hmem⟩ := hfin
  rw [← map_bind]
  refine (prEvent_bind_le_prEvent_add ($ᵗ St : ProbComp St) _
    (fun cv => cv ∈ F.IV :: l.filterMap (look c)) _
    (ε := (q₂ + 2 * L + 4 : ℕ) * (δ + (2 * (N + (q₂ + 2 * L + 4)) + 3 : ℕ) *
      (Fintype.card St : ℝ≥0∞)⁻¹)) fun cv hcv => ?_).trans ?_
  · simp only [List.mem_cons, List.mem_filterMap, not_or, not_exists, not_and] at hcv
    obtain ⟨hcvIV, hcvval⟩ := hcv
    have hG : MP2.Good F btw L x.2.1 cv (look c) :=
      MP2.Good.of_mInv hInv fun y hy => hcvval y (hmem y (by rw [hy]; rfl)) hy
    rw [StateT.run'_eq, prEvent_map]
    exact (prEvent_mono_of_support _ _ (fun z => ¬ MP2.Good F btw L x.2.1 cv (look z.2))
      fun z hz hw => MP2.not_good_of_win hlen hbtwT hinj seed hcvIV A x c hz hw).trans
      (MP2.prEvent_run_not_good_le δ hδ hInv.twfun (F.sb seed) _ _
        (MP2.isQueryBoundP_tcrP₂ hlen A q₂ hq₂ seed x) c N hG ⟨l, hl, hmem⟩)
  · have hlen' : (F.IV :: l.filterMap (look c)).length ≤ N + 1 := by
      have := List.length_filterMap_le (look c) l
      simp only [List.length_cons]
      omega
    have h1 : Pr{let cv ← ($ᵗ St : ProbComp St)}[cv ∈ F.IV :: l.filterMap (look c)] ≤
        (N + 1 : ℕ) * (Fintype.card St : ℝ≥0∞)⁻¹ := by
      refine (MP2.prEvent_uniform_mem_le _).trans ?_
      gcongr
    refine (add_le_add_left h1 _).trans (le_of_eq ?_)
    push_cast
    ring

end Ideal

#print axioms Ideal.tcr_multi_phase2_le
