import Ideal.Direct.Parse
import Ideal.Games.Itsr

/-!
# Rooted chains in a cache (D2 of `status/DIRECT.md`, cache-dependent part)

A cache `κ : St × Blk → Option St` (the lazy table's state) and an initial value `c₀` (`IV`).

* `mdC κ c bs`: the Merkle–Damgård iteration from `c` over `bs` through the cache (`none` as
  soon as a cell is missing); `mdC_append`, `mdC_mono` (extension of caches), `mdC_of_ext`
  (through a total table extending the cache it is `mdFold`).
* `NoCollC c₀ κ`: distinct cached cells have distinct values and no value is `c₀` (Inv 1 of the
  plan, without the temporal back-link part).
* **`rooted_unique`**: under `NoCollC`, a value is reached from `c₀` by at most one block list:
  `mdC κ c₀ bs = some c → mdC κ c₀ bs' = some c → bs = bs'`.
* `rootOf c₀ κ c`: that block list (if any); `rootOf_spec`, `rootOf_eq`.
* The two cache-dependent parse classes of the plan (§2.3), for SLH-DSA-SHA2-128s:
  `IsThL pk κ q A xs` (the cell `q` is the **last** cell of the multi-block `Thash` evaluation of
  `(A, xs)` from the public midstate: its chaining value is rooted as `sb128 pk` followed by all
  but the last block of `tblocks A xs`, and its block is the last one) and `IsHmF κ q R pk s`
  (the cell is the outer final cell of an `H_msg` evaluation: its chaining value is rooted as the
  first outer block `R ‖ pk ‖ s` and its block the second).  **Uniqueness**: `isThL_unique`
  (under `NoCollC IV128`, a cell is the last cell of at most one `(A, xs)`), `isHmF_unique`.
-/

open OracleComp OracleSpec ENNReal SLHDSA SLHDSA.Concrete

namespace Ideal.Direct

set_option linter.unusedSectionVars false

/-! ## Iteration through a cache -/

section MD

variable {S B : Type} [DecidableEq S] [DecidableEq B]

/-- The Merkle–Damgård iteration through a partial table. -/
def mdC (κ : S × B → Option S) : S → List B → Option S
  | c, [] => some c
  | c, b :: bs => (κ (c, b)).bind fun c' => mdC κ c' bs

theorem mdC_append (κ : S × B → Option S) (c : S) (bs : List B) (b : B) :
    mdC κ c (bs ++ [b]) = (mdC κ c bs).bind fun c' => κ (c', b) := by
  induction bs generalizing c with
  | nil => simp [mdC]
  | cons a bs ih =>
    simp only [List.cons_append, mdC]
    cases κ (c, a) with
    | none => rfl
    | some c' => exact ih c'

/-- Extension of caches. -/
def CExt (κ κ' : S × B → Option S) : Prop := ∀ q v, κ q = some v → κ' q = some v

theorem mdC_mono {κ κ' : S × B → Option S} (h : CExt κ κ') :
    ∀ (c : S) (bs : List B) (v : S), mdC κ c bs = some v → mdC κ' c bs = some v := by
  intro c bs
  induction bs generalizing c with
  | nil => intro v hv; exact hv
  | cons b bs ih =>
    intro v hv
    simp only [mdC, Option.bind_eq_some_iff] at hv ⊢
    obtain ⟨c', hc', hv'⟩ := hv
    exact ⟨c', h _ _ hc', ih c' v hv'⟩

/-- Through a total table extending the cache, the iteration is `mdFold`. -/
theorem mdC_of_ext {κ : S × B → Option S} (g : S × B → S) (hg : ∀ q v, κ q = some v → g q = v) :
    ∀ (c : S) (bs : List B) (v : S), mdC κ c bs = some v → mdFold g c bs = v := by
  intro c bs
  induction bs generalizing c with
  | nil => intro v hv; simp only [mdC, Option.some.injEq] at hv; simp [mdFold, hv]
  | cons b bs ih =>
    intro v hv
    simp only [mdC, Option.bind_eq_some_iff] at hv
    obtain ⟨c', hc', hv'⟩ := hv
    have := ih c' v hv'
    simp only [mdFold, List.foldl_cons] at this ⊢
    rw [hg _ _ hc']
    exact this

/-- No 256-bit coincidence in a cache: distinct cells have distinct values, and no value is
`c₀`. -/
def NoCollC (c₀ : S) (κ : S × B → Option S) : Prop :=
  (∀ q q' v, κ q = some v → κ q' = some v → q = q') ∧ ∀ q, κ q ≠ some c₀

/-- **A value is reached from `c₀` by at most one block list.** -/
theorem rooted_unique {c₀ : S} {κ : S × B → Option S} (h : NoCollC c₀ κ) :
    ∀ (bs bs' : List B) (c : S), mdC κ c₀ bs = some c → mdC κ c₀ bs' = some c → bs = bs' := by
  intro bs
  induction bs using List.reverseRecOn with
  | nil =>
    intro bs' c h1 h2
    simp only [mdC, Option.some.injEq] at h1
    subst h1
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, rfl⟩
    · rfl
    · rw [List.concat_eq_append, mdC_append, Option.bind_eq_some_iff] at h2
      obtain ⟨c', -, hc'⟩ := h2
      exact absurd hc' (h.2 _)
  | append_singleton as a ih =>
    intro bs' c h1 h2
    rw [mdC_append, Option.bind_eq_some_iff] at h1
    obtain ⟨c1, hc1, hv1⟩ := h1
    rcases List.eq_nil_or_concat bs' with rfl | ⟨L, b, rfl⟩
    · simp only [mdC, Option.some.injEq] at h2
      subst h2
      exact absurd hv1 (h.2 _)
    · rw [List.concat_eq_append, mdC_append, Option.bind_eq_some_iff] at h2
      obtain ⟨c2, hc2, hv2⟩ := h2
      have hq := h.1 _ _ _ hv1 hv2
      obtain ⟨e1, e2⟩ := Prod.mk.inj hq
      subst e1; subst e2
      rw [ih L c1 hc1 hc2, List.concat_eq_append]

theorem NoCollC.mono {c₀ : S} {κ κ' : S × B → Option S} (h : NoCollC c₀ κ') (hext : CExt κ κ') :
    NoCollC c₀ κ :=
  ⟨fun q q' v h1 h2 => h.1 q q' v (hext _ _ h1) (hext _ _ h2),
    fun q hq => h.2 q (hext _ _ hq)⟩

open Classical in
/-- The block list by which a value is rooted at `c₀` in the cache, if any. -/
noncomputable def rootOf (c₀ : S) (κ : S × B → Option S) (c : S) : Option (List B) :=
  if h : ∃ bs, mdC κ c₀ bs = some c then some (Classical.choose h) else none

theorem rootOf_spec {c₀ : S} {κ : S × B → Option S} {c : S} {bs : List B}
    (h : rootOf c₀ κ c = some bs) : mdC κ c₀ bs = some c := by
  unfold rootOf at h
  split_ifs at h with hex
  · cases h; exact Classical.choose_spec hex

theorem rootOf_eq {c₀ : S} {κ : S × B → Option S} (hn : NoCollC c₀ κ) {c : S} {bs : List B}
    (h : mdC κ c₀ bs = some c) : rootOf c₀ κ c = some bs := by
  have hex : ∃ bs, mdC κ c₀ bs = some c := ⟨bs, h⟩
  unfold rootOf
  rw [dif_pos hex]
  exact congrArg some (rooted_unique hn _ _ c (Classical.choose_spec hex) h)

end MD

/-! ## The two rooted classes at SLH-DSA-SHA2-128s -/

section Classes

/-- The cell `q` is the **last** cell of the evaluation of `Thash(pk, A, xs)` (any length) from
`IV`: its chaining value is rooted as `sb128 pk` followed by all blocks of `tblocks A xs` but the
last, and its block is the last block. -/
def IsThL (pk : Bytes 16) (κ : St × Blk → Option St) (q : St × Blk) (A : Bytes 22)
    (xs : List (Bytes 16)) : Prop :=
  ∃ pre : List Blk, (tblocks A xs).1 :: (tblocks A xs).2 = pre ++ [q.2] ∧
    mdC κ IV128 (sb128 pk :: pre) = some q.1

/-- **A cell is the last cell of at most one `Thash` evaluation.** -/
theorem isThL_unique {pk : Bytes 16} {κ : St × Blk → Option St} (hn : NoCollC IV128 κ)
    {q : St × Blk} {A A' : Bytes 22} {xs xs' : List (Bytes 16)} (h : IsThL pk κ q A xs)
    (h' : IsThL pk κ q A' xs') : A = A' ∧ xs = xs' := by
  obtain ⟨pre, hb, hc⟩ := h
  obtain ⟨pre', hb', hc'⟩ := h'
  have e := rooted_unique hn _ _ _ hc hc'
  have e2 : pre = pre' := (List.cons.inj e).2
  subst e2
  have hall : (tblocks A xs).1 :: (tblocks A xs).2 = (tblocks A' xs').1 :: (tblocks A' xs').2 := by
    rw [hb, hb']
  exact tblocks_injective (Prod.ext (List.cons.inj hall).1 (List.cons.inj hall).2)

/-- Through a total table extending the cache, the value of a last cell is the `Thash` chaining
value (`mdFold` over the seed block and all blocks). -/
theorem isThL_value {pk : Bytes 16} {κ : St × Blk → Option St} (g : CF St Blk)
    (hg : ∀ q v, κ q = some v → g q = v) {q : St × Blk} {A : Bytes 22} {xs : List (Bytes 16)}
    (h : IsThL pk κ q A xs) :
    g q = mdFold g IV128 (sb128 pk :: (tblocks A xs).1 :: (tblocks A xs).2) := by
  obtain ⟨pre, hb, hc⟩ := h
  have := mdC_of_ext g hg _ _ _ hc
  rw [hb]
  have e : sb128 pk :: (pre ++ [q.2]) = (sb128 pk :: pre) ++ [q.2] := rfl
  rw [e, Ideal.Itsr.mdFold_append, this]

/-- The cell `q` is the outer final cell of an `H_msg` evaluation with randomizer `R`, seed `pk`
and inner digest `s`: its chaining value is rooted as the first outer block, its block is the
second. -/
def IsHmF (κ : St × Blk → Option St) (q : St × Blk) (R pk : Bytes 16) (s : St) : Prop :=
  ∃ b₁ b₂, oblocksH R pk s = [b₁, b₂] ∧ q.2 = b₂ ∧ mdC κ IV128 [b₁] = some q.1

/-- **A cell is the outer final cell of at most one `(R, pk, s)`.** -/
theorem isHmF_unique {κ : St × Blk → Option St} (hn : NoCollC IV128 κ) {q : St × Blk}
    {R pk R' pk' : Bytes 16} {s s' : St} (h : IsHmF κ q R pk s) (h' : IsHmF κ q R' pk' s') :
    R = R' ∧ pk = pk' ∧ s = s' := by
  obtain ⟨b₁, b₂, hb, hq, hc⟩ := h
  obtain ⟨b₁', b₂', hb', hq', hc'⟩ := h'
  have e := rooted_unique hn _ _ _ hc hc'
  have e1 : b₁ = b₁' := (List.cons.inj e).1
  have e2 : b₂ = b₂' := hq.symm.trans hq'
  subst e1; subst e2
  exact oblocksH_injective (hb.trans hb'.symm)

end Classes

end Ideal.Direct

#print axioms Ideal.Direct.rooted_unique
#print axioms Ideal.Direct.rootOf_eq
#print axioms Ideal.Direct.isThL_unique
#print axioms Ideal.Direct.isThL_value
#print axioms Ideal.Direct.isHmF_unique
