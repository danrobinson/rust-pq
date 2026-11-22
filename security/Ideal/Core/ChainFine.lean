import Ideal.Core.HiddenInput

/-!
# Phase two with chain queries: chains not starting with the seed block never reach the row

A second-phase program may be given with **chain queries** `bs` (the Merkle–Damgård iteration
of the compression function from `IV` over the blocks `bs`) besides raw compression queries
(`pcS`); `expandImpl IV` issues a chain query as its raw compression queries.  In the ideal
(hidden-prefix) game, phase two answers the seed cell `(IV, sb seed)` by `cv` and every cell in
row `cv` from the private row table (`routeRO`).

A chain query whose first block is NOT the seed block (`freeC`) reads only public cells, unless
some public cell read has the value `IV` or `cv` (`PubBad`): its first cell is `(IV, b₀)` with
`b₀ ≠ sb seed` (public since `cv ≠ IV`), and every later cell has as chaining value the value of
the previous (public) cell.  Hence:

* `free_fold`, `routeRO_potential_fine`: a potential that only private-row cells can raise is
  raised by at most `n·ε` along the run of a program with `n` raw queries and only free chain
  queries, or the final cache is `PubBad` (pathwise);
* `prEvent_routeRO_pubBad_le`: from a cache that is not `PubBad`, a phase-two run with `n`
  compression queries ends `PubBad` with probability at most `2n/|St|`;
* `pubHit_routeRO`: a public value once cached stays cached.

Nothing here restricts the adversary: the chain queries a program makes are what they are; the
count `n` is of raw queries only, the free chain queries are counted in `PubBad`'s probability
through the total number of compression queries.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

variable {St Blk : Type}

/-! ## Chain queries and their expansion -/

/-- Chain queries from `IV`: `bs ↦ mdFold g IV bs`. -/
abbrev chQ (St Blk : Type) : OracleSpec (List Blk) := List Blk →ₒ St

/-- Second-phase interface with chain queries: uniform bits, raw compression queries, chain
queries. -/
abbrev pcS (St Blk : Type) := unifSpec + (hS St Blk + chQ St Blk)

/-- One raw compression query. -/
def rawQ (q : St × Blk) : OracleComp (unifSpec + hS St Blk) St :=
  (liftM ((unifSpec + hS St Blk).query (.inr q)) : OracleComp (unifSpec + hS St Blk) St)

/-- The Merkle–Damgård iteration from `c` as raw compression queries. -/
def foldR (c : St) (bs : List Blk) : OracleComp (unifSpec + hS St Blk) St :=
  bs.foldlM (fun c b => rawQ (c, b)) c

/-- Chain queries issued as their raw compression queries. -/
def expandImpl (IV : St) : QueryImpl (pcS St Blk) (OracleComp (unifSpec + hS St Blk))
  | .inl n => (liftM ((unifSpec + hS St Blk).query (.inl n)) :
      OracleComp (unifSpec + hS St Blk) _)
  | .inr (.inl q) => rawQ q
  | .inr (.inr bs) => foldR IV bs

/-- A raw compression query. -/
def isRawC : ℕ ⊕ ((St × Blk) ⊕ List Blk) → Bool
  | .inr (.inl _) => true
  | _ => false

/-- A chain query. -/
def isChainC : ℕ ⊕ ((St × Blk) ⊕ List Blk) → Bool
  | .inr (.inr _) => true
  | _ => false

/-- Every chain query has at most `Lc` blocks. -/
def chainLenC (Lc : ℕ) : ℕ ⊕ ((St × Blk) ⊕ List Blk) → Prop
  | .inr (.inr bs) => bs.length ≤ Lc
  | _ => True

/-- A chain query is free if its first block is not `sbS`. -/
def freeC (sbS : Blk) : ℕ ⊕ ((St × Blk) ⊕ List Blk) → Prop
  | .inr (.inr bs) => bs.head? ≠ some sbS
  | _ => True

theorem foldR_cons (c : St) (b : Blk) (bs : List Blk) :
    foldR c (b :: bs) = rawQ (c, b) >>= fun c' => foldR c' bs := by
  simp [foldR, List.foldlM_cons]

theorem foldR_bound (c : St) (bs : List Blk) :
    IsQueryBoundP (foldR c bs) (fun i => i.isRight = true) bs.length := by
  induction bs generalizing c with
  | nil => exact isQueryBoundP_pure _ _ _
  | cons b bs ih =>
    rw [foldR_cons]
    refine (isQueryBoundP_bind ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos)
      fun c' _ => ih c').mono (by simp; omega)

/-- **The expansion's raw count**: each raw query costs one, each chain query its length. -/
theorem expand_bound (IV : St) {α : Type} (oc : OracleComp (pcS St Blk) α) (n m Lc : ℕ)
    (hr : IsQueryBoundP oc (fun t => isRawC t = true) n)
    (hc : IsQueryBoundP oc (fun t => isChainC t = true) m)
    (hL : AllQueriesSatisfy oc (chainLenC Lc)) :
    IsQueryBoundP (simulateQ (expandImpl IV) oc) (fun i => i.isRight = true) (n + m * Lc) := by
  induction oc using OracleComp.inductionOn generalizing n m with
  | pure x => exact isQueryBoundP_pure _ _ _
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hr hc
    rw [allQueriesSatisfy_query_bind_iff] at hL
    simp only [simulateQ_bind, simulateQ_spec_query]
    rcases t with n' | q | bs
    · refine (isQueryBoundP_bind (m := n + m * Lc) (n := 0)
        ((isQueryBoundP_query_iff _ _ _).2 fun h => by simp at h) fun u _ => ?_).mono (by omega)
      exact ih u n m (by have h := hr.2 u; rwa [if_neg (by simp [isRawC])] at h)
        (by have h := hc.2 u; rwa [if_neg (by simp [isChainC])] at h) (hL.2 u)
    · have hn : 0 < n := hr.1.resolve_left (by simp [isRawC])
      refine (isQueryBoundP_bind (m := (n - 1) + m * Lc) (n := 1)
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos) fun u _ => ?_).mono (by omega)
      exact ih u (n - 1) m (by
          have h := hr.2 u
          rwa [if_pos (show isRawC (St := St) (Blk := Blk) (.inr (.inl q)) = true from rfl)] at h)
        (by have h := hc.2 u; rwa [if_neg (by simp [isChainC])] at h) (hL.2 u)
    · have hm : 0 < m := hc.1.resolve_left (by simp [isChainC])
      have hlen : bs.length ≤ Lc := hL.1
      refine (isQueryBoundP_bind (m := n + (m - 1) * Lc) (n := bs.length)
        (foldR_bound IV bs) fun u _ => ?_).mono ?_
      · exact ih u n (m - 1) (by have h := hr.2 u; rwa [if_neg (by simp [isRawC])] at h)
          (by
            have h := hc.2 u
            rwa [if_pos (show isChainC (St := St) (Blk := Blk) (.inr (.inr bs)) = true from rfl)] at h)
          (hL.2 u)
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.add_mul, one_mul]
        omega

variable [DecidableEq St] [DecidableEq Blk] [SampleableType St]

/-! ## Public values -/

/-- Some public cell has the value `w`. -/
def PubHit (w : St) (c : Cache St Blk) : Prop := ∃ q, c (.inl q) = some w

/-- Some public cell has the value `IV` or `cv`. -/
def PubBad (IV cv : St) (c : Cache St Blk) : Prop := PubHit IV c ∨ PubHit cv c

/-- Caching any cell keeps a cached public value. -/
theorem pubHit_cacheQuery {w : St} {c : Cache St Blk} (h : PubHit w c)
    (t : (St × Blk) ⊕ Blk) (u : (hS St Blk + tS St Blk).Range t) (ht : c t = none) : PubHit w (c.cacheQuery t u) := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q, ?_⟩
  have hne : (.inl q : (St × Blk) ⊕ Blk) ≠ t := by
    rintro rfl
    rw [hq] at ht
    exact absurd ht (by simp)
  rw [QueryCache.cacheQuery_of_ne c u hne, hq]

/-- A lazy-oracle step keeps a cached public value. -/
theorem pubHit_randomOracle {w : St} {c : Cache St Blk} (h : PubHit w c)
    (t : (St × Blk) ⊕ Blk) {z : (hS St Blk + tS St Blk).Range t × Cache St Blk}
    (hz : z ∈ support (((hS St Blk + tS St Blk).randomOracle t).run c)) : PubHit w z.2 := by
  rw [randomOracle.run_eq] at hz
  cases ht : c t with
  | none =>
    rw [ht] at hz
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact pubHit_cacheQuery h t u ht
  | some v =>
    rw [ht] at hz
    simp only [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact h

/-- **A cached public value stays cached along a phase-two run.** -/
theorem pubHit_routeRO (IV : St) (sbS : Blk) (cv : St) (w : St) {α : Type}
    (oa : OracleComp (unifSpec + hS St Blk) α) (c : Cache St Blk) (h : PubHit w c) :
    ∀ z ∈ support ((simulateQ (routeRO IV sbS cv) oa).run c), PubHit w z.2 := by
  refine simulateQ_run_preservesInv _ (PubHit w) ?_ oa c h
  rintro (n | q) s hs z hz
  · rw [routeRO_run_inl, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact hs
  · by_cases h1 : q = (IV, sbS)
    · subst h1
      rw [routeRO_run_seed, support_pure, Set.mem_singleton_iff] at hz
      rw [hz]; exact hs
    · by_cases h2 : q.1 = cv
      · obtain ⟨c', B⟩ := q
        subst h2
        rw [routeRO_run_row _ _ _ _ _ h1] at hz
        exact pubHit_randomOracle hs (.inr B) hz
      · rw [routeRO_run_pub _ _ _ _ _ h1 h2] at hz
        exact pubHit_randomOracle hs (.inl q) hz

theorem pubBad_routeRO (IV : St) (sbS : Blk) (cv : St) {α : Type}
    (oa : OracleComp (unifSpec + hS St Blk) α) (c : Cache St Blk) (h : PubBad IV cv c) :
    ∀ z ∈ support ((simulateQ (routeRO IV sbS cv) oa).run c), PubBad IV cv z.2 := by
  intro z hz
  rcases h with h | h
  · exact .inl (pubHit_routeRO IV sbS cv IV oa c h z hz)
  · exact .inr (pubHit_routeRO IV sbS cv cv oa c h z hz)

/-- A public step returns the value it leaves cached at its cell. -/
theorem randomOracle_pub_cached (q : St × Blk) (c : Cache St Blk) {z : St × Cache St Blk}
    (hz : z ∈ support (((hS St Blk + tS St Blk).randomOracle (.inl q)).run c)) :
    z.2 (.inl q) = some z.1 := by
  rcases randomOracle_run_pub_cases q c with ⟨v, hv, h⟩ | ⟨-, h⟩
  · rw [h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact hv
  · rw [h, support_map] at hz
    obtain ⟨u, -, rfl⟩ := hz
    exact QueryCache.cacheQuery_self c (.inl q) u

/-! ## Free chains read only public cells -/

/-- **A free chain stays in the public table.**  Run from a chaining value `v ≠ cv` (and, if
`v = IV`, a first block `≠ sbS`), the iteration's raw queries do not raise a potential that
public caching does not raise, or the final cache is `PubBad`. -/
theorem free_fold (IV : St) (sbS : Blk) (cv : St) (Φ : Cache St Blk → ℝ≥0∞)
    (hpub : ∀ (c : Cache St Blk) (q : St × Blk) (u : St), c (.inl q) = none →
      Φ (c.cacheQuery (.inl q) u) ≤ Φ c) :
    ∀ (bs : List Blk) (v : St) (c : Cache St Blk), v ≠ cv → (v = IV → bs.head? ≠ some sbS) →
      ∀ z ∈ support ((simulateQ (routeRO IV sbS cv) (foldR v bs)).run c),
        Φ z.2 ≤ Φ c ∨ PubBad IV cv z.2 := by
  intro bs
  induction bs with
  | nil =>
    intro v c _ _ z hz
    simp only [foldR, List.foldlM_nil, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at hz
    rw [hz]
    exact .inl le_rfl
  | cons b bs ih =>
    intro v c hv hh z hz
    rw [foldR_cons, rawQ, run_simulateQ_query_bind, mem_support_bind_iff] at hz
    obtain ⟨z₁, hz₁, hz⟩ := hz
    have hq : (v, b) ≠ (IV, sbS) := by
      intro e
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
      exact hh rfl rfl
    rw [routeRO_run_pub _ _ _ _ _ hq hv] at hz₁
    have hΦ : Φ z₁.2 ≤ Φ c := by
      rcases randomOracle_run_pub_cases (v, b) c with ⟨u, -, h⟩ | ⟨hnone, h⟩
      · rw [h, support_pure, Set.mem_singleton_iff] at hz₁
        rw [hz₁]
      · rw [h, support_map] at hz₁
        obtain ⟨u, -, rfl⟩ := hz₁
        exact hpub c _ u hnone
    have hcache := randomOracle_pub_cached (v, b) c hz₁
    by_cases hb : z₁.1 = IV ∨ z₁.1 = cv
    · refine .inr (pubBad_routeRO IV sbS cv _ z₁.2 ?_ z hz)
      rcases hb with hb | hb
      · exact .inl ⟨(v, b), hb ▸ hcache⟩
      · exact .inr ⟨(v, b), hb ▸ hcache⟩
    · simp only [not_or] at hb
      rcases ih z₁.1 z₁.2 hb.2 (fun h => absurd h hb.1) z hz with h | h
      · exact .inl (h.trans hΦ)
      · exact .inr h

/-- **Phase-two potential bound with free chain queries.**  A potential that caching a public
cell does not raise and caching a private-row cell raises by at most `ε` is raised by at most
`n·ε` along the run of a program with at most `n` raw compression queries whose chain queries
are all free, or the final cache is `PubBad` — on every run, for `cv ≠ IV`. -/
theorem routeRO_potential_fine (IV : St) (sbS : Blk) (cv : St) (hcv : cv ≠ IV)
    (Φ : Cache St Blk → ℝ≥0∞) (ε : ℝ≥0∞)
    (hpub : ∀ (c : Cache St Blk) (q : St × Blk) (u : St), Φ (c.cacheQuery (.inl q) u) ≤ Φ c)
    (hrow : ∀ (c : Cache St Blk) (B : Blk) (u : St), Φ (c.cacheQuery (.inr B) u) ≤ Φ c + ε)
    {α : Type} (oc : OracleComp (pcS St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP oc (fun t => isRawC t = true) n)
    (hfree : AllQueriesSatisfy oc (freeC sbS)) (c : Cache St Blk) :
    ∀ z ∈ support ((simulateQ (routeRO IV sbS cv) (simulateQ (expandImpl IV) oc)).run c),
      Φ z.2 ≤ Φ c + n * ε ∨ PubBad IV cv z.2 := by
  induction oc using OracleComp.inductionOn generalizing n c with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact .inl le_self_add
  | query_bind t k ih =>
    intro z hz
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [allQueriesSatisfy_query_bind_iff] at hfree
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at hz
    obtain ⟨z₁, hz₁, hz⟩ := hz
    rcases t with n' | q | bs
    · -- uniform bits: the cache is unchanged
      have e : (simulateQ (routeRO IV sbS cv) (expandImpl IV (.inl n'))).run c =
          (fun u => (u, c)) <$> (unifSpec.query n' : ProbComp (Fin (n' + 1))) := by
        simp only [expandImpl, simulateQ_spec_query]
        rw [← routeRO_run_inl IV sbS cv n' c]
      rw [e, support_map] at hz₁
      obtain ⟨u, -, rfl⟩ := hz₁
      exact ih u n (by have h := hn.2 u; rwa [if_neg (by simp [isRawC])] at h) (hfree.2 u) c z hz
    · -- one raw query
      have hn0 : 0 < n := hn.1.resolve_left (by simp [isRawC])
      have h1 := routeRO_potential_le IV sbS cv Φ ε hpub hrow (rawQ q) 1
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos) c z₁ hz₁
      rcases ih z₁.1 (n - 1) (by
          have h := hn.2 z₁.1
          rwa [if_pos (show isRawC (St := St) (Blk := Blk) (.inr (.inl q)) = true from rfl)] at h)
        (hfree.2 z₁.1)
        z₁.2 z hz with h | h
      · refine .inl (h.trans ((add_le_add h1 le_rfl).trans (le_of_eq ?_)))
        obtain ⟨n'', rfl⟩ : ∃ n'', n = n'' + 1 := ⟨n - 1, by omega⟩
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
        ring
      · exact .inr h
    · -- a free chain query
      have hhead : bs.head? ≠ some sbS := hfree.1
      rcases free_fold IV sbS cv Φ (fun c q u _ => hpub c q u) bs IV c hcv.symm (fun _ => hhead)
        z₁ hz₁ with h1 | h1
      · rcases ih z₁.1 n (by have h := hn.2 z₁.1; rwa [if_neg (by simp [isRawC])] at h)
          (hfree.2 z₁.1) z₁.2 z hz with h | h
        · exact .inl (h.trans (add_le_add h1 le_rfl))
        · exact .inr h
      · exact .inr (pubBad_routeRO IV sbS cv _ z₁.2 h1 z hz)

/-- **Phase-two bad event with free chain queries.**  A bad predicate of the cache that caching
a fresh public cell never fires and caching a fresh private-row cell fires with probability at
most `ε`: along the run of a program with at most `n` raw compression queries and only free
chain queries, from a non-bad cache, the final cache is bad and not `PubBad` with probability at
most `n·ε`, for `cv ≠ IV`. -/
theorem prEvent_routeRO_bad_fine (IV : St) (sbS : Blk) (cv : St) (hcv : cv ≠ IV)
    (bad : Cache St Blk → Prop) (ε : ℝ≥0∞)
    (hpub : ∀ (c : Cache St Blk) (q : St × Blk) (u : St), ¬ bad c → c (.inl q) = none →
      ¬ bad (c.cacheQuery (.inl q) u))
    (hrow : ∀ (c : Cache St Blk) (B : Blk), ¬ bad c → c (.inr B) = none →
      Pr{let u ← ($ᵗ St : ProbComp St)}[bad (c.cacheQuery (.inr B) u)] ≤ ε)
    {α : Type} (oc : OracleComp (pcS St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP oc (fun t => isRawC t = true) n)
    (hfree : AllQueriesSatisfy oc (freeC sbS)) (c : Cache St Blk) (hc : ¬ bad c) :
    Pr{let z ← (simulateQ (routeRO IV sbS cv) (simulateQ (expandImpl IV) oc)).run c}[
      bad z.2 ∧ ¬ PubBad IV cv z.2] ≤ n * ε := by
  classical
  induction oc using OracleComp.inductionOn generalizing n c with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure]
    rw [prEvent_pure]
    simp only [hc, false_and, ↓reduceIte]
    exact zero_le
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hn
    rw [allQueriesSatisfy_query_bind_iff] at hfree
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    rcases t with n' | q | bs
    · have e : (simulateQ (routeRO IV sbS cv) (expandImpl IV (.inl n'))).run c =
          (fun u => (u, c)) <$> (unifSpec.query n' : ProbComp (Fin (n' + 1))) := by
        simp only [expandImpl, simulateQ_spec_query]
        rw [← routeRO_run_inl IV sbS cv n' c]
      rw [e]
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z₁ hz₁ => ?_
      rw [support_map] at hz₁
      obtain ⟨u, -, rfl⟩ := hz₁
      exact ih u n (by have h := hn.2 u; rwa [if_neg (by simp [isRawC])] at h) (hfree.2 u) c hc
    · have hn0 : 0 < n := hn.1.resolve_left (by simp [isRawC])
      have h1 := prEvent_routeRO_bad_le IV sbS cv bad ε hpub hrow (rawQ q) 1
        ((isQueryBoundP_query_iff _ _ _).2 fun _ => Nat.one_pos) c hc
      refine (prEvent_bind_le_prEvent_add _ _ (fun z₁ => bad z₁.2) _ (ε := (n - 1 : ℕ) * ε)
        fun z₁ hz₁ => ih z₁.1 (n - 1) (by
          have h := hn.2 z₁.1
          rwa [if_pos (show isRawC (St := St) (Blk := Blk) (.inr (.inl q)) = true from rfl)] at h)
          (hfree.2 z₁.1) z₁.2 hz₁).trans ?_
      refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
      obtain ⟨n'', rfl⟩ : ∃ n'', n = n'' + 1 := ⟨n - 1, by omega⟩
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring
    · have hhead : bs.head? ≠ some sbS := hfree.1
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z₁ hz₁ => ?_
      have hff := free_fold IV sbS cv (fun c' => if bad c' then 1 else 0)
        (fun c' q u hnone => by
          by_cases hb : bad c'
          · simp only [hb, ↓reduceIte]
            split_ifs <;> simp
          · simp only [hb, ↓reduceIte, hpub c' q u hb hnone]; exact le_rfl)
        bs IV c hcv.symm (fun _ => hhead) z₁ hz₁
      by_cases hpb : PubBad IV cv z₁.2
      · rw [prEvent_eq_zero_of_forall_mem_support _ _ fun z hz h =>
          h.2 (pubBad_routeRO IV sbS cv _ z₁.2 hpb z hz)]
        exact zero_le
      · have hb1 : ¬ bad z₁.2 := by
          rcases hff with h | h
          · intro hb
            simp only [hb, hc, ↓reduceIte] at h
            exact absurd h (by simp)
          · exact absurd h hpb
        exact ih z₁.1 n (by have h := hn.2 z₁.1; rwa [if_neg (by simp [isRawC])] at h)
          (hfree.2 z₁.1) z₁.2 hb1

/-! ## The probability of reaching a bad public value -/

variable [Fintype St]

/-- **`PubBad` in phase two.**  From a cache that is not `PubBad`, a phase-two run making at most
`n` compression queries ends `PubBad` with probability at most `n·2/|St|` (each fresh public
value is `IV` or `cv` with probability at most `2/|St|`; the seed cell and private-row cells
cache no public value). -/
theorem prEvent_routeRO_pubBad_le (IV : St) (sbS : Blk) (cv : St) {α : Type}
    (oa : OracleComp (unifSpec + hS St Blk) α) (n : ℕ)
    (hn : IsQueryBoundP oa (fun i => i.isRight = true) n) (c : Cache St Blk)
    (hc : ¬ PubBad IV cv c) :
    Pr{let z ← (simulateQ (routeRO IV sbS cv) oa).run c}[PubBad IV cv z.2] ≤
      n * (2 * (Fintype.card St : ℝ≥0∞)⁻¹) := by
  classical
  refine prEvent_bad_le_of_step _ (PubBad IV cv) _ _ ?_ ?_ oa n hn c hc
  · rintro (n | q) s hs ht
    · simp at ht
    · have hpure : ∀ v : St, Pr{let z ← (pure (v, s) : ProbComp (St × Cache St Blk))}[
          PubBad IV cv z.2] ≤ 2 * (Fintype.card St : ℝ≥0∞)⁻¹ := fun v => by
        rw [prEvent_pure]
        simp only [hs, ↓reduceIte]
        exact zero_le
      by_cases h1 : q = (IV, sbS)
      · subst h1
        rw [routeRO_run_seed]
        exact hpure cv
      · by_cases h2 : q.1 = cv
        · obtain ⟨c', B⟩ := q
          subst h2
          rw [routeRO_run_row _ _ _ _ _ h1]
          rcases randomOracle_run_row_cases B s with ⟨v, -, h⟩ | ⟨hnone, h⟩
          · rw [h]; exact hpure v
          · rw [h, prEvent_map, prEvent_eq_zero_of_forall_not _ _ fun u hu => hs ?_]
            · exact zero_le
            · have key : ∀ w, PubHit w (s.cacheQuery (.inr B) u) → PubHit w s := by
                rintro w ⟨q', hq'⟩
                refine ⟨q', ?_⟩
                rwa [QueryCache.cacheQuery_of_ne (t := .inr B) s u (by simp)] at hq'
              rcases hu with hu | hu
              · exact .inl (key _ hu)
              · exact .inr (key _ hu)
        · rw [routeRO_run_pub _ _ _ _ _ h1 h2]
          rcases randomOracle_run_pub_cases q s with ⟨v, -, h⟩ | ⟨hnone, h⟩
          · rw [h]; exact hpure v
          · rw [h, prEvent_map]
            have key : ∀ u, PubBad IV cv (s.cacheQuery (.inl q) u) → u = IV ∨ u = cv := by
              intro u hu
              have hw : ∀ w, PubHit w (s.cacheQuery (.inl q) u) → ¬ PubHit w s → u = w := by
                rintro w ⟨q', hq'⟩ hnw
                by_cases e : q' = q
                · subst e
                  rw [QueryCache.cacheQuery_self] at hq'
                  exact Option.some.inj hq'
                · rw [QueryCache.cacheQuery_of_ne (t := .inl q) s u (by simpa using e)] at hq'
                  exact absurd ⟨q', hq'⟩ hnw
              rcases hu with hu | hu
              · exact .inl (hw _ hu fun h => hs (.inl h))
              · exact .inr (hw _ hu fun h => hs (.inr h))
            refine (prEvent_mono _ _ (fun u => u = IV ∨ u = cv) fun u hu => key u hu).trans ?_
            refine (prEvent_or_le _ _ _).trans (le_of_eq ?_)
            rw [SampleableType.prEvent_uniformSample_eq_singleton,
              SampleableType.prEvent_uniformSample_eq_singleton, two_mul]
  · rintro (n | q) s hs ht z hz
    · rw [routeRO_run_inl, support_map] at hz
      obtain ⟨u, -, rfl⟩ := hz
      exact hs
    · simp at ht

end Ideal

#print axioms Ideal.expand_bound
#print axioms Ideal.free_fold
#print axioms Ideal.routeRO_potential_fine
#print axioms Ideal.prEvent_routeRO_pubBad_le
#print axioms Ideal.prEvent_routeRO_bad_fine
