import Reduction.Resources2
import Reduction.TightCaps

/-!
# Phase-1 counts of the WOTS adversaries, generic part

Collection-oracle queries of phase 1 of `Lazy.bWotsWith my A` (in particular `Lazy.bWotsS A`),
counted in an arbitrary *counting semantics* `CSem` of the WOTS-game interface:

* `CSem` — an interpretation `sem` of programs over `WSpec prims` in a state monad over `S`, with a
  signing history `hist : S → List Entry` and a counter `n : S → ℕ`, such that a collection query
  raises the counter by at most `cC` and leaves the history alone, and a signing query is either
  refused (instance not allowed or already in the history; counter unchanged) or appends its
  entry to the history and raises the counter by at most `K`.
* `chooseBody_count`, `bWotsWith_choose_count` — in every run from an empty history the counter
  grows by at most `cC * wotsQc vp + #inst * K`, where
  `wotsQc vp = Σ_{a ∈ wotsInsts} own(a.layer) + own(d)`, `own 0 = k·(2^(a+1) - 1) + 1` (one FORS
  public key), `own (l+1) = 2^(h'+1) - 1` (one XMSS root over recorded chain ends).
  The proof is the memoisation argument made formal: a potential over the signed instances.
* `simSem` — the counting semantics given by running the simulator `WotsGame.simChoose` of a
  reduction inside its SM game (`WotsFinal.outer O₂`), for any counter `n` on the game state that
  grows by at most one per query satisfying `pc` (`growth_of_qb`: `IsQueryBoundP` ⇒ growth).
* `wotsQc_closed`, `wotsQc_128s` — closed form and numeral.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## From a syntactic query bound to growth of a counter on the oracle state -/

/-- If every query raises the counter `n` of the oracle state by at most one, and only when its
index satisfies `p`, a program with at most `N` queries satisfying `p` raises it by at most `N`
in every run. -/
theorem growth_of_qb {ι : Type} {spec : OracleSpec ι} {Sg : Type}
    (O : QueryImpl spec (StateT Sg ProbComp)) (n : Sg → ℕ) (p : ι → Prop) [DecidablePred p]
    (hO : ∀ t σ, ∀ z ∈ support ((O t).run σ), n z.2 ≤ n σ + (if p t then 1 else 0))
    {α : Type} (oa : OracleComp spec α) (N : ℕ) (h : IsQueryBoundP oa p N) (σ : Sg) :
    ∀ z ∈ support ((simulateQ O oa).run σ), n z.2 ≤ n σ + N := by
  induction oa using OracleComp.inductionOn generalizing N σ with
  | pure x =>
    intro z hz
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]; exact Nat.le_add_right _ _
  | query_bind t k ih =>
    intro z hz
    rw [isQueryBoundP_query_bind_iff] at h
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map, StateT.run_bind] at hz
    rw [mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    have h1 := hO t σ w hw
    have h2 := ih w.1 _ (h.2 w.1) w.2 z hz
    by_cases hp : p t
    · simp only [if_pos hp] at h1 h2
      have : 0 < N := h.1.resolve_left (not_not.2 hp)
      omega
    · simp only [if_neg hp] at h1 h2
      omega

/-! ## Budgets -/

/-- Collection queries of one FORS public key: `k` trees of `2^a` leaves and `2^a - 1` nodes,
and one `T_k`. -/
def forsC (vp : ValidatedParams) : ℕ := vp.params.k * Lazy.merkleB 1 1 vp.params.a + 1

/-- Collection queries of one XMSS root over recorded chain ends: `2^h'` calls `T_len` and
`2^h' - 1` node hashes. -/
def treeC (vp : ValidatedParams) : ℕ := Lazy.merkleB 1 1 vp.params.hp

/-- Collection queries `bWots` spends on the message of an instance of layer `l` (or, at
`l = d`, on `PK.root`), not counting the messages of the instances below it. -/
def own (vp : ValidatedParams) (l : ℕ) : ℕ := if l = 0 then forsC vp else treeC vp

/-- **`qc`**: the collection queries of phase 1 of `bWotsWith my A`. -/
def wotsQc (vp : ValidatedParams) : ℕ :=
  ((wotsInsts vp).map fun a => own vp a.layer).sum + own vp vp.params.d

/-! ## Counting semantics of the WOTS-game interface -/

/-- A counting semantics of programs over the WOTS-game interface (see the module docstring). -/
structure CSem (vp : ValidatedParams) (prims : Primitives vp.params) (S : Type) where
  sem : {α : Type} → OracleComp (WSpec prims) α → S → ProbComp (α × S)
  hist : S → List (WotsGame.Entry prims)
  n : S → ℕ
  cC : ℕ
  K : ℕ
  sem_pure : ∀ {α : Type} (x : α) (s : S), sem (pure x) s = pure (x, s)
  sem_bind : ∀ {α β : Type} (oa : OracleComp (WSpec prims) α)
    (f : α → OracleComp (WSpec prims) β) (s : S),
    sem (oa >>= f) s = sem oa s >>= fun z => sem (f z.1) z.2
  lift : ∀ {β : Type} (my : ProbComp β) (s : S),
    ∀ z ∈ support (sem (monadLift my : OracleComp (WSpec prims) β) s), z.2 = s
  coll : ∀ (q : prims.AdrsKey × List prims.Y) (s : S),
    ∀ z ∈ support (sem ((WSpec prims).query (Sum.inr (Sum.inr q)) :
        OracleComp (WSpec prims) (Option prims.Y)) s),
      hist z.2 = hist s ∧ n z.2 ≤ n s + cC
  sign : ∀ (q : Adrs × prims.Y) (s : S),
    ∀ z ∈ support (sem ((WSpec prims).query (Sum.inr (Sum.inl q)) :
        OracleComp (WSpec prims)
          (Option (WotsSig vp.params prims.core × Vector prims.Y vp.params.len))) s),
      (z.1 = none ∧ hist z.2 = hist s ∧ n z.2 ≤ n s ∧
          (q.1 ∉ wotsInsts vp ∨ q.1 ∈ (hist s).map (·.1))) ∨
        (∃ sig tops, z.1 = some (sig, tops) ∧ hist z.2 = hist s ++ [(q.1, q.2, sig, tops)] ∧
          q.1 ∈ wotsInsts vp ∧ q.1 ∉ (hist s).map (·.1) ∧ n z.2 ≤ n s + K)

namespace CSem

variable {S : Type} (C : CSem vp prims S)

/-- Potential of newly signed instances. -/
def pot (ext : List (WotsGame.Entry prims)) : ℕ :=
  (ext.map fun e => C.cC * own vp e.1.layer + C.K).sum

theorem pot_nil : C.pot [] = 0 := rfl

theorem pot_append (e1 e2 : List (WotsGame.Entry prims)) :
    C.pot (e1 ++ e2) = C.pot e1 + C.pot e2 := by
  simp [pot]

/-- Postcondition: the mirrored history equals the semantic history, which extends the initial
one by entries of layer `< L` whose potential, plus `cC * N`, pays for the counter. -/
def Post (L N : ℕ) (s : S) (h' : List (WotsGame.Entry prims)) (s' : S) : Prop :=
  h' = C.hist s' ∧ Lazy.HistInv vp (C.hist s') ∧
    ∃ ext, C.hist s' = C.hist s ++ ext ∧ (∀ e ∈ ext, e.1.layer < L) ∧
      C.n s' ≤ C.n s + C.cC * N + C.pot ext

/-- Hoare triple with a budget of `N` own collection queries and new entries of layer `< L`. -/
def Spec {α : Type} (c : WM prims α) (N L : ℕ) : Prop :=
  ∀ s, Lazy.HistInv vp (C.hist s) →
    ∀ z ∈ support (C.sem (c.run (C.hist s)) s), C.Post L N s z.1.2 z.2

theorem semW_bind {α β : Type} (c : WM prims α) (f : α → WM prims β)
    (h : List (WotsGame.Entry prims)) (s : S) :
    C.sem ((c >>= f).run h) s =
      C.sem (c.run h) s >>= fun w => C.sem ((f w.1.1).run w.1.2) w.2 := by
  rw [StateT.run_bind, C.sem_bind]

theorem spec_pure {α : Type} (x : α) (N L : ℕ) : C.Spec (pure x : WM prims α) N L := by
  intro s hI z hz
  rw [StateT.run_pure, C.sem_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  exact ⟨rfl, hI, [], by simp, by simp, by simp [pot]⟩

theorem spec_bind {α β : Type} {c : WM prims α} {f : α → WM prims β} {N1 N2 L : ℕ}
    (hc : C.Spec c N1 L) (hf : ∀ x, C.Spec (f x) N2 L) : C.Spec (c >>= f) (N1 + N2) L := by
  intro s hI z hz
  rw [semW_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  obtain ⟨e1, hI1, ext1, hx1, hl1, hn1⟩ := hc s hI w hw
  rw [e1] at hz
  obtain ⟨e2, hI2, ext2, hx2, hl2, hn2⟩ := hf w.1.1 w.2 hI1 z hz
  refine ⟨e2, hI2, ext1 ++ ext2, by rw [hx2, hx1, List.append_assoc], ?_, ?_⟩
  · intro e he
    rcases List.mem_append.1 he with h0 | h0
    · exact hl1 e h0
    · exact hl2 e h0
  · rw [pot_append, Nat.mul_add]
    omega

theorem spec_mono {α : Type} {c : WM prims α} {N N' L L' : ℕ} (hc : C.Spec c N L)
    (hN : N ≤ N') (hL : L ≤ L') : C.Spec c N' L' := by
  intro s hI z hz
  obtain ⟨e1, hI1, ext1, hx1, hl1, hn1⟩ := hc s hI z hz
  refine ⟨e1, hI1, ext1, hx1, fun e he => lt_of_lt_of_le (hl1 e he) hL, ?_⟩
  have := Nat.mul_le_mul_left C.cC hN
  omega

theorem semW_lift {α : Type} (x : OracleComp (WSpec prims) α)
    (h : List (WotsGame.Entry prims)) (s : S) :
    C.sem ((monadLift x : WM prims α).run h) s =
      C.sem x s >>= fun w => pure ((w.1, h), w.2) := by
  rw [StateT.run_monadLift, C.sem_bind]
  simp only [C.sem_pure]
  rfl

theorem spec_wColl (key : prims.AdrsKey) (xs : List prims.Y) (L : ℕ) :
    C.Spec (wColl key xs) 1 L := by
  intro s hI z hz
  unfold wColl at hz
  rw [semW_bind, semW_lift, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  rw [mem_support_bind_iff] at hw
  obtain ⟨v, hv, hw⟩ := hw
  rw [support_pure, Set.mem_singleton_iff] at hw
  subst hw
  rw [StateT.run_pure, C.sem_pure, support_pure, Set.mem_singleton_iff] at hz
  subst hz
  obtain ⟨h1, h2⟩ := C.coll (key, xs) s v hv
  refine ⟨h1.symm, h1 ▸ hI, [], by simpa using h1, by simp, ?_⟩
  simp only [pot_nil]
  omega

theorem semW_get_bind {α : Type} (f : List (WotsGame.Entry prims) → WM prims α)
    (h : List (WotsGame.Entry prims)) (s : S) :
    C.sem ((get >>= f).run h) s = C.sem ((f h).run h) s := by
  rw [StateT.run_bind, StateT.run_get, pure_bind]

/-- `topsAt` is free once the message of the instance is paid by the instance's potential. -/
theorem spec_topsAt {a : Adrs} {msg : WM prims prims.Y} {l : ℕ} (ha : a ∈ wotsInsts vp)
    (hl : a.layer = l) (hmsg : C.Spec msg (own vp l) l) : C.Spec (topsAt a msg) 0 (l + 1) := by
  intro s hI z hz
  unfold topsAt at hz
  rw [semW_get_bind] at hz
  cases hf : (C.hist s).find? (fun e => decide (e.1 = a)) with
  | some e =>
    simp only [hf] at hz
    exact C.spec_pure _ 0 (l + 1) s hI z hz
  | none =>
    simp only [hf] at hz
    rw [semW_bind, mem_support_bind_iff] at hz
    obtain ⟨w, hw, hz⟩ := hz
    obtain ⟨e1, hI1, ext1, hx1, hl1, hn1⟩ := hmsg s hI w hw
    rw [semW_bind, semW_lift, mem_support_bind_iff] at hz
    obtain ⟨u, hu, hz⟩ := hz
    rw [mem_support_bind_iff] at hu
    obtain ⟨v, hv, hu⟩ := hu
    rw [support_pure, Set.mem_singleton_iff] at hu
    subst hu
    have hnot : a ∉ (C.hist w.2).map (·.1) := by
      intro hm
      rw [hx1, List.map_append, List.mem_append] at hm
      rcases hm with hm | hm
      · obtain ⟨e, he, hea⟩ := List.mem_map.1 hm
        have := List.find?_eq_none.1 hf e he
        simp at this
        exact this hea
      · obtain ⟨e, he, hea⟩ := List.mem_map.1 hm
        have := hl1 e he
        rw [hea, hl] at this
        exact lt_irrefl _ this
    rcases C.sign (a, w.1.1) w.2 v hv with ⟨-, -, -, hbad⟩ | ⟨sig, tops, hv1, hv2, -, -, hv3⟩
    · exact absurd hbad (by simp only [not_or, not_not]; exact ⟨ha, hnot⟩)
    · simp only [hv1] at hz
      rw [semW_bind, mem_support_bind_iff] at hz
      obtain ⟨y, hy, hz⟩ := hz
      have hy' : y = ((PUnit.unit, w.1.2 ++ [(a, w.1.1, sig, tops)]), v.2) := by
        simpa [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, StateT.run,
          C.sem_pure] using hy
      subst hy'
      rw [StateT.run_pure, C.sem_pure, support_pure, Set.mem_singleton_iff] at hz
      subst hz
      refine ⟨by rw [hv2, e1], ?_, ext1 ++ [(a, w.1.1, sig, tops)], ?_, ?_, ?_⟩
      · rw [hv2]
        exact Lazy.histInv_append hI1 _ ha hnot
      · show C.hist v.2 = _
        rw [hv2, hx1, List.append_assoc]
      · intro e he
        rcases List.mem_append.1 he with h0 | h0
        · exact Nat.lt_succ_of_lt (hl1 e h0)
        · rw [List.mem_singleton] at h0
          subst h0
          show a.layer < l + 1
          omega
      · show C.n v.2 ≤ _
        rw [pot_append]
        have : C.pot [(a, w.1.1, sig, tops)] = C.cC * own vp l + C.K := by
          simp [pot, hl]
        omega

/-- A program over the hash callbacks with at most `N` calls costs `N` collection queries. -/
theorem spec_free {α : Type} (x : OracleComp (x1_spec prims) α) (N L : ℕ)
    (hx : IsQueryBoundP x (fun _ => True) N) : C.Spec (simulateQ x1_implW x) N L := by
  induction x using OracleComp.inductionOn generalizing N with
  | pure x =>
    rw [simulateQ_pure]
    exact C.spec_pure x N L
  | query_bind t k ih =>
    rw [isQueryBoundP_query_bind_iff] at hx
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
      OracleQuery.cont_query, id_map]
    have hN : 0 < N := hx.1.resolve_left (fun h => h trivial)
    have h2 := hx.2
    simp only [if_true] at h2
    refine C.spec_mono (C.spec_bind (C.spec_wColl _ _ L) fun u => ih u (N - 1) (h2 u)) ?_ le_rfl
    omega

open PerfectMerkleTree in
theorem spec_merkle (P : ℕ → ℕ → Prop)
    (hP : ∀ z t, P (z + 1) t → P z (2 * t) ∧ P z (2 * t + 1))
    (leafW : ℕ → WM prims prims.Y) (nodeW : ℕ → ℕ → prims.Y → prims.Y → WM prims prims.Y)
    (cl cn L : ℕ) (hleaf : ∀ i, P 0 i → C.Spec (leafW i) cl L)
    (hnode : ∀ z t l r, P (z + 1) t → C.Spec (nodeW (z + 1) t l r) cn L) :
    ∀ z t, P z t → C.Spec (merkleRootM leafW nodeW z t) (Lazy.merkleB cl cn z) L
  | 0, t, h => hleaf t h
  | z + 1, t, h => by
    rw [merkleRootM]
    exact C.spec_bind (spec_merkle P hP leafW nodeW cl cn L hleaf hnode z (2 * t) (hP z t h).1)
      fun l => C.spec_bind (spec_merkle P hP leafW nodeW cl cn L hleaf hnode z (2 * t + 1)
        (hP z t h).2) fun r => hnode z t l r h

/-- Calls of the FORS public key as a free program over the hash callbacks. -/
theorem x1_free_qb (tbl : SecretTable vp prims) (adrs : Adrs) :
    IsQueryBoundP (x1_free (prims := prims) tbl adrs) (fun _ => True) (forsC vp) := by
  unfold x1_free forsPkGenWithSecret forsC
  refine Lazy.qb_bind _ (Lazy.qb_ofFnM _ _ _ fun i => ?_) fun roots => by simp
  unfold forsRootWithSecret
  refine Lazy.qb_merkleRoot _ _ _ 1 1 _ _ (fun j => ?_) (fun h i l r => ?_)
  · exact (Lazy.qb_bind _ (n := 0) (m := 1) (isQueryBoundP_pure _ _ _) fun x => by
      simp).mono (by omega)
  · unfold forsNodeHashWith
    simp

/-- The message of an instance of layer `l` costs `own vp l` collection queries beyond the
potential of the instances it signs. -/
theorem spec_msgAt (tbl : SecretTable vp prims) :
    ∀ (l tree leaf : ℕ), l ≤ vp.params.d →
    (l < vp.params.d → tree < 2 ^ layerTreeHeight vp l ∧ leaf < 2 ^ vp.params.hp) →
    (l = vp.params.d → tree = 0 ∧ leaf = 0) →
    C.Spec (msgAt tbl l tree leaf) (own vp l) l
  | 0, tree, leaf, _, _, _ => by
    rw [x1_msgAt_eq]
    exact C.spec_free _ _ 0 (x1_free_qb tbl _)
  | l + 1, tree, leaf, hl, h1, h2 => by
    have hT := x2_child_lt hl h1 h2
    have hld : l < vp.params.d := by omega
    have hown : own vp (l + 1) = Lazy.merkleB 1 1 vp.params.hp := by simp [own, treeC]
    rw [msgAt, hown]
    refine C.spec_merkle (fun z t => z ≤ vp.params.hp ∧ t < 2 ^ (vp.params.hp - z)) ?_ _ _ 1 1
      (l + 1) ?_ ?_ vp.params.hp 0 ⟨le_rfl, by simp⟩
    · rintro z t ⟨hz, ht⟩
      have e : vp.params.hp - z = (vp.params.hp - (z + 1)) + 1 := by omega
      rw [e, pow_succ]
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · rintro i ⟨-, hi⟩
      rw [Nat.sub_zero] at hi
      have hmem : wotsLeafAdrs (GeneralHypertree.layerAdrs l (tree * 2 ^ vp.params.hp + leaf)) i ∈
          wotsInsts vp := by
        simp only [wotsInsts, List.mem_map]
        exact ⟨⟨⟨l, hld⟩, ⟨_, hT⟩, ⟨i, hi⟩⟩, mem_allWotsInstances vp _, rfl⟩
      exact C.spec_bind (N1 := 0) (C.spec_topsAt hmem rfl
        (spec_msgAt tbl l _ i hld.le (fun _ => ⟨hT, hi⟩) (fun h => absurd h hld.ne)))
        fun tops => C.spec_wColl _ _ _
    · rintro z t x y ⟨hz, ht⟩
      exact C.spec_wColl _ _ _

theorem spec_forM {β : Type} (f : β → WM prims PUnit) (L : ℕ) (hf : ∀ b, C.Spec (f b) 0 L) :
    ∀ ps : List β, C.Spec (ps.forM f) 0 L
  | [] => C.spec_pure _ 0 L
  | p :: ps => C.spec_bind (f := fun _ => ps.forM f) (hf p) fun _ => spec_forM f L hf ps

theorem spec_chooseBody (tbl : SecretTable vp prims) :
    C.Spec (chooseBody tbl) (own vp vp.params.d) vp.params.d := by
  unfold chooseBody
  refine C.spec_mono (C.spec_bind (N1 := 0) (C.spec_forM _ _ (fun pos => ?_) _) fun _ =>
    C.spec_msgAt tbl vp.params.d 0 0 le_rfl (fun h => absurd h (lt_irrefl _))
      (fun _ => ⟨rfl, rfl⟩)) (Nat.zero_add _).le le_rfl
  have hmem : wotsInstanceAdrs pos ∈ wotsInsts vp :=
    List.mem_map.2 ⟨pos, mem_allWotsInstances vp pos, rfl⟩
  exact C.spec_bind (N1 := 0) (C.spec_mono (C.spec_topsAt hmem rfl
    (C.spec_msgAt tbl pos.layer.val pos.tree.val pos.leaf.val pos.layer.isLt.le
      (fun _ => ⟨pos.tree.isLt, pos.leaf.isLt⟩) (fun h => absurd h pos.layer.isLt.ne)))
    le_rfl pos.layer.isLt) fun _ => C.spec_pure _ 0 _

/-- The potential of a duplicate-free history over allowed instances is at most that of all
instances. -/
theorem pot_le {ext : List (WotsGame.Entry prims)} (hI : Lazy.HistInv vp ext) :
    C.pot ext ≤ ((wotsInsts vp).map fun a => C.cC * own vp a.layer + C.K).sum := by
  have h1 : C.pot ext = ((ext.map (·.1)).map fun a => C.cC * own vp a.layer + C.K).sum := by
    simp [pot, Function.comp_def]
  rw [h1]
  obtain ⟨l', hp, hs⟩ := List.subperm_of_subset hI.1 hI.2
  rw [← (hp.map _).sum_eq]
  exact (hs.map _).sum_le_sum fun _ _ => Nat.zero_le _

theorem sum_insts (cC K : ℕ) :
    ((wotsInsts vp).map fun a => cC * own vp a.layer + K).sum =
      cC * ((wotsInsts vp).map fun a => own vp a.layer).sum + (wotsInsts vp).length * K := by
  induction wotsInsts vp with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    ring

/-- **Collection queries of `chooseBody`** in any counting semantics. -/
theorem chooseBody_count (tbl : SecretTable vp prims) (s : S) (hs : C.hist s = []) :
    ∀ z ∈ support (C.sem ((chooseBody tbl).run []) s),
      C.n z.2 ≤ C.n s + C.cC * wotsQc vp + (wotsInsts vp).length * C.K := by
  intro z hz
  have hI : Lazy.HistInv vp (C.hist s) := hs ▸ Lazy.histInv_nil
  rw [← hs] at hz
  obtain ⟨-, hI1, ext, hx, -, hn⟩ := C.spec_chooseBody tbl s hI z hz
  rw [hs, List.nil_append] at hx
  have hp := C.pot_le (hx ▸ hI1)
  rw [sum_insts] at hp
  unfold wotsQc
  rw [Nat.mul_add]
  omega

/-- **Collection queries of phase 1 of `bWotsWith my A`** in any counting semantics. -/
theorem bWotsWith_choose_count (my : ProbComp (SecretTable vp prims))
    (A : Forger vp prims optRand pkSeedDist) (s : S) (hs : C.hist s = []) :
    ∀ z ∈ support (C.sem (Lazy.bWotsWith my A).choose s),
      C.n z.2 ≤ C.n s + C.cC * wotsQc vp + (wotsInsts vp).length * C.K := by
  intro z hz
  rw [Lazy.bWotsWith_choose_eq, C.sem_bind, mem_support_bind_iff] at hz
  obtain ⟨w, hw, hz⟩ := hz
  have hw2 := C.lift my s w hw
  rw [C.sem_bind, mem_support_bind_iff] at hz
  obtain ⟨y, hy, hz⟩ := hz
  have hz' : z ∈ support (pure ((w.1, y.1.2, y.1.1), y.2) :
      ProbComp ((Lazy.bWotsWith my A).State × S)) :=
    (C.sem_pure (α := (Lazy.bWotsWith my A).State) _ _) ▸ hz
  rw [support_pure] at hz'
  rw [Set.mem_singleton_iff.1 hz']
  rw [hw2] at hy
  exact C.chooseBody_count _ s hs y hy

end CSem

end Open
end Reduction

namespace Reduction
namespace Open

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-! ## The counting semantics of a reduction's simulator inside its SM game -/

section Sim

variable {ι : Type} {spec : OracleSpec ι} {Sg : Type}

/-- What the simulated signing oracle runs for an accepted query: the revealed values, then the
chain ends. -/
def signProg (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y) (a : Adrs) (m : prims.Y) :
    OracleComp (unifSpec + spec) (WotsSig vp.params prims.core × Vector prims.Y vp.params.len) :=
  (Vector.ofFnM fun i : Fin vp.params.len =>
      startVal (wotsChainAdrs a i.val) (chainStepsCore prims.core m i.val)) >>= fun sig =>
    wotsPkFromSigTopsWith prims.core chainHash sig m a >>= fun tops => pure (sig, tops)

theorem simImpl_run_unif (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (k : ℕ) (g : List (WotsGame.Entry prims)) :
    (WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll (Sum.inl k)).run g =
      (liftM ((unifSpec + spec).query (Sum.inl k)) : OracleComp (unifSpec + spec) _) >>=
        fun u => pure (u, g) := by
  simp [WotsFinal.simImpl]
  rfl

theorem simImpl_run_coll (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (q : prims.AdrsKey × List prims.Y) (g : List (WotsGame.Entry prims)) :
    (WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll (Sum.inr (Sum.inr q))).run g =
      if WotsGame.reservedKey (wotsInsts vp) q.1 = true then pure (none, g)
      else coll q.1 q.2 >>= fun y => pure (some y, g) := by
  split_ifs with h
  · simp [WotsFinal.simImpl, WotsGame.simCollOracle, h]
  · simp [WotsFinal.simImpl, WotsGame.simCollOracle, h]

theorem simImpl_run_sign (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (q : Adrs × prims.Y) (g : List (WotsGame.Entry prims)) :
    (WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll (Sum.inr (Sum.inl q))).run g =
      if q.1 ∉ wotsInsts vp ∨ q.1 ∈ g.map (·.1) then pure (none, g)
      else signProg startVal chainHash q.1 q.2 >>= fun r =>
        pure (some (r.1, r.2), g ++ [(q.1, q.2, r.1, r.2)]) := by
  split_ifs with h
  · simp only [WotsFinal.simImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      WotsGame.simSignOracle, StateT.run_bind, StateT.run_get, pure_bind, if_pos h,
      StateT.run_pure]
  · simp only [WotsFinal.simImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
      WotsGame.simSignOracle, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
      if_neg h, StateT.run_monadLift, monadLift_self, StateT.run_map,
      StateT.run_set, map_pure, signProg, bind_map_left, Functor.map_map, map_bind]

/-- The run of the simulator inside the SM game, as a state monad over (mirror, game state). -/
noncomputable def simRun (O₂ : QueryImpl spec (StateT Sg ProbComp))
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    {α : Type} (oa : OracleComp (WSpec prims) α) (s : List (WotsGame.Entry prims) × Sg) :
    ProbComp (α × (List (WotsGame.Entry prims) × Sg)) :=
  (fun z => (z.1.1, (z.1.2, z.2))) <$>
    (simulateQ (WotsFinal.outer O₂)
      ((simulateQ (WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll) oa).run s.1)).run s.2

theorem simRun_query (O₂ : QueryImpl spec (StateT Sg ProbComp))
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (t : (WSpec prims).Domain) (s : List (WotsGame.Entry prims) × Sg) :
    simRun O₂ startVal chainHash coll
        (liftM ((WSpec prims).query t) : OracleComp (WSpec prims) _) s =
      (fun z => (z.1.1, (z.1.2, z.2))) <$>
        (simulateQ (WotsFinal.outer O₂)
          ((WotsFinal.simImpl (wotsInsts vp) startVal chainHash coll t).run s.1)).run s.2 := by
  unfold simRun
  rw [simulateQ_spec_query]

/-- **The counting semantics of `simChoose` inside an SM game**, for a counter `n` on the game
state that grows by at most one per query satisfying `pc`. -/
noncomputable def simSem (O₂ : QueryImpl spec (StateT Sg ProbComp)) (n : Sg → ℕ)
    (pc : ℕ ⊕ ι → Prop) [DecidablePred pc]
    (hO : ∀ t σ, ∀ z ∈ support ((WotsFinal.outer O₂ t).run σ),
      n z.2 ≤ n σ + (if pc t then 1 else 0))
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) (cC K : ℕ)
    (hcoll : ∀ key xs, IsQueryBoundP (coll key xs) pc cC)
    (hsign : ∀ a m, IsQueryBoundP (signProg (vp := vp) startVal chainHash a m) pc K) :
    CSem vp prims (List (WotsGame.Entry prims) × Sg) where
  sem := simRun O₂ startVal chainHash coll
  hist s := s.1
  n s := n s.2
  cC := cC
  K := K
  sem_pure x s := by simp [simRun]
  sem_bind oa f s := by
    simp [simRun, simulateQ_bind, StateT.run_bind, map_bind, bind_map_left]
  lift my s := by
    intro z hz
    have h1 : (monadLift my : OracleComp (WSpec prims) _) = my.liftComp (WSpec prims) := rfl
    unfold simRun at hz
    rw [h1, WotsFinal.simImpl, QueryImpl.simulateQ_add_liftComp_left, simulateQ_liftTarget] at hz
    have h2 : simulateQ (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + spec))) my =
        (monadLift my : OracleComp (unifSpec + spec) _) := rfl
    rw [h2] at hz
    simp only [StateT.run_monadLift, monadLift_self, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, StateT.run_pure, WotsFinal.outer_lift, bind_map_left,
      map_bind, map_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
    obtain ⟨w, -, rfl⟩ := hz
    rfl
  coll q s := by
    intro z hz
    rw [simRun_query, simImpl_run_coll] at hz
    split_ifs at hz with h
    · simp at hz
      subst hz
      exact ⟨rfl, Nat.le_add_right _ _⟩
    · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind,
        map_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨rfl, growth_of_qb (WotsFinal.outer O₂) n pc hO _ _ (hcoll q.1 q.2) s.2 w hw⟩
  sign q s := by
    intro z hz
    rw [simRun_query, simImpl_run_sign] at hz
    split_ifs at hz with h
    · simp only [simulateQ_pure, StateT.run_pure, map_pure, support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl ⟨rfl, rfl, le_rfl, h⟩
    · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind,
        map_pure, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      rw [not_or, not_not] at h
      exact Or.inr ⟨w.1.1, w.1.2, rfl, rfl, h.1, h.2,
        growth_of_qb (WotsFinal.outer O₂) n pc hO _ _ (hsign q.1 q.2) s.2 w hw⟩

/-- **Counter growth of `simChoose (bWotsWith my A)` inside an SM game.** -/
theorem simChoose_bWotsWith_count (O₂ : QueryImpl spec (StateT Sg ProbComp)) (n : Sg → ℕ)
    (pc : ℕ ⊕ ι → Prop) [DecidablePred pc]
    (hO : ∀ t σ, ∀ z ∈ support ((WotsFinal.outer O₂ t).run σ),
      n z.2 ≤ n σ + (if pc t then 1 else 0))
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (coll : prims.AdrsKey → List prims.Y → OracleComp (unifSpec + spec) prims.Y) (cC K : ℕ)
    (hcoll : ∀ key xs, IsQueryBoundP (coll key xs) pc cC)
    (hsign : ∀ a m, IsQueryBoundP (signProg (vp := vp) startVal chainHash a m) pc K)
    (my : ProbComp (SecretTable vp prims)) (A : Forger vp prims optRand pkSeedDist) (σ : Sg) :
    ∀ z ∈ support ((simulateQ (WotsFinal.outer O₂)
        (WotsGame.simChoose (Lazy.bWotsWith my A) (wotsInsts vp) startVal chainHash coll)).run σ),
      n z.2 ≤ n σ + cC * wotsQc vp + (wotsInsts vp).length * K := by
  intro z hz
  have h := (simSem O₂ n pc hO startVal chainHash coll cC K hcoll hsign).bWotsWith_choose_count
    my A ([], σ) rfl (z.1.1, (z.1.2, z.2))
    (by
      show _ ∈ support (simRun O₂ startVal chainHash coll (Lazy.bWotsWith my A).choose ([], σ))
      unfold simRun
      rw [support_map]
      exact ⟨z, hz, rfl⟩)
  exact h

/-- Non-uniform budget for `Vector.ofFnM`. -/
theorem qb_ofFnM_sum {κ' : Type} {sp : OracleSpec κ'} (p : κ' → Prop) [DecidablePred p]
    {α : Type} {k : ℕ} (g : Fin k → OracleComp sp α) (c : Fin k → ℕ)
    (h : ∀ i, IsQueryBoundP (g i) p (c i)) : IsQueryBoundP (Vector.ofFnM g) p (∑ i, c i) := by
  induction k with
  | zero =>
    rw [Vector.ofFnM_zero]
    exact isQueryBoundP_pure _ _ _
  | succ k ih =>
    rw [Vector.ofFnM_succ, Fin.sum_univ_castSucc]
    exact Lazy.qb_bind p (ih (fun i => g i.castSucc) (fun i => c i.castSucc) fun i => h i.castSucc)
      fun xs => (Lazy.qb_bind p (m := 0) (h (Fin.last k)) fun a =>
        isQueryBoundP_pure _ _ _).mono (by omega)

/-- Budget of the simulated signing program: per chain with digit `b`, `cS b` for the revealed
value and `cH` per remaining chain step. -/
theorem signProg_qb (p : ℕ ⊕ ι → Prop) [DecidablePred p]
    (startVal : Adrs → ℕ → OracleComp (unifSpec + spec) prims.Y)
    (chainHash : Adrs → prims.Y → OracleComp (unifSpec + spec) prims.Y)
    (cS : ℕ → ℕ) (cH K0 : ℕ)
    (hstart : ∀ ca b, IsQueryBoundP (startVal ca b) p (cS b))
    (hchain : ∀ a y, IsQueryBoundP (chainHash a y) p cH)
    (hsum : ∀ b, b ≤ vp.params.w - 1 → cS b + (vp.params.w - 1 - b) * cH ≤ K0)
    (a : Adrs) (m : prims.Y) :
    IsQueryBoundP (signProg (vp := vp) startVal chainHash a m) p (vp.params.len * K0) := by
  unfold signProg wotsPkFromSigTopsWith
  refine (Lazy.qb_bind p (qb_ofFnM_sum p _ (fun i : Fin vp.params.len =>
      cS (chainStepsCore prims.core m i.val)) fun i => hstart _ _) fun sig =>
    Lazy.qb_bind p (m := 0) (qb_ofFnM_sum p _ (fun i : Fin vp.params.len =>
      (vp.params.w - 1 - chainStepsCore prims.core m i.val) * cH) fun i =>
        Lazy.qb_chain p prims.core cH hchain _ _ _ _) fun tops => isQueryBoundP_pure _ _ _).mono ?_
  rw [Nat.add_zero, ← Finset.sum_add_distrib]
  calc _ ≤ ∑ _i : Fin vp.params.len, K0 :=
        Finset.sum_le_sum fun i _ => hsum _ (chainStepsCore_le prims.core m i.val)
    _ = vp.params.len * K0 := by simp

/-- The index of a collection query in an SM game interface
`unifSpec + (challengeSpec + collectionSpec)`. -/
def isColl {A B : Type} : ℕ ⊕ (A ⊕ B) → Prop
  | Sum.inr (Sum.inr _) => True
  | _ => False

instance {A B : Type} : DecidablePred (isColl (A := A) (B := B)) := fun t =>
  match t with
  | Sum.inr (Sum.inr _) => isTrue trivial
  | Sum.inr (Sum.inl _) => isFalse id
  | Sum.inl _ => isFalse id

/-- A lifted sampling program makes no collection query. -/
theorem qb_lift_isColl {ι' : Type} {hs : OracleSpec ι'} {α : Type} (oa : ProbComp α)
    (p : ℕ ⊕ ι' → Prop) [DecidablePred p] (hp : ∀ t, p t → t.isRight = true) :
    IsQueryBoundP (liftM oa : OracleComp (unifSpec + hs) α) p 0 :=
  IsQueryBoundP.of_imp hp (isQueryBoundP_liftM_isRight oa)

end Sim

/-! ## Closed form of `wotsQc` -/

theorem forsC_eq (vp : ValidatedParams) :
    forsC vp + vp.params.k = vp.params.k * 2 ^ (vp.params.a + 1) + 1 := by
  have h := Lazy.merkleB_add 1 1 vp.params.a
  unfold forsC
  rw [pow_succ, ← Nat.mul_assoc]
  have : vp.params.k * (Lazy.merkleB 1 1 vp.params.a + 1) = vp.params.k * 2 ^ vp.params.a * 2 := by
    rw [h]; ring
  rw [Nat.mul_add] at this
  omega

theorem treeC_eq (vp : ValidatedParams) : treeC vp + 1 = 2 ^ (vp.params.hp + 1) := by
  have h := Lazy.merkleB_add 1 1 vp.params.hp
  unfold treeC
  rw [h, pow_succ]

theorem sum_flatMap_nat {β : Type} (l : List β) (f : β → List ℕ) :
    (l.flatMap f).sum = (l.map fun b => (f b).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Sums over the instances by layer. -/
theorem sum_insts_layer (vp : ValidatedParams) (g : ℕ → ℕ) :
    ((wotsInsts vp).map fun a => g a.layer).sum =
      ((List.finRange vp.params.d).map fun l =>
        2 ^ layerTreeHeight vp l.val * (2 ^ vp.params.hp * g l.val)).sum := by
  have h1 : (wotsInsts vp).map (fun a => g a.layer) =
      (allWotsInstances vp).map fun pos => g pos.layer.val := by
    simp [wotsInsts, List.map_map, Function.comp_def]
  rw [h1, allWotsInstances, allXmssTrees]
  simp only [List.map_flatMap, List.flatMap_assoc, sum_flatMap_nat, List.map_map,
    Function.comp_def, List.flatMap_map]
  refine congrArg List.sum (List.map_congr_left fun l _ => ?_)
  simp

theorem sum_finRange_ind (n : ℕ) (hn : 0 < n) (G : ℕ → ℕ) :
    ((List.finRange n).map fun l : Fin n => G l.val * (if l.val = 0 then 1 else 0)).sum = G 0 := by
  cases n with
  | zero => omega
  | succ n => simp [List.finRange_succ, Function.comp_def]

theorem sum_own_list (vp : ValidatedParams) (l : List Adrs) :
    (l.map fun a => own vp a.layer).sum +
        treeC vp * (l.map fun a => if a.layer = 0 then 1 else 0).sum =
      l.length * treeC vp + forsC vp * (l.map fun a => if a.layer = 0 then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.add_mul]
    by_cases h : a.layer = 0
    · have ho : own vp a.layer = forsC vp := by simp [own, h]
      rw [ho]
      simp only [h, if_true]
      omega
    · have ho : own vp a.layer = treeC vp := by simp [own, h]
      rw [ho]
      simp only [h, if_false]
      omega

/-- The number of bottom-layer instances is `2^h`. -/
theorem count_layer_zero (vp : ValidatedParams) :
    ((wotsInsts vp).map fun a => if a.layer = 0 then 1 else 0).sum = 2 ^ vp.params.h := by
  rw [sum_insts_layer vp fun l => if l = 0 then 1 else 0]
  have h := sum_finRange_ind vp.params.d vp.valid.d_pos
    (fun l => 2 ^ layerTreeHeight vp l * 2 ^ vp.params.hp)
  simp only [Nat.mul_assoc] at h
  rw [h, ← pow_add, vp.valid.h_eq_layers]
  congr 1
  unfold layerTreeHeight
  have := vp.valid.d_pos
  have e : vp.params.d = (vp.params.d - (0 + 1)) + 1 := by omega
  conv_rhs => rw [e, Nat.add_mul, Nat.one_mul]

/-- **Closed form of `qc`** (division- and subtraction-free):
`qc + 2^h · T = 2^h · F + (#inst + 1) · T`, i.e. `qc = 2^h · F + #trees · T` with
`F = forsC = k·(2^(a+1) - 1) + 1`, `T = treeC = 2^(h'+1) - 1`, `#trees = #inst - 2^h + 1`. -/
theorem wotsQc_closed (vp : ValidatedParams) :
    wotsQc vp + 2 ^ vp.params.h * treeC vp =
      2 ^ vp.params.h * forsC vp + ((wotsInsts vp).length + 1) * treeC vp := by
  have h := sum_own_list vp (wotsInsts vp)
  rw [count_layer_zero] at h
  have hd : own vp vp.params.d = treeC vp := by
    have := vp.valid.d_pos
    simp [own]
    omega
  unfold wotsQc
  rw [hd, Nat.add_mul, Nat.one_mul, Nat.mul_comm (2 ^ vp.params.h) (treeC vp),
    Nat.mul_comm (2 ^ vp.params.h) (forsC vp)]
  omega

theorem forsC_128s : forsC Link.vp = 114675 := by
  have h := forsC_eq Link.vp
  obtain ⟨-, -, -, -, ha, hk, -⟩ := Resources.params_128s
  rw [ha, hk] at h
  omega

theorem treeC_128s : treeC Link.vp = 1023 := by
  have h := treeC_eq Link.vp
  obtain ⟨-, -, -, hhp, -⟩ := Resources.params_128s
  rw [hhp] at h
  omega

/-- **`qc` at SLH-DSA-SHA2-128s** (`≈ 2^79.807`; `1023` less than the value argued in
`status/W3.md`, which counted the top tree twice). -/
theorem wotsQc_128s : wotsQc Link.vp = 1057708653120046860861951 := by
  have h := wotsQc_closed Link.vp
  obtain ⟨-, hh, -⟩ := Resources.params_128s
  have key : ∀ q F T N H : ℕ, q + 2 ^ H * T = 2 ^ H * F + (N + 1) * T → F = 114675 → T = 1023 →
      N = 9241421688590303744 → H = 63 → q = 1057708653120046860861951 := by
    intro q F T N H h hF hT hN hH
    subst hF hT hN hH
    norm_num at h
    omega
  exact key _ _ _ _ _ h forsC_128s treeC_128s Resources.wotsInsts_length_128s hh

end Open
end Reduction

#print axioms Reduction.Open.CSem.bWotsWith_choose_count
#print axioms Reduction.Open.simChoose_bWotsWith_count
#print axioms Reduction.Open.signProg_qb
#print axioms Reduction.Open.wotsQc_closed
#print axioms Reduction.Open.wotsQc_128s
