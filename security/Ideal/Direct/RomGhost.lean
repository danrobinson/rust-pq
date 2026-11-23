import Ideal.Direct.RomState

/-!
# The ROM-side game with ghost values (`status/DIRECT.md` §13)

The deferred game draws the whole 256-bit label of every node an honest walk reads, and keeps
the part the honest party does not see (the 16 or 2 bytes after `out16` / `dig30`, and the whole
inner digest of `H_msg` and `PRF_msg`).  The ROM-side game has no such value: the simulator draws
a fresh `u` when the forger reaches the cell.  A pointwise coupling of the two games therefore
needs the ROM side to draw these values at the honest query too, as **ghosts**.

* `romGP k`: the simulator and the honest queries over VCVio's label interface on the ghost
  graph `gG` (nodes `KG = (hashSpec Cr).Domain × Bool`, no children, point `.inr k`): an honest
  query `t` asks the oracle and **touches** the ghosts `(t, false)` (final tail) and `(t, true)`
  (inner digest); the simulator, on a fresh relevant final cell of `t`, answers
  `overlay t (O t) (ghost (t, false))`, and on a fresh inner final cell of `t` (`innQ`) the ghost
  `(t, true)`, instead of a fresh value.
* `romGE k = fuseS (romGP k) gG.eagerImpl`: touches draw (the **eager ghost game**, the game the
  coupling uses); `romGD k = fuseS (romGP k) gG.deferredImpl`: touches only recorded.
* **`romGE_le`**: the eager ghost game wins at most as often as the ROM-side game `romSt k`.
  Proof: eager ≤ deferred + `Bad` (`LDefer`), `Bad` impossible here (the public cache never holds
  a ghost point), and the deferred ghost game IS the ROM-side game: every ghost the simulator
  reads is undrawn (`GInv`: a drawn ghost has its canonical cell cached, and a key has at most one
  canonical cell along a run, `cellOf_unique`), so it is a fresh value, as `u` is.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security SignatureAlg ENNReal

set_option linter.unusedSectionVars false

namespace Ideal.Direct.Rom

open Ideal.Realize Ideal.Realize.Prf

/-! ## Canonical cells -/

/-- The simulator table. -/
abbrev Tc : Type := (hS St Blk).QueryCache

/-- `q` is the last cell of the `T`-rooted chain of the block list `bs`. -/
def IsLastC (T : Tc) (q : St × Blk) (bs : List Blk) : Prop :=
  ∃ pre : List Blk, bs = pre ++ [q.2] ∧ mdC T IV128 pre = some q.1

/-- The final cell of a query (the relevance condition of `IsRel` without the public key). -/
def CellF (T : Tc) (q : St × Blk) : (hashSpec Cr).Domain → Prop
  | .inl (.thash ps key xs) => IsThL ps T q key xs
  | .inl (.hmsg R ps pr M) => ∃ s, IsHmF T q R ps s ∧ mdC T IV128 (iblocksH R ps pr M) = some s
  | .inr ⟨k, o, M⟩ => ∃ s, mdC T IV128 [okey k] = some q.1 ∧ q.2 = oblock s ∧
      mdC T IV128 (ikey k :: iblocks o M) = some s

/-- The inner block list of a two-stage query. -/
def innBlocks : (hashSpec Cr).Domain → Option (List Blk)
  | .inl (.thash _ _ _) => none
  | .inl (.hmsg R ps pr M) => some (iblocksH R ps pr M)
  | .inr ⟨k, o, M⟩ => some (ikey k :: iblocks o M)

/-- The ghost keys: a query and a slot (`false` the final tail, `true` the inner digest). -/
abbrev KG : Type := (hashSpec Cr).Domain × Bool

/-- **The canonical cell of a ghost key.** -/
def CellOf (T : Tc) (q : St × Blk) : KG → Prop
  | (t, false) => CellF T q t
  | (t, true) => ∃ bs, innBlocks t = some bs ∧ IsLastC T q bs

/-- The cell `q` is the inner final cell of the two-stage query `t` (at the public key `pk` for
`H_msg`). -/
def IsInn (pk : PublicKeyCore Cr) (T : Tc) (q : St × Blk) : (hashSpec Cr).Domain → Prop
  | .inl (.thash _ _ _) => False
  | .inl (.hmsg R ps pr M) => ps = pk.pkSeed ∧ pr = pk.pkRoot ∧ IsLastC T q (iblocksH R ps pr M)
  | .inr ⟨k, o, M⟩ => IsLastC T q (ikey k :: iblocks o M)

open Classical in
/-- The two-stage query whose inner final cell `q` is, if any. -/
noncomputable def innQ (pk : PublicKeyCore Cr) (T : Tc) (q : St × Blk) :
    Option (hashSpec Cr).Domain :=
  if h : ∃ t, IsInn pk T q t then some (Classical.choose h) else none

theorem innQ_spec {pk : PublicKeyCore Cr} {T : Tc} {q : St × Blk} {t : (hashSpec Cr).Domain}
    (h : innQ pk T q = some t) : IsInn pk T q t := by
  unfold innQ at h
  split_ifs at h with hex
  · cases h; exact Classical.choose_spec hex

theorem cellF_of_isRel {pk : PublicKeyCore Cr} {T : Tc} {q : St × Blk} {t : (hashSpec Cr).Domain}
    (h : IsRel pk T q t) : CellF T q t := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · exact h.2.2
  · exact h.2.2
  · exact h

theorem cellOf_of_isInn {pk : PublicKeyCore Cr} {T : Tc} {q : St × Blk}
    {t : (hashSpec Cr).Domain} (h : IsInn pk T q t) : CellOf T q (t, true) := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · exact h.elim
  · exact ⟨_, rfl, h.2.2⟩
  · exact ⟨_, rfl, h⟩


/-! ## Monotonicity and uniqueness of canonical cells -/

theorem isLastC_mono {T T' : Tc} (h : CExt T T') {q : St × Blk} {bs : List Blk}
    (hq : IsLastC T q bs) : IsLastC T' q bs := by
  obtain ⟨pre, e, hm⟩ := hq
  exact ⟨pre, e, mdC_mono h _ _ _ hm⟩

theorem cellF_mono {T T' : Tc} (h : CExt T T') {q : St × Blk} {t : (hashSpec Cr).Domain}
    (hq : CellF T q t) : CellF T' q t := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · obtain ⟨pre, e, hm⟩ := hq
    exact ⟨pre, e, mdC_mono h _ _ _ hm⟩
  · obtain ⟨s, ⟨b₁, b₂, e, e2, hm⟩, hs⟩ := hq
    exact ⟨s, ⟨b₁, b₂, e, e2, mdC_mono h _ _ _ hm⟩, mdC_mono h _ _ _ hs⟩
  · obtain ⟨s, h1, h2, h3⟩ := hq
    exact ⟨s, mdC_mono h _ _ _ h1, h2, mdC_mono h _ _ _ h3⟩

theorem cellOf_mono {T T' : Tc} (h : CExt T T') {q : St × Blk} {c : KG}
    (hq : CellOf T q c) : CellOf T' q c := by
  rcases c with ⟨t, _ | _⟩
  · exact cellF_mono h hq
  · obtain ⟨bs, e, hl⟩ := hq
    exact ⟨bs, e, isLastC_mono h hl⟩

theorem append_singleton_inj {α : Type} {l l' : List α} {a a' : α} (h : l ++ [a] = l' ++ [a']) :
    l = l' ∧ a = a' := by
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨h1, List.singleton_inj.1 h2⟩

theorem isLastC_unique {T T' : Tc} (h : CExt T T') {q q' : St × Blk} {bs : List Blk}
    (hq : IsLastC T q bs) (hq' : IsLastC T' q' bs) : q = q' := by
  obtain ⟨pre, e, hm⟩ := hq
  obtain ⟨pre', e', hm'⟩ := hq'
  obtain ⟨rfl, h2⟩ := append_singleton_inj (e.symm.trans e')
  have := (mdC_mono h _ _ _ hm).symm.trans hm'
  exact Prod.ext (Option.some_inj.1 this) h2

theorem cellF_unique {T T' : Tc} (h : CExt T T') {q q' : St × Blk} {t : (hashSpec Cr).Domain}
    (hq : CellF T q t) (hq' : CellF T' q' t) : q = q' := by
  rcases t with (⟨ps, key, xs⟩ | ⟨R, ps, pr, M⟩) | ⟨k, o, M⟩
  · obtain ⟨pre, e, hm⟩ := hq
    obtain ⟨pre', e', hm'⟩ := hq'
    obtain ⟨rfl, h2⟩ := append_singleton_inj (e.symm.trans e')
    have := (mdC_mono h _ _ _ hm).symm.trans hm'
    exact Prod.ext (Option.some_inj.1 this) h2
  · obtain ⟨s, ⟨b₁, b₂, e, e2, hm⟩, hs⟩ := hq
    obtain ⟨s', ⟨b₁', b₂', e', e2', hm'⟩, hs'⟩ := hq'
    obtain rfl : s = s' := Option.some_inj.1 ((mdC_mono h _ _ _ hs).symm.trans hs')
    have hb := e.symm.trans e'
    simp only [List.cons.injEq, and_true] at hb
    obtain ⟨rfl, rfl⟩ := hb
    exact Prod.ext (Option.some_inj.1 ((mdC_mono h _ _ _ hm).symm.trans hm')) (e2.trans e2'.symm)
  · obtain ⟨s, h1, h2, h3⟩ := hq
    obtain ⟨s', h1', h2', h3'⟩ := hq'
    obtain rfl : s = s' := Option.some_inj.1 ((mdC_mono h _ _ _ h3).symm.trans h3')
    exact Prod.ext (Option.some_inj.1 ((mdC_mono h _ _ _ h1).symm.trans h1')) (h2.trans h2'.symm)

/-- **A ghost key has at most one canonical cell along a run** (the table only grows). -/
theorem cellOf_unique {T T' : Tc} (h : CExt T T') {q q' : St × Blk} {c : KG}
    (hq : CellOf T q c) (hq' : CellOf T' q' c) : q = q' := by
  rcases c with ⟨t, _ | _⟩
  · exact cellF_unique h hq hq'
  · obtain ⟨bs, e, hl⟩ := hq
    obtain ⟨bs', e', hl'⟩ := hq'
    obtain rfl : bs = bs' := Option.some_inj.1 (e.symm.trans e')
    exact isLastC_unique h hl hl'

theorem cExt_refl (T : Tc) : CExt T T := fun _ _ h => h

theorem cExt_cacheQuery {T : Tc} {q : St × Blk} (hq : T q = none) (v : St) :
    CExt T (T.cacheQuery q v) := by
  intro q' v' h
  by_cases e : q' = q
  · subst e; rw [hq] at h; cases h
  · rw [QueryCache.cacheQuery_of_ne _ _ e]; exact h


/-! ## The ghost graph and the ghost program -/

/-- The public interface of the ghost game: the hash oracles and (unused) ghost points. -/
abbrev PubG := hashSpec Cr + (KG →ₒ St)

instance instSampPubG : ∀ t : PubG.Domain, SampleableType (PubG.Range t)
  | .inl t => inferInstanceAs (SampleableType ((hashSpec Cr).Range t))
  | .inr _ => inferInstanceAs (SampleableType St)

/-- **The ghost graph**: childless nodes `KG`, the point of `k` is `.inr k`. -/
def gG : LGraph PubG Empty KG St where
  ch _ := []
  pt k _ := .inr k
  range_eq _ _ := rfl
  root_inj := by
    intro k k' _ _ h
    exact Sum.inr_injective h

/-- The ghost game's program interface. -/
abbrev WG := PubG.withLabels Empty KG St

/-- A coin of the ghost interface. -/
def coinG (n : ℕ) : OracleComp WG (Fin (n + 1)) :=
  (liftM (WG.query (.inl (.inl (.inl n)))) : OracleComp WG _)

/-- A fresh 256-bit value by the coins. -/
noncomputable def freshG : OracleComp WG St := simulateQ coinG ($ᵗ St : ProbComp St)

/-- An oracle query. -/
def oG (t : (hashSpec Cr).Domain) : OracleComp WG ((hashSpec Cr).Range t) :=
  (liftM (WG.query (.inl (.inl (.inr (.inl t))))) : OracleComp WG _)

/-- A ghost touch. -/
def tG (c : KG) : OracleComp WG Unit := (liftM (WG.query (.inr (.inl (.inr c)))) : OracleComp WG _)

/-- A ghost read. -/
def rG (c : KG) : OracleComp WG St := (liftM (WG.query (.inr (.inr c)))) 

/-- **An honest query**: the oracle, and a touch of both ghosts. -/
def honG (t : (hashSpec Cr).Domain) : OracleComp WG ((hashSpec Cr).Range t) := do
  let y ← oG t
  tG (t, false)
  tG (t, true)
  pure y

/-- **The simulator's step with ghosts.** -/
noncomputable def simStepG (pk : PublicKeyCore Cr) (q : St × Blk) :
    StateT Tc (OracleComp WG) St := fun T =>
  match T q with
  | some v => pure (v, T)
  | none =>
    match relQ pk T q with
    | some t => do
      let y ← oG t
      let g ← rG (t, false)
      pure (overlay t y g, T.cacheQuery q (overlay t y g))
    | none =>
      match innQ pk T q with
      | some t => do
        let g ← rG (t, true)
        pure (g, T.cacheQuery q g)
      | none => do
        let u ← freshG
        pure (u, T.cacheQuery q u)

/-- Lift a ghost-interface computation, the table unchanged. -/
def liftT {α : Type} (oa : OracleComp WG α) : StateT Tc (OracleComp WG) α :=
  StateT.mk fun T => (fun a => (a, T)) <$> oa

/-- **The ghost program of the tagged interface at the secret seed `k`.** -/
noncomputable def romGP (k : Bytes 16) : QueryImpl (QT Dsk) (StateT Tc (OracleComp WG))
  | .inl n => liftT (coinG n)
  | .inr (.inl (.inl pq)) => simStepG pq.1 pq.2
  | .inr (.inl (.inr d)) => liftT (honG (.inl
      (PublicHashQuery.thash d.1 (Cr.adrsToKey d.2.1) [k])))
  | .inr (.inr (.inl q)) => liftT (honG (.inl q))
  | .inr (.inr (.inr t)) => liftT (honG (.inr ⟨t.1, t.2.1, t.2.2⟩))

/-- The ghost relabel state. -/
abbrev GS : Type := RelabelState PubG Empty KG St

/-- **The eager ghost game** (touches draw). -/
noncomputable def romGE (k : Bytes 16) : QueryImpl (QT Dsk) (StateT (Tc × GS) ProbComp) :=
  fuseS (romGP k) gG.eagerImpl

/-- The deferred ghost game (touches recorded). -/
noncomputable def romGD (k : Bytes 16) :
    QueryImpl (QT Dsk) (StateT (Tc × (GS × List (Empty ⊕ KG))) ProbComp) :=
  fuseS (romGP k) gG.deferredImpl


/-! ## Run equations of the deferred ghost game -/

/-- The deferred ghost state. -/
abbrev GDS : Type := GS × List (Empty ⊕ KG)

theorem gG_no_pt (t : (hashSpec Cr).Domain) (st : GS) :
    ¬∃ k vs, gG.childVals st k = some vs ∧ gG.pt k vs = .inl t := by
  rintro ⟨k, vs, -, h⟩
  cases h

theorem dG_coin (n : ℕ) (s : GDS) :
    (simulateQ gG.deferredImpl (coinG n)).run s =
      (fun u => (u, s)) <$> (unifSpec.query n : ProbComp _) := by
  unfold coinG
  rw [simulateQ_spec_query, LGraph.deferredImpl_run_inl, LGraph.relabelImpl_run_unif,
    Functor.map_map]

theorem dG_fresh (s : GDS) :
    (simulateQ gG.deferredImpl freshG).run s = (fun u => (u, s)) <$> ($ᵗ St : ProbComp St) := by
  unfold freshG
  rw [← QueryImpl.simulateQ_compose]
  refine (run_simulateQ_statelessP _ (fun n => (liftM (unifSpec.query n) : ProbComp _))
    (fun n s' => ?_) _ s).trans ?_
  · simp only [QueryImpl.apply_compose]
    exact dG_coin n s'
  · rw [simulateQ_unif_id]

theorem dG_o (t : (hashSpec Cr).Domain) (s : GDS) :
    (simulateQ gG.deferredImpl (oG t)).run s =
      (fun z => (z.1, ((z.2, s.1.2), s.2))) <$> (PubG.randomOracle (.inl t)).run s.1.1 := by
  unfold oG
  rw [simulateQ_spec_query, LGraph.deferredImpl_run_inl,
    LGraph.relabelImpl_run_pub_of_not_exists _ (gG_no_pt t s.1), Functor.map_map]

theorem dG_t (c : KG) (s : GDS) :
    (simulateQ gG.deferredImpl (tG c)).run s = pure ((), (s.1, s.2 ++ [.inr c])) := by
  unfold tG
  rw [simulateQ_spec_query, LGraph.deferredImpl_run_touch]

theorem dG_r (c : KG) (s : GDS) :
    (simulateQ gG.deferredImpl (rG c)).run s =
      (fun z => (z.1, (z.2, s.2))) <$> (RelabelState.drawCell (.inr c)).run s.1 := by
  unfold rG
  rw [simulateQ_spec_query, LGraph.deferredImpl_run_read]

theorem dG_hon (t : (hashSpec Cr).Domain) (s : GDS) :
    (simulateQ gG.deferredImpl (honG t)).run s =
      (fun z => (z.1, ((z.2, s.1.2), s.2 ++ [.inr (t, false)] ++ [.inr (t, true)]))) <$>
        (PubG.randomOracle (.inl t)).run s.1.1 := by
  unfold honG
  simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, dG_o, dG_t,
    pure_bind, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc]
  rfl

/-! ## The ghost interface's hash oracle is the ROM's -/

/-- The hash part of the ghost public cache. -/
def oP (C : PubG.QueryCache) : (hashSpec Cr).QueryCache := QueryCache.ofFn fun t => C (.inl t)

theorem oP_cacheQuery (C : PubG.QueryCache) (t : (hashSpec Cr).Domain) (u : (hashSpec Cr).Range t) :
    oP (C.cacheQuery (.inl t) u) = (oP C).cacheQuery t u := by
  ext t' : 1
  by_cases h : t' = t
  · subst h
    simp only [oP, QueryCache.ofFn_apply, QueryCache.cacheQuery_self]
  · rw [QueryCache.cacheQuery_of_ne _ _ h]
    simp only [oP, QueryCache.ofFn_apply]
    exact QueryCache.cacheQuery_of_ne _ _ (fun e => h (Sum.inl_injective e))

theorem oP_cacheQuery_inr (C : PubG.QueryCache) (c : KG) (u : St) :
    oP (C.cacheQuery (.inr c) u) = oP C := by
  ext t' : 1
  simp only [oP, QueryCache.ofFn_apply]
  exact QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem ro_inl (t : (hashSpec Cr).Domain) (C : PubG.QueryCache) :
    (fun z => (z.1, oP z.2)) <$> (PubG.randomOracle (.inl t)).run C =
      ((hashSpec Cr).randomOracle t).run (oP C) := by
  rw [randomOracle.run_eq, randomOracle.run_eq]
  have e : (oP C) t = C (.inl t) := rfl
  rw [e]
  cases C (.inl t) with
  | some u => simp
  | none =>
    simp only [map_bind, map_pure, oP_cacheQuery]
    rfl


/-! ## Run equations of the ROM side -/

theorem rS_coin (n : ℕ) (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl (rq (.inl n))).run O =
      (fun u => (u, O)) <$> (unifSpec.query n : ProbComp _) := by
  unfold rq
  rw [simulateQ_spec_query]
  rfl

theorem rS_o (t : (hashSpec Cr).Domain) (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl (rq (.inr t))).run O =
      ((hashSpec Cr).randomOracle t).run O := by
  unfold rq
  rw [simulateQ_spec_query]
  rfl

theorem rS_fresh (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl freshR).run O = (fun u => (u, O)) <$> ($ᵗ St : ProbComp St) :=
  roSim.run_liftM _ _ O

/-! ## The invariant of the deferred ghost game -/

/-- **The invariant**: the public cache holds no ghost point, and a drawn ghost has its canonical
cell cached in the simulator table. -/
def GInv (s : Tc × GDS) : Prop :=
  (∀ c : KG, s.2.1.1 (.inr c) = none) ∧
    ∀ c : KG, s.2.1.2 (.inr c) ≠ none → ∃ q, CellOf s.1 q c ∧ s.1 q ≠ none

theorem ginv_init : GInv ((∅ : Tc), (((∅, ∅) : GS), ([] : List (Empty ⊕ KG)))) :=
  ⟨fun _ => rfl, fun _ h => absurd rfl h⟩

/-- Under the invariant, the ghost of a fresh canonical cell is undrawn. -/
theorem ginv_undrawn {s : Tc × GDS} (hs : GInv s) {q : St × Blk} (hq : s.1 q = none) {c : KG}
    (hc : CellOf s.1 q c) : s.2.1.2 (.inr c) = none := by
  by_contra h
  obtain ⟨q', hc', hq'⟩ := hs.2 c h
  obtain rfl := cellOf_unique (cExt_refl _) hc hc'
  exact hq' hq

/-- The projection of the deferred ghost state to the ROM-side state. -/
def prj (s : Tc × GDS) : RomSt := (s.1, oP s.2.1.1)


/-! ## The port step, both sides -/

section Port

variable (pk : PublicKeyCore Cr) (q : St × Blk) (T : Tc)

theorem gd_port_some {v : St} (hq : T q = some v) (s2 : GDS) :
    (simulateQ gG.deferredImpl ((simStepG pk q).run T)).run s2 = pure ((v, T), s2) := by
  show (simulateQ gG.deferredImpl (simStepG pk q T)).run s2 = _
  unfold simStepG
  simp only [hq, simulateQ_pure, StateT.run_pure]

theorem gd_port_rel (hq : T q = none) {t : (hashSpec Cr).Domain} (ht : relQ pk T q = some t)
    (s2 : GDS) (hL : s2.1.2 (.inr (t, false)) = none) :
    (simulateQ gG.deferredImpl ((simStepG pk q).run T)).run s2 =
      (PubG.randomOracle (.inl t)).run s2.1.1 >>= fun z => ($ᵗ St : ProbComp St) >>= fun g =>
        pure ((overlay t z.1 g, T.cacheQuery q (overlay t z.1 g)),
          ((z.2, s2.1.2.cacheQuery (.inr (t, false)) g), s2.2)) := by
  show (simulateQ gG.deferredImpl (simStepG pk q T)).run s2 = _
  unfold simStepG
  simp only [hq, ht, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, dG_o,
    bind_map_left, dG_r]
  refine bind_congr fun z => ?_
  rw [RelabelState.drawCell_run_of_cell_eq_none (st := (z.2, s2.1.2)) hL]
  simp only [bind_map_left]

theorem gd_port_inn (hq : T q = none) (ht : relQ pk T q = none) {t : (hashSpec Cr).Domain}
    (hi : innQ pk T q = some t) (s2 : GDS) (hL : s2.1.2 (.inr (t, true)) = none) :
    (simulateQ gG.deferredImpl ((simStepG pk q).run T)).run s2 =
      ($ᵗ St : ProbComp St) >>= fun g =>
        pure ((g, T.cacheQuery q g), ((s2.1.1, s2.1.2.cacheQuery (.inr (t, true)) g), s2.2)) := by
  show (simulateQ gG.deferredImpl (simStepG pk q T)).run s2 = _
  unfold simStepG
  simp only [hq, ht, hi, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    dG_r, RelabelState.drawCell_run_of_cell_eq_none hL, bind_map_left]

theorem gd_port_fresh (hq : T q = none) (ht : relQ pk T q = none) (hi : innQ pk T q = none)
    (s2 : GDS) :
    (simulateQ gG.deferredImpl ((simStepG pk q).run T)).run s2 =
      ($ᵗ St : ProbComp St) >>= fun u => pure ((u, T.cacheQuery q u), s2) := by
  show (simulateQ gG.deferredImpl (simStepG pk q T)).run s2 = _
  unfold simStepG
  simp only [hq, ht, hi, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    dG_fresh, bind_map_left]

theorem rs_port_some {v : St} (hq : T q = some v) (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl ((simStepR pk q).run T)).run O = pure ((v, T), O) := by
  show (simulateQ (hashSpec Cr).romImpl (simStepR pk q T)).run O = _
  unfold simStepR
  simp only [hq, simulateQ_pure, StateT.run_pure]

theorem rs_port_rel (hq : T q = none) {t : (hashSpec Cr).Domain} (ht : relQ pk T q = some t)
    (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl ((simStepR pk q).run T)).run O =
      ($ᵗ St : ProbComp St) >>= fun u => ((hashSpec Cr).randomOracle t).run O >>= fun z =>
        pure ((overlay t z.1 u, T.cacheQuery q (overlay t z.1 u)), z.2) := by
  show (simulateQ (hashSpec Cr).romImpl (simStepR pk q T)).run O = _
  unfold simStepR
  simp only [hq, ht, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, rS_fresh,
    bind_map_left, rS_o]
  rfl

theorem rs_port_fresh (hq : T q = none) (ht : relQ pk T q = none) (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl ((simStepR pk q).run T)).run O =
      ($ᵗ St : ProbComp St) >>= fun u => pure ((u, T.cacheQuery q u), O) := by
  show (simulateQ (hashSpec Cr).romImpl (simStepR pk q T)).run O = _
  unfold simStepR
  simp only [hq, ht, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, rS_fresh,
    bind_map_left]

end Port


/-! ## The deferred ghost game steps as the ROM-side game -/

theorem liftT_run {α : Type} (oa : OracleComp WG α) (T : Tc) :
    (liftT oa).run T = (fun a => (a, T)) <$> oa := rfl

theorem gd_hon_run (t : (hashSpec Cr).Domain) (T : Tc) (s2 : GDS) :
    (simulateQ gG.deferredImpl ((liftT (honG t)).run T)).run s2 =
      (fun z => ((z.1, T), ((z.2, s2.1.2), s2.2 ++ [.inr (t, false)] ++ [.inr (t, true)]))) <$>
        (PubG.randomOracle (.inl t)).run s2.1.1 := by
  rw [liftT_run, simulateQ_map, StateT.run_map, dG_hon, Functor.map_map]

theorem rs_hon_run (t : (hashSpec Cr).Domain) (T : Tc) (O : (hashSpec Cr).QueryCache) :
    (simulateQ (hashSpec Cr).romImpl
        ((monadLift (rq (.inr t)) : StateT Tc (OracleComp RS) _).run T)).run O =
      (fun z => ((z.1, T), z.2)) <$> ((hashSpec Cr).randomOracle t).run O := by
  rw [StateT.run_monadLift, simulateQ_bind, StateT.run_bind]
  simp only [monadLift_self, rS_o, simulateQ_pure, StateT.run_pure, map_eq_bind_pure_comp]
  rfl

theorem step_hon (t : (hashSpec Cr).Domain) (s : Tc × GDS) :
    (fun z => (z.1, prj z.2)) <$>
        ((fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ gG.deferredImpl ((liftT (honG t)).run s.1)).run s.2) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (hashSpec Cr).romImpl
        ((monadLift (rq (.inr t)) : StateT Tc (OracleComp RS) _).run s.1)).run (prj s).2 := by
  rw [gd_hon_run, rs_hon_run]
  have e : (prj s).2 = oP s.2.1.1 := rfl
  rw [e, ← ro_inl]
  simp only [Functor.map_map]
  rfl

theorem step_coin (n : ℕ) (s : Tc × GDS) :
    (fun z => (z.1, prj z.2)) <$>
        ((fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ gG.deferredImpl ((liftT (coinG n)).run s.1)).run s.2) =
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (hashSpec Cr).romImpl
        ((monadLift (rq (.inl n)) : StateT Tc (OracleComp RS) _).run s.1)).run (prj s).2 := by
  rw [liftT_run, simulateQ_map, StateT.run_map, dG_coin, StateT.run_monadLift, simulateQ_bind,
    StateT.run_bind]
  simp only [monadLift_self, rS_coin, simulateQ_pure, StateT.run_pure, Functor.map_map,
    bind_map_left]
  simp only [map_eq_bind_pure_comp]
  rfl

theorem step_port (pk : PublicKeyCore Cr) (q : St × Blk) (s : Tc × GDS) (hs : GInv s) :
    (fun z => (z.1, prj z.2)) <$>
        ((fun z => (z.1.1, (z.1.2, z.2))) <$>
          (simulateQ gG.deferredImpl ((simStepG pk q).run s.1)).run s.2) =ᵈ
      (fun z => (z.1.1, (z.1.2, z.2))) <$> (simulateQ (hashSpec Cr).romImpl
        ((simStepR pk q).run s.1)).run (prj s).2 := by
  obtain ⟨T, s2⟩ := s
  rcases hq : T q with _ | v
  · rcases ht : relQ pk T q with _ | t
    · rw [rs_port_fresh pk q T hq ht]
      rcases hi : innQ pk T q with _ | t
      · rw [gd_port_fresh pk q T hq ht hi]
        simp only [map_bind, map_pure]
        exact EvalDistEq.refl _
      · rw [gd_port_inn pk q T hq ht hi s2 (ginv_undrawn hs hq (cellOf_of_isInn (innQ_spec hi)))]
        simp only [map_bind, map_pure]
        exact EvalDistEq.refl _
    · rw [rs_port_rel pk q T hq ht, gd_port_rel pk q T hq ht s2
        (ginv_undrawn hs hq (cellF_of_isRel (relQ_spec ht)))]
      have e : (prj (T, s2)).2 = oP s2.1.1 := rfl
      rw [e, ← ro_inl]
      simp only [map_bind, map_pure, bind_map_left]
      exact (OracleComp.EvalDistEq.bind_bind_swap _ _ _).symm
  · rw [gd_port_some pk q T hq, rs_port_some pk q T hq]
    simp only [map_pure]
    exact EvalDistEq.refl _


/-! ## The invariant is preserved -/

theorem ro_inl_keep (t : (hashSpec Cr).Domain) (C : PubG.QueryCache) :
    ∀ z ∈ support ((PubG.randomOracle (.inl t)).run C), ∀ c : KG, z.2 (.inr c) = C (.inr c) := by
  intro z hz c
  rw [randomOracle.run_eq] at hz
  cases h : C (.inl t) with
  | some u =>
    rw [h, support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
  | none =>
    rw [h, mem_support_bind_iff] at hz
    obtain ⟨u, -, hz⟩ := hz
    rw [support_pure, Set.mem_singleton_iff] at hz
    rw [hz]
    exact QueryCache.cacheQuery_of_ne _ _ (by simp)

theorem ginv_hon {T : Tc} {C C' : PubG.QueryCache} {L : ((Empty ⊕ KG) →ₒ St).QueryCache}
    {p p' : List (Empty ⊕ KG)} (hs : GInv (T, ((C, L), p))) (hC : ∀ c : KG, C' (.inr c) = C (.inr c)) :
    GInv (T, ((C', L), p')) :=
  ⟨fun c => (hC c).trans (hs.1 c), hs.2⟩

theorem ginv_cache_plain {T : Tc} {q : St × Blk} (hq : T q = none) (v : St) {C : PubG.QueryCache}
    {L : ((Empty ⊕ KG) →ₒ St).QueryCache} {p : List (Empty ⊕ KG)} (hs : GInv (T, ((C, L), p))) :
    GInv (T.cacheQuery q v, ((C, L), p)) := by
  refine ⟨hs.1, fun c hc => ?_⟩
  obtain ⟨q', h1, h2⟩ := hs.2 c hc
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h2
  exact ⟨q', cellOf_mono (cExt_cacheQuery hq v) h1, by
    rw [cExt_cacheQuery hq v _ _ hw]; simp⟩

theorem ginv_cache {T : Tc} {q : St × Blk} (hq : T q = none) {c₀ : KG} (hc₀ : CellOf T q c₀)
    {C C' : PubG.QueryCache} {L : ((Empty ⊕ KG) →ₒ St).QueryCache} {p : List (Empty ⊕ KG)}
    (hs : GInv (T, ((C, L), p))) (hC : ∀ c : KG, C' (.inr c) = C (.inr c)) (v g : St) :
    GInv (T.cacheQuery q v, ((C', L.cacheQuery (.inr c₀) g), p)) := by
  refine ⟨fun c => (hC c).trans (hs.1 c), fun c hc => ?_⟩
  by_cases e : c = c₀
  · subst e
    exact ⟨q, cellOf_mono (cExt_cacheQuery hq v) hc₀, by simp⟩
  · have hL : (L.cacheQuery (.inr c₀) g) (.inr c) = L (.inr c) :=
      QueryCache.cacheQuery_of_ne _ _ (fun h => e (Sum.inr_injective h))
    rw [hL] at hc
    exact (ginv_cache_plain hq v hs).2 c hc

theorem romGD_preservesInv (k : Bytes 16) : QueryImpl.PreservesInv (romGD k) GInv := by
  intro t s hs z hz
  obtain ⟨T, ⟨⟨C, L⟩, p⟩⟩ := s
  unfold romGD at hz
  rw [fuseS_run, support_map] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  rcases t with n | (pq | d) | (q | tq)
  · simp only [romGP] at hw
    rw [liftT_run, simulateQ_map, StateT.run_map, dG_coin, Functor.map_map, support_map] at hw
    obtain ⟨u, -, rfl⟩ := hw
    exact hs
  · obtain ⟨pk, q⟩ := pq
    simp only [romGP] at hw
    rcases hq : T q with _ | v
    · rcases ht : relQ pk T q with _ | t
      · rcases hi : innQ pk T q with _ | t
        · rw [gd_port_fresh pk q T hq ht hi, mem_support_bind_iff] at hw
          obtain ⟨u, -, hw⟩ := hw
          rw [support_pure, Set.mem_singleton_iff] at hw
          subst hw
          exact ginv_cache_plain hq u hs
        · have hc := cellOf_of_isInn (innQ_spec hi)
          rw [gd_port_inn pk q T hq ht hi _ (ginv_undrawn hs hq hc), mem_support_bind_iff] at hw
          obtain ⟨g, -, hw⟩ := hw
          rw [support_pure, Set.mem_singleton_iff] at hw
          subst hw
          exact ginv_cache hq hc hs (fun _ => rfl) g g
      · have hc : CellOf T q (t, false) := cellF_of_isRel (relQ_spec ht)
        rw [gd_port_rel pk q T hq ht _ (ginv_undrawn hs hq hc), mem_support_bind_iff] at hw
        obtain ⟨z0, hz0, hw⟩ := hw
        rw [mem_support_bind_iff] at hw
        obtain ⟨g, -, hw⟩ := hw
        rw [support_pure, Set.mem_singleton_iff] at hw
        subst hw
        exact ginv_cache hq hc hs (ro_inl_keep t C z0 hz0) _ g
    · rw [gd_port_some pk q T hq, support_pure, Set.mem_singleton_iff] at hw
      subst hw
      exact hs
  · simp only [romGP] at hw
    erw [gd_hon_run, support_map] at hw
    obtain ⟨z0, hz0, rfl⟩ := hw
    exact ginv_hon hs (ro_inl_keep _ C z0 hz0)
  · simp only [romGP] at hw
    erw [gd_hon_run, support_map] at hw
    obtain ⟨z0, hz0, rfl⟩ := hw
    exact ginv_hon hs (ro_inl_keep _ C z0 hz0)
  · simp only [romGP] at hw
    erw [gd_hon_run, support_map] at hw
    obtain ⟨z0, hz0, rfl⟩ := hw
    exact ginv_hon hs (ro_inl_keep _ C z0 hz0)


theorem eqD_of_eq {α : Type} {mx my : ProbComp α} (h : mx = my) : mx =ᵈ my :=
  h ▸ EvalDistEq.refl _

/-- **One step of the deferred ghost game is one step of the ROM-side game** (in distribution,
after the projection, under the invariant). -/
theorem romGD_step (k : Bytes 16) (t : (QT Dsk).Domain) (s : Tc × GDS) (hs : GInv s) :
    (fun z => (z.1, prj z.2)) <$> (romGD k t).run s =ᵈ (romSt k t).run (prj s) := by
  unfold romGD romSt
  rw [fuseS_run, fuseS_run]
  rcases t with n | (pq | d) | (q | tq)
  · exact eqD_of_eq (step_coin n s)
  · exact step_port pq.1 pq.2 s hs
  · exact eqD_of_eq (step_hon (.inl (PublicHashQuery.thash d.1 (Cr.adrsToKey d.2.1) [k])) s)
  · exact eqD_of_eq (step_hon (.inl q) s)
  · exact eqD_of_eq (step_hon (.inr ⟨tq.1, tq.2.1, tq.2.2⟩) s)

theorem romGD_dom (k : Bytes 16) :
    QueryImpl.DominatedUntilBad (romGD k) (romSt k) prj GInv (fun _ => False) :=
  QueryImpl.DominatedUntilBad.of_evalDistEq_or_bad fun t s hs _ => Or.inl (romGD_step k t s hs)

/-- **The deferred ghost game wins at most as often as the ROM-side game.** -/
theorem romGD_le (k : Bytes 16) (P : OracleComp (QT Dsk) Bool) :
    Pr{let z ← (simulateQ (romGD k) P).run ((∅ : Tc), (((∅, ∅) : GS), []))}[z.1 = true] ≤
      Pr{let z ← (simulateQ (romSt k) P).run ((∅ : Tc), (∅ : (hashSpec Cr).QueryCache))}[
        z.1 = true] := by
  have h := (romGD_dom k).prEvent_simulateQ_run_map_and_not_bad_le (romGD_preservesInv k)
    (fun _ _ h _ _ => h) P _ ginv_init (fun z => z.1 = true)
  have e : prj ((∅ : Tc), (((∅, ∅) : GS), ([] : List (Empty ⊕ KG)))) =
      ((∅ : Tc), (∅ : (hashSpec Cr).QueryCache)) := rfl
  rw [e] at h
  refine le_trans (le_of_eq ?_) h
  exact prEvent_congr _ _ _ fun z => by simp


/-! ## Eager ghosts -/

theorem prEvent_bind_drop {α β : Type} (A : ProbComp α) (f : α → ProbComp β) (Q : α → β → Prop)
    (E : α → Prop) (h : ∀ a ∈ support A, ∀ b ∈ support (f a), Q a b → E a) :
    Pr{let a ← A; let b ← f a}[Q a b] ≤ Pr{let a ← A}[E a] := by
  set D : ProbComp (α × β) := A >>= fun a => (fun b => (a, b)) <$> f a with hD
  have c1 : Pr{let a ← A; let b ← f a}[Q a b] = Pr{let w ← D}[Q w.1 w.2] := by
    rw [hD]; simp only [prEvent_norm]
  have c2 : Pr{let w ← D}[E w.1] = Pr{let a ← A}[E a] := by
    rw [← prEvent_map D Prod.fst E]
    have e : Prod.fst <$> D = A >>= fun a => (fun _ => a) <$> f a := by
      rw [hD, map_bind]; simp only [Functor.map_map]
    rw [e]
    conv_rhs => rw [← bind_pure A]
    refine MD.prEvent_bind_congr_supp _ _ _ _ _ fun a _ => ?_
    rw [prEvent_map]
    show prEvent ((fun _ => E a) <$> f a) = prEvent ((fun y => E y) <$> (pure a : ProbComp α))
    rw [map_pure, map_eq_bind_pure_comp]
    exact prEvent_bind_const _ _
  rw [c1, ← c2]
  refine prEvent_mono_of_support _ _ _ fun w hw hq => ?_
  rw [hD, mem_support_bind_iff] at hw
  obtain ⟨a, ha, hw⟩ := hw
  rw [support_map] at hw
  obtain ⟨b, hb, rfl⟩ := hw
  exact h a ha b hb hq


theorem gG_not_bad {st : GS} (h : ∀ c : KG, st.1 (.inr c) = none) : ¬ gG.Bad st := by
  rintro (⟨k, vs, -, hc⟩ | ⟨k, k', vs, vs', -, -, hpt, hne⟩)
  · have : st.1 (.inr k) = none := h k
    simp only [gG] at hc
    rw [this] at hc
    exact absurd hc (by simp)
  · exact hne (Sum.inr_injective hpt)

/-- **The eager ghost game wins at most as often as the deferred ghost game.** -/
theorem romGE_le_romGD (k : Bytes 16) (P : OracleComp (QT Dsk) Bool) :
    Pr{let z ← (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] ≤
      Pr{let z ← (simulateQ (romGD k) P).run ((∅ : Tc), (((∅, ∅) : GS), []))}[z.1 = true] := by
  set oa := (simulateQ (romGP k) P).run (∅ : Tc)
  have hE : Pr{let z ← (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] =
      Pr{let z ← (simulateQ gG.eagerImpl oa).run (∅, ∅)}[z.1.1 = true] := by
    rw [run_fuseS, prEvent_map]; rfl
  have hD : Pr{let z ← (simulateQ (romGD k) P).run ((∅ : Tc), (((∅, ∅) : GS), []))}[z.1 = true] =
      Pr{let z ← (simulateQ gG.deferredImpl oa).run ((∅, ∅), [])}[z.1.1 = true] := by
    rw [run_fuseS, prEvent_map]; rfl
  rw [hE, hD]
  refine (gG.prEvent_eagerImpl_le_deferredImpl_empty oa (fun z => z.1.1 = true)).trans ?_
  refine prEvent_bind_drop _ _ _ _ fun z hz st hst h => ?_
  rcases h with h | h
  · exact h
  · exfalso
    have hz' : z ∈ support ((fun w => ((w.1, w.2.1), w.2.2)) <$>
        (simulateQ (romGD k) P).run ((∅ : Tc), (((∅, ∅) : GS), []))) := by
      unfold romGD; rw [← run_fuseS]; exact hz
    rw [support_map] at hz'
    obtain ⟨w, hw, rfl⟩ := hz'
    have hinv := simulateQ_run_preservesInv _ _ (romGD_preservesInv k) P _ ginv_init w hw
    refine gG_not_bad (fun c => ?_) h
    rw [RelabelState.fst_eq_of_mem_support_endFill hst]
    exact hinv.1 c

/-- **The eager ghost game wins at most as often as the ROM-side game.** -/
theorem romGE_le (k : Bytes 16) (P : OracleComp (QT Dsk) Bool) :
    Pr{let z ← (simulateQ (romGE k) P).run ((∅ : Tc), ((∅, ∅) : GS))}[z.1 = true] ≤
      Pr{let z ← (simulateQ (romSt k) P).run ((∅ : Tc), (∅ : (hashSpec Cr).QueryCache))}[
        z.1 = true] :=
  (romGE_le_romGD k P).trans (romGD_le k P)

end Ideal.Direct.Rom

#print axioms Ideal.Direct.Rom.cellOf_unique
#print axioms Ideal.Direct.Rom.romGD_step
#print axioms Ideal.Direct.Rom.romGD_preservesInv
#print axioms Ideal.Direct.Rom.romGD_le
#print axioms Ideal.Direct.Rom.romGE_le_romGD
#print axioms Ideal.Direct.Rom.romGE_le
