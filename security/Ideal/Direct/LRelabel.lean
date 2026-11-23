import VCVio.OracleComp.QueryTracking.RandomOracle.Relabel

/-!
# Relabelling a lazy random oracle along a graph with non-injective points

A copy of VCVio's `CanonicalGraph` relabelling
(`VCVio/OracleComp/QueryTracking/RandomOracle/Relabel.lean`, Apache 2.0, A. Hicks), generalised
for Merkle–Damgård (`status/DIRECT.md` §10.5, item 2).  VCVio's `CanonicalGraph` asks that
distinct nodes, or one node at distinct children values, have distinct public points
(`pt_inj`).  For Merkle–Damgård (nodes = block lists, the point of `bs ++ [b]` at the label `v`
of `bs` is the cell `(v, b)`) this fails: `bs ++ [b]` and `bs' ++ [b]` have the same point when
`bs` and `bs'` have the same label.

Here `LGraph` drops `pt_inj` and keeps only `root_inj` (childless nodes have distinct points).
The missing injectivity becomes a state predicate, `PtColl`: two distinct nodes, both with drawn
children, have the same point at their children's values.  It is monotone, and the bad event of
the relabelling is `Bad = Conflict ∨ PtColl` (VCVio's `Conflict`: a node with drawn children
whose point the public cache already holds).  Every statement of VCVio's file that used
`pt_inj` holds on states off `PtColl`; the relabelled game, read through the merge, is dominated
by the ideal (= real) game until `Bad` (`LGraph.dominatedUntilBad_relabelImpl`), so

* **`LGraph.prEvent_idealImpl_le_relabelImpl`**: an event of the real lazy-oracle game (VCVio's
  `SecretEncoding.idealImpl`) is at most the same event of the relabelled game read through the
  merge, or `Bad`.

The definitions `RelabelState`, `drawCell`, `labelImpl` are VCVio's (they do not mention the
graph).  Changed relative to VCVio: the structure (`pt_inj` → `root_inj`), the bad predicate,
hypotheses `¬ PtColl` on the lemmas that identified a node by its point, and the support lemmas,
which no longer identify the chosen node.
-/

open OracleComp OracleSpec

namespace Ideal.Direct

/-- A graph of public points with possibly non-injective points (VCVio's `CanonicalGraph`
without `pt_inj`): each node `k` has children `ch k` and a public point `pt k vs` at children
values `vs`, answered in `R`.  Only childless nodes are required to have distinct points. -/
structure LGraph {ι : Type} (pub : OracleSpec ι) (X K R : Type) where
  /-- The children of a node. -/
  ch : K → List (X ⊕ K)
  /-- The public point of a node at children values. -/
  pt : K → List R → ι
  /-- The public oracle answers every node point in `R`. -/
  range_eq : ∀ k vs, pub.Range (pt k vs) = R
  /-- Childless nodes have distinct points. -/
  root_inj : ∀ {k k'}, ch k = [] → ch k' = [] → pt k [] = pt k' [] → k = k'

namespace LGraph

variable {ι : Type} {pub : OracleSpec ι} {X K R : Type} (G : LGraph pub X K R)

theorem range_eq_of_pt_eq {k : K} {vs : List R} {t : ι} (h : G.pt k vs = t) : pub.Range t = R :=
  h ▸ G.range_eq k vs

/-! ## Children values -/

/-- The values of the children of a node, if all are drawn. -/
def childVals (st : RelabelState pub X K R) (k : K) : Option (List R) :=
  (G.ch k).mapM st.2

theorem childVals_eq_some_iff {st : RelabelState pub X K R} {k : K} {vs : List R} :
    G.childVals st k = some vs ↔ List.Forall₂ (fun c v ↦ st.2 c = some v) (G.ch k) vs :=
  List.mapM_eq_some_iff_forall₂

theorem length_eq_of_childVals_eq_some {st : RelabelState pub X K R} {k : K} {vs : List R}
    (h : G.childVals st k = some vs) : vs.length = (G.ch k).length :=
  ((G.childVals_eq_some_iff.1 h).length_eq).symm

theorem isSome_childVals_iff {st : RelabelState pub X K R} {k : K} :
    (G.childVals st k).isSome ↔ ∀ c ∈ G.ch k, (st.2 c).isSome :=
  List.isSome_mapM

theorem childVals_mono {st st' : RelabelState pub X K R} (hle : st ≤ st') {k : K}
    {vs : List R} (h : G.childVals st k = some vs) : G.childVals st' k = some vs :=
  G.childVals_eq_some_iff.2 ((G.childVals_eq_some_iff.1 h).imp fun _ _ h ↦ hle.2 h)

theorem childVals_congr {st st' : RelabelState pub X K R} {k : K}
    (h : ∀ c ∈ G.ch k, st.2 c = st'.2 c) : G.childVals st k = G.childVals st' k :=
  Option.ext fun vs ↦ by
    rw [childVals_eq_some_iff, childVals_eq_some_iff, List.forall₂_apply_eq_some_iff,
      List.forall₂_apply_eq_some_iff, List.map_inj_left.2 h]

theorem childVals_of_ch_nil {st : RelabelState pub X K R} {k : K} (h : G.ch k = []) :
    G.childVals st k = some [] := by
  simp [childVals, h]

/-! ## Point collisions -/

/-- **A point collision**: two distinct nodes with drawn children have the same point at their
children values. -/
def PtColl (st : RelabelState pub X K R) : Prop :=
  ∃ k k' vs vs', G.childVals st k = some vs ∧ G.childVals st k' = some vs' ∧
    G.pt k vs = G.pt k' vs' ∧ k ≠ k'

theorem PtColl.mono {st st' : RelabelState pub X K R} (hle : st ≤ st') (h : G.PtColl st) :
    G.PtColl st' := by
  obtain ⟨k, k', vs, vs', hk, hk', hpt, hne⟩ := h
  exact ⟨k, k', vs, vs', G.childVals_mono hle hk, G.childVals_mono hle hk', hpt, hne⟩

/-- Off a point collision, a point is the point of at most one node with drawn children. -/
theorem eq_of_childVals_of_pt_eq {st : RelabelState pub X K R} (hc : ¬ G.PtColl st) {k k' : K}
    {vs vs' : List R} (h : G.childVals st k = some vs) (h' : G.childVals st k' = some vs')
    (hpt : G.pt k vs = G.pt k' vs') : k = k' ∧ vs = vs' := by
  by_cases hkk : k = k'
  · subst hkk
    exact ⟨rfl, Option.some_inj.1 (h.symm.trans h')⟩
  · exact absurd ⟨k, k', vs, vs', h, h', hpt, hkk⟩ hc

theorem not_ptColl_empty : ¬ G.PtColl ((∅, ∅) : RelabelState pub X K R) := by
  rintro ⟨k, k', vs, vs', hk, hk', hpt, hne⟩
  have hch : ∀ {k : K} {vs : List R}, G.childVals ((∅, ∅) : RelabelState pub X K R) k = some vs →
      G.ch k = [] ∧ vs = [] := by
    intro k vs h
    have h2 := G.childVals_eq_some_iff.1 h
    cases hc : G.ch k with
    | nil =>
      rw [hc] at h2
      exact ⟨rfl, (List.forall₂_nil_left_iff.1 h2)⟩
    | cons c cs =>
      rw [hc] at h2
      obtain ⟨v, vs', hv, -, -⟩ := List.forall₂_cons_left_iff.1 h2
      simp at hv
  obtain ⟨h1, rfl⟩ := hch hk
  obtain ⟨h2, rfl⟩ := hch hk'
  exact hne (G.root_inj h1 h2 hpt)

open Classical in
theorem dite_exists_pt_eq {β : Sort*} {st : RelabelState pub X K R} (hc : ¬ G.PtColl st) {k : K}
    {vs : List R} (h : G.childVals st k = some vs) (F : K → pub.Range (G.pt k vs) = R → β)
    (g : (¬∃ k' vs', G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs) → β) :
    (if hex : ∃ k' vs', G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs then
      F hex.choose (G.range_eq_of_pt_eq hex.choose_spec.choose_spec.2) else g hex) =
      F k (G.range_eq k vs) := by
  have hex : ∃ k' vs', G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs := ⟨k, vs, h, rfl⟩
  simp only [hex, ↓reduceDIte]
  exact congrArg₂ F (G.eq_of_childVals_of_pt_eq hc hex.choose_spec.choose_spec.1 h
    hex.choose_spec.choose_spec.2).1 rfl

/-! ## Merging the state into a public cache -/

open Classical in
/-- The public cache the relabelled state stands for. -/
noncomputable def merge (st : RelabelState pub X K R) : pub.QueryCache :=
  .ofFn fun t ↦ if h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t then
    (st.2 (.inr h.choose)).map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm)
  else st.1 t

theorem merge_apply_pt {st : RelabelState pub X K R} (hc : ¬ G.PtColl st) {k : K} {vs : List R}
    (h : G.childVals st k = some vs) :
    G.merge st (G.pt k vs) = (st.2 (.inr k)).map (cast (G.range_eq k vs).symm) := by
  rw [merge, QueryCache.ofFn_apply]
  exact G.dite_exists_pt_eq hc h (fun k' e ↦ (st.2 (.inr k')).map (cast e.symm)) _

theorem merge_apply_of_not_exists {st : RelabelState pub X K R} {t : ι}
    (ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t) : G.merge st t = st.1 t := by
  simp only [merge, QueryCache.ofFn_apply, ht, ↓reduceDIte]

@[simp] theorem merge_empty : G.merge ((∅, ∅) : RelabelState pub X K R) = ∅ := by
  refine QueryCache.ext fun t ↦ ?_
  by_cases ht : ∃ k vs, G.childVals (∅, ∅) k = some vs ∧ G.pt k vs = t
  · obtain ⟨k, vs, hk, rfl⟩ := ht
    simp only [G.merge_apply_pt G.not_ptColl_empty hk, QueryCache.empty_apply, Option.map_none]
  · simp only [G.merge_apply_of_not_exists ht, QueryCache.empty_apply]

/-- The split state of the ideal game that a relabelled state stands for. -/
noncomputable def toSplitCache (st : RelabelState pub X K R) :
    SecretEncoding.SplitCache pub X R :=
  (G.merge st, st.table)

@[simp] theorem toSplitCache_empty :
    G.toSplitCache ((∅, ∅) : RelabelState pub X K R) = (∅, ∅) := by
  simp only [toSplitCache, merge_empty, RelabelState.table_empty]

/-! ## Conflicts -/

/-- VCVio's conflict: some node whose children are all drawn has its point in the public
cache. -/
def Conflict (st : RelabelState pub X K R) : Prop :=
  ∃ k vs, G.childVals st k = some vs ∧ (st.1 (G.pt k vs)).isSome

theorem Conflict.mono {st st' : RelabelState pub X K R} (hle : st ≤ st') (h : G.Conflict st) :
    G.Conflict st' := by
  obtain ⟨k, vs, hk, hc⟩ := h
  exact ⟨k, vs, G.childVals_mono hle hk, QueryCache.isSome_mono hle.1 hc⟩

theorem not_conflict_empty : ¬G.Conflict ((∅, ∅) : RelabelState pub X K R) := by
  rintro ⟨k, vs, -, h⟩
  simp only [QueryCache.empty_apply, Option.isSome_none, Bool.false_eq_true] at h

/-- **The bad event of the relabelling**: a conflict or a point collision. -/
def Bad (st : RelabelState pub X K R) : Prop := G.Conflict st ∨ G.PtColl st

theorem Bad.mono {st st' : RelabelState pub X K R} (hle : st ≤ st') (h : G.Bad st) :
    G.Bad st' :=
  h.imp (Conflict.mono G hle) (PtColl.mono G hle)

theorem not_bad_empty : ¬G.Bad ((∅, ∅) : RelabelState pub X K R) := by
  rintro (h | h)
  · exact G.not_conflict_empty h
  · exact G.not_ptColl_empty h

/-- Every drawn label belongs to a node whose children are all drawn. -/
def LabelsComplete (st : RelabelState pub X K R) : Prop :=
  ∀ k, (st.2 (.inr k)).isSome → (G.childVals st k).isSome

theorem labelsComplete_empty : G.LabelsComplete ((∅, ∅) : RelabelState pub X K R) := by
  intro k hk
  simp only [QueryCache.empty_apply, Option.isSome_none, Bool.false_eq_true] at hk

theorem merge_apply_eq_of_le {st st' : RelabelState pub X K R} (hle : st ≤ st')
    (hinv : G.LabelsComplete st) (hc : ¬G.Bad st') {t : ι} (hcache : st'.1 t = st.1 t)
    (hlab : ∀ k vs, G.childVals st' k = some vs → G.pt k vs = t →
      st'.2 (.inr k) = st.2 (.inr k)) :
    G.merge st' t = G.merge st t := by
  have hp' : ¬ G.PtColl st' := fun h ↦ hc (Or.inr h)
  have hp : ¬ G.PtColl st := fun h ↦ hp' (h.mono G hle)
  by_cases ht' : ∃ k vs, G.childVals st' k = some vs ∧ G.pt k vs = t
  · obtain ⟨k, vs, hk', rfl⟩ := ht'
    rw [G.merge_apply_pt hp' hk', hlab k vs hk' rfl]
    cases hk : G.childVals st k with
    | some ws =>
      obtain rfl : ws = vs := Option.some_inj.1 ((G.childVals_mono hle hk).symm.trans hk')
      rw [G.merge_apply_pt hp hk]
    | none =>
      have hl : st.2 (.inr k) = none := by
        cases hl : st.2 (.inr k) with
        | none => rfl
        | some _ => simpa only [hk, hl, Option.isSome_some, Option.isSome_none,
            Bool.false_eq_true, imp_false, not_true_eq_false] using hinv k
      have hnot : ¬∃ k' vs', G.childVals st k' = some vs' ∧ G.pt k' vs' = G.pt k vs := by
        rintro ⟨k', vs', hk'', hpt⟩
        obtain ⟨rfl, rfl⟩ := G.eq_of_childVals_of_pt_eq hp' (G.childVals_mono hle hk'') hk' hpt
        rw [hk] at hk''
        exact absurd hk'' (Option.some_ne_none _).symm
      rw [G.merge_apply_of_not_exists hnot, ← hcache, hl, Option.map_none]
      cases hC : st'.1 (G.pt k vs) with
      | none => rfl
      | some _ => exact absurd (Or.inl ⟨k, vs, hk', by rw [hC]; rfl⟩) hc
  · have ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t := fun ⟨k, vs, hk, hpt⟩ ↦
      ht' ⟨k, vs, G.childVals_mono hle hk, hpt⟩
    rw [G.merge_apply_of_not_exists ht', G.merge_apply_of_not_exists ht, hcache]

/-! ## The relabelled game -/

variable [DecidableEq ι] [DecidableEq X] [DecidableEq K] [SampleableType R]
  [∀ t, SampleableType (pub.Range t)]

open Classical in
/-- **The relabelled game** (VCVio's `relabelImpl`, verbatim). -/
noncomputable def relabelImpl :
    QueryImpl (pub.withDerivations X R) (StateT (RelabelState pub X K R) ProbComp) := fun
  | .inl (.inl n) => StateT.mk fun st ↦ (fun u ↦ (u, st)) <$> (unifSpec.query n : ProbComp _)
  | .inl (.inr t) => StateT.mk fun st ↦
      if h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t then
        Prod.map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) id <$>
          (RelabelState.drawCell (.inr h.choose)).run st
      else (fun z ↦ (z.1, (z.2, st.2))) <$> (pub.randomOracle t).run st.1
  | .inr x => RelabelState.drawCell (.inl x)

theorem relabelImpl_run_unif (n : ℕ) (st : RelabelState pub X K R) :
    (G.relabelImpl (.inl (.inl n))).run st =
      (fun u ↦ (u, st)) <$> (unifSpec.query n : ProbComp _) := by rfl

theorem relabelImpl_apply_inr (x : X) :
    G.relabelImpl (.inr x) = RelabelState.drawCell (.inl x) := by rfl

open Classical in
theorem relabelImpl_run_pub (t : ι) (st : RelabelState pub X K R) :
    (G.relabelImpl (.inl (.inr t))).run st =
      if h : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t then
        Prod.map (cast (G.range_eq_of_pt_eq h.choose_spec.choose_spec.2).symm) id <$>
          (RelabelState.drawCell (.inr h.choose)).run st
      else (fun z ↦ (z.1, (z.2, st.2))) <$> (pub.randomOracle t).run st.1 := by
  simp only [relabelImpl, StateT.run_mk]

theorem relabelImpl_run_pt {st : RelabelState pub X K R} (hc : ¬ G.PtColl st) {k : K}
    {vs : List R} (h : G.childVals st k = some vs) :
    (G.relabelImpl (.inl (.inr (G.pt k vs)))).run st =
      Prod.map (cast (G.range_eq k vs).symm) id <$> (RelabelState.drawCell (.inr k)).run st := by
  rw [relabelImpl_run_pub]
  exact G.dite_exists_pt_eq hc h
    (fun k' e ↦ Prod.map (cast e.symm) id <$> (RelabelState.drawCell (.inr k')).run st) _

theorem relabelImpl_run_pub_of_not_exists {st : RelabelState pub X K R} {t : ι}
    (ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t) :
    (G.relabelImpl (.inl (.inr t))).run st =
      (fun z ↦ (z.1, (z.2, st.2))) <$> (pub.randomOracle t).run st.1 := by
  rw [relabelImpl_run_pub]
  simp only [ht, ↓reduceDIte]

/-! ## Monotonicity -/

/-- Every step of the relabelled game extends the state. -/
theorem le_of_mem_support_relabelImpl {t : (pub.withDerivations X R).Domain}
    {st : RelabelState pub X K R} {z} (hz : z ∈ support ((G.relabelImpl t).run st)) :
    st ≤ z.2 := by
  classical
  rcases t with (n | t) | x
  · rw [relabelImpl_run_unif, support_map] at hz
    obtain ⟨_, -, rfl⟩ := hz
    exact le_rfl
  · rw [relabelImpl_run_pub] at hz
    split_ifs at hz with ht
    · rw [support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hw).1
    · rw [support_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact ⟨QueryImpl.withCaching_cache_le _ _ _ _ hw, le_rfl⟩
  · exact (RelabelState.le_and_cell_eq_of_mem_support_drawCell hz).1

theorem preservesInv_bad_relabelImpl : QueryImpl.PreservesInv G.relabelImpl G.Bad :=
  fun _ _ h _ hz ↦ h.mono G (G.le_of_mem_support_relabelImpl hz)

/-- A label is drawn only for a node whose children are all drawn. -/
theorem preservesInv_labelsComplete_relabelImpl :
    QueryImpl.PreservesInv G.relabelImpl G.LabelsComplete := by
  classical
  intro t st hinv z hz k hk
  have hle := G.le_of_mem_support_relabelImpl hz
  have hsome : (G.childVals st k).isSome := by
    rcases t with (n | t) | x
    · rw [relabelImpl_run_unif, support_map] at hz
      obtain ⟨_, -, rfl⟩ := hz
      exact hinv k hk
    · rw [relabelImpl_run_pub] at hz
      split_ifs at hz with ht
      · rw [support_map] at hz
        obtain ⟨w, hw, rfl⟩ := hz
        simp only [RelabelState.drawCell, StateT.run_mk, support_map] at hw
        obtain ⟨y, hy, rfl⟩ := hw
        rcases (QueryImpl.withCaching_run_isSome_apply_iff _ hy (.inr k)).1 hk with h | h
        · exact hinv k h
        · cases h
          rw [ht.choose_spec.choose_spec.1]
          rfl
      · rw [support_map] at hz
        obtain ⟨w, -, rfl⟩ := hz
        exact hinv k hk
    · simp only [relabelImpl_apply_inr, RelabelState.drawCell, StateT.run_mk, support_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rcases (QueryImpl.withCaching_run_isSome_apply_iff _ hy (.inr k)).1 hk with h | h
      · exact hinv k h
      · cases h
  obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.1 hsome
  rw [G.childVals_mono hle hvs]
  rfl

/-! ## The relabelled game projects onto the ideal game off `Bad` -/

private theorem step_unif (n : ℕ) (st : RelabelState pub X K R)
    (Q : (pub.withDerivations X R).Range (.inl (.inl n)) ×
      SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inl (.inl n))).run st}[
        Q (z.1, G.toSplitCache z.2) ∧ ¬G.Bad z.2] ≤
      Pr{let z ← ((SecretEncoding.idealImpl pub X R (.inl (.inl n))).run
        (G.toSplitCache st))}[Q z] := by
  rw [relabelImpl_run_unif, prEvent_map]
  change _ ≤ Pr{let z ← (fun u ↦ (u, G.toSplitCache st)) <$> (unifSpec.query n : ProbComp _)}[Q z]
  rw [prEvent_map]
  exact prEvent_mono _ (fun u ↦ Q (u, G.toSplitCache st) ∧ ¬G.Bad st) _ fun _ h ↦ h.1

private theorem step_derive (x : X) (st : RelabelState pub X K R) (hinv : G.LabelsComplete st)
    (Q : (pub.withDerivations X R).Range (.inr x) × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inr x)).run st}[Q (z.1, G.toSplitCache z.2) ∧ ¬G.Bad z.2] ≤
      Pr{let z ← (SecretEncoding.idealImpl pub X R (.inr x)).run (G.toSplitCache st)}[Q z] := by
  rw [relabelImpl_apply_inr]
  cases hT : st.2 (.inl x) with
  | some v =>
    rw [RelabelState.drawCell_run_of_cell_eq_some hT,
      SecretEncoding.idealImpl_run_derive_some (st := G.toSplitCache st) hT]
    exact prEvent_pure_le_pure _ _ _ _ And.left
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none hT,
      SecretEncoding.idealImpl_run_derive_none (st := G.toSplitCache st) hT]
    refine prEvent_map_le_map _ _ _ _ _ fun u hu ↦ ?_
    have hm : G.merge (st.1, st.2.cacheQuery (.inl x) u) = G.merge st :=
      QueryCache.ext fun t ↦ G.merge_apply_eq_of_le (st := st)
        (st' := (st.1, st.2.cacheQuery (.inl x) u))
        ⟨le_rfl, QueryCache.le_cacheQuery _ hT⟩ hinv hu.2 rfl fun _ _ _ _ ↦
          QueryCache.cacheQuery_of_ne _ _ nofun
    have h2 : G.toSplitCache (st.1, st.2.cacheQuery (.inl x) u) =
        ((G.toSplitCache st).1, st.table.cacheQuery x u) := by
      rw [toSplitCache, toSplitCache, hm, RelabelState.table_cacheQuery_inl]
    exact h2 ▸ hu.1

private theorem step_pt (st : RelabelState pub X K R) (hinv : G.LabelsComplete st)
    (hb : ¬ G.Bad st) {k : K}
    {vs : List R} (hk : G.childVals st k = some vs)
    (Q : (pub.withDerivations X R).Range (.inl (.inr (G.pt k vs))) ×
      SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inl (.inr (G.pt k vs)))).run st}[
        Q (z.1, G.toSplitCache z.2) ∧ ¬G.Bad z.2] ≤
      Pr{let z ← ((SecretEncoding.idealImpl pub X R (.inl (.inr (G.pt k vs)))).run
        (G.toSplitCache st))}[Q z] := by
  have hp : ¬ G.PtColl st := fun h ↦ hb (Or.inr h)
  rw [G.relabelImpl_run_pt hp hk]
  have hmerge := G.merge_apply_pt hp hk
  cases hl : st.2 (.inr k) with
  | some v =>
    rw [RelabelState.drawCell_run_of_cell_eq_some hl, map_pure,
      SecretEncoding.idealImpl_run_pub_some (st := G.toSplitCache st)
        (v := cast (G.range_eq k vs).symm v) (by rw [toSplitCache, hmerge, hl]; rfl)]
    exact prEvent_pure_le_pure _ _ _ _ And.left
  | none =>
    rw [RelabelState.drawCell_run_of_cell_eq_none hl, Functor.map_map,
      SecretEncoding.idealImpl_run_pub_none (st := G.toSplitCache st)
        (by rw [toSplitCache, hmerge, hl]; rfl),
      prEvent_map]
    refine le_trans ?_ (le_of_eq (prEvent_map _ _ _).symm)
    rw [← SampleableType.prEvent_map_cast_uniformSample (G.range_eq k vs).symm, prEvent_map]
    refine prEvent_mono _ _ _ fun u hu ↦ ?_
    set h := (G.range_eq k vs).symm
    have hle : st ≤ (st.1, st.2.cacheQuery (.inr k) u) := ⟨le_rfl, QueryCache.le_cacheQuery _ hl⟩
    have hp' : ¬ G.PtColl (st.1, st.2.cacheQuery (.inr k) u) := fun h ↦ hu.2 (Or.inr h)
    have hm : G.merge (st.1, st.2.cacheQuery (.inr k) u) =
        (G.merge st).cacheQuery (G.pt k vs) (cast h u) := by
      refine QueryCache.ext fun t ↦ ?_
      by_cases ht : t = G.pt k vs
      · subst ht
        rw [G.merge_apply_pt hp' (G.childVals_mono hle hk), QueryCache.cacheQuery_self,
          QueryCache.cacheQuery_self]
        rfl
      · rw [QueryCache.cacheQuery_of_ne _ _ ht]
        refine G.merge_apply_eq_of_le hle hinv hu.2 rfl fun k' vs' hk' hpt ↦ ?_
        have hkk : k' ≠ k := by
          rintro rfl
          obtain rfl : vs' = vs := Option.some_inj.1 (hk'.symm.trans (G.childVals_mono hle hk))
          exact ht hpt.symm
        exact QueryCache.cacheQuery_of_ne _ _ fun e ↦ hkk (Sum.inr_injective e)
    have h2 : G.toSplitCache (st.1, st.2.cacheQuery (.inr k) u) =
        ((G.merge st).cacheQuery (G.pt k vs) (cast h u), st.table) := by
      rw [toSplitCache, hm, RelabelState.table_cacheQuery_inr]
    exact h2 ▸ hu.1

private theorem step_pub_of_not_exists (st : RelabelState pub X K R) (hinv : G.LabelsComplete st)
    {t : ι} (ht : ¬∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t)
    (Q : (pub.withDerivations X R).Range (.inl (.inr t)) ×
      SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (G.relabelImpl (.inl (.inr t))).run st}[
        Q (z.1, G.toSplitCache z.2) ∧ ¬G.Bad z.2] ≤
      Pr{let z ← ((SecretEncoding.idealImpl pub X R (.inl (.inr t))).run
        (G.toSplitCache st))}[Q z] := by
  have hmerge : (G.toSplitCache st).1 t = st.1 t := G.merge_apply_of_not_exists ht
  cases hc : st.1 t with
  | some v =>
    have hrun : (G.relabelImpl (.inl (.inr t))).run st = pure (v, st) := by
      rw [G.relabelImpl_run_pub_of_not_exists ht, randomOracle.run_eq]
      simp [hc]
    rw [hrun, SecretEncoding.idealImpl_run_pub_some (hmerge.trans hc)]
    exact prEvent_pure_le_pure _ _ _ _ And.left
  | none =>
    have hrun : (G.relabelImpl (.inl (.inr t))).run st =
        (fun u ↦ (u, (st.1.cacheQuery t u, st.2))) <$> ($ᵗ pub.Range t) := by
      rw [G.relabelImpl_run_pub_of_not_exists ht, randomOracle.run_eq]
      simp [hc]
    rw [hrun, SecretEncoding.idealImpl_run_pub_none (hmerge.trans hc)]
    refine prEvent_map_le_map _ _ _ _ _ fun u hu ↦ ?_
    set st' : RelabelState pub X K R := (st.1.cacheQuery t u, st.2)
    have hle : st ≤ st' := ⟨QueryCache.le_cacheQuery _ hc, le_rfl⟩
    have hm : G.merge st' = (G.merge st).cacheQuery t u := by
      refine QueryCache.ext fun t' ↦ ?_
      by_cases htt : t' = t
      · subst htt
        rw [QueryCache.cacheQuery_self, G.merge_apply_of_not_exists (st := st') ht]
        exact QueryCache.cacheQuery_self _ _ _
      · rw [QueryCache.cacheQuery_of_ne _ _ htt]
        exact G.merge_apply_eq_of_le hle hinv hu.2 (QueryCache.cacheQuery_of_ne _ _ htt)
          fun _ _ _ _ ↦ rfl
    have h2 : G.toSplitCache st' = ((G.merge st).cacheQuery t u, st.table) := by
      rw [toSplitCache, hm]; rfl
    exact h2 ▸ hu.1

theorem dominatedUntilBad_relabelImpl :
    QueryImpl.DominatedUntilBad G.relabelImpl (SecretEncoding.idealImpl pub X R) G.toSplitCache
      G.LabelsComplete G.Bad := by
  intro t st hinv hb Q
  rcases t with (n | t) | x
  · exact G.step_unif n st Q
  · by_cases ht : ∃ k vs, G.childVals st k = some vs ∧ G.pt k vs = t
    · obtain ⟨k, vs, hk, rfl⟩ := ht
      exact G.step_pt st hinv hb hk Q
    · exact G.step_pub_of_not_exists st hinv ht Q
  · exact G.step_derive x st hinv Q

/-- **Relabelling with point collisions, off `Bad`.** -/
theorem prEvent_relabelImpl_and_not_bad_le {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (simulateQ G.relabelImpl oa).run (∅, ∅)}[
        P (z.1, G.toSplitCache z.2) ∧ ¬G.Bad z.2] ≤
      Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z] := by
  simpa only [toSplitCache_empty] using
    G.dominatedUntilBad_relabelImpl.prEvent_simulateQ_run_map_and_not_bad_le
      G.preservesInv_labelsComplete_relabelImpl G.preservesInv_bad_relabelImpl oa (∅, ∅)
      G.labelsComplete_empty P

/-- **Relabelling with point collisions.**  An event of the real lazy-oracle game is at most the
same event of the relabelled game, read on the merged state, or `Bad` (a conflict or a point
collision). -/
theorem prEvent_idealImpl_le_relabelImpl {α : Type}
    (oa : OracleComp (pub.withDerivations X R) α)
    (P : α × SecretEncoding.SplitCache pub X R → Prop) :
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl oa).run (∅, ∅)}[
        P (z.1, G.toSplitCache z.2) ∨ G.Bad z.2] := by
  simpa only [toSplitCache_empty] using
    G.dominatedUntilBad_relabelImpl.prEvent_simulateQ_run_le_map_or_bad
      G.preservesInv_labelsComplete_relabelImpl G.preservesInv_bad_relabelImpl oa (∅, ∅)
      G.labelsComplete_empty P

end LGraph

end Ideal.Direct

#print axioms Ideal.Direct.LGraph.dominatedUntilBad_relabelImpl
#print axioms Ideal.Direct.LGraph.prEvent_idealImpl_le_relabelImpl
#print axioms Ideal.Direct.LGraph.prEvent_relabelImpl_and_not_bad_le
