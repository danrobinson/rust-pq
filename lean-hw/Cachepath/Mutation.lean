import Cachepath.MutationCaller
import Cachepath.EndToEnd

open Aeneas Aeneas.Std Result CacheopsRust
open slhdsa.cache.endtoend
namespace CacheopsRust.cache.mutation

private abbrev Nodes (N : Usize) := alloc.vec.Vec (Array U8 N)
private abbrev Answer (N : Usize) := Option (Slice (Array U8 N)) × TopTreeCache N

/-- The returned slice is valid at the requested tree, and every resident
entry still satisfies the key-specific invariant after mutation. -/
def Post {N : Usize} (c : TopTreeCache N) (p : Spec.Params) (sk pk : Spec.Bytes)
    (key : U64) (result : Answer N) : Prop :=
  CacheValid result.2 p sk pk ∧ result.2.family = c.family ∧
  result.2.layer_d2_capacity = c.layer_d2_capacity ∧
  (result.1 = none → (c.layer_d2_capacity = 0#usize ∨ p.d < 2) ∧
    ∀ e ∈ result.2.layer_d2.val, e.tree_index ≠ key) ∧
  (∀ s, result.1 = some s → s.length = treeSize p.hp ∧
    slhdsa.cache.Built s p sk pk (layerAdrs (p.d - 2) key.val))

private theorem get {N : Usize} (v : alloc.vec.Vec (LayerD2Entry N))
    (i : Usize) (h : i.val < v.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) v i = ok v.val[i.val] := by
  simp only [alloc.vec.Vec.index, Slice.index_usize, Slice.getElem?_Usize_eq, alloc.vec.Vec.val]
  have h' : i.val < v.slice.val.length := h
  rw [List.getElem?_eq_getElem h']

private def fromIndex {N : Usize} (c : TopTreeCache N) (pos : Usize) : Result (Answer N) := do
  let e ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) c.layer_d2 pos
  ok (some (alloc.vec.Vec.deref e.nodes), c)

private theorem fromIndex_safe {N : Usize} (c : TopTreeCache N) {p sk pk key}
    (hc : CacheValid c p sk pk) (pos : Usize) (hp : pos.val < c.layer_d2.val.length)
    (hm : c.layer_d2.val[pos.val].tree_index = key) :
    fromIndex c pos ⦃ r => Post c p sk pk key r ⦄ := by
  rw [fromIndex, get _ _ hp]; simp only [bind_ok, WP.spec_ok]
  refine ⟨hc, rfl, rfl, by simp, ?_⟩
  rintro _ ⟨⟩
  have hv := hc.d2_built _ (List.getElem_mem hp)
  simpa only [vec_deref_len, hm] using hv

private def front {N : Usize} (c : TopTreeCache N) (v : alloc.vec.Vec (LayerD2Entry N))
    (e : LayerD2Entry N) := do
  let v1 ← insert v 0#usize e
  fromIndex { c with layer_d2 := v1 } 0#usize

private theorem front_safe {N : Usize} (c : TopTreeCache N) {p sk pk key}
    (hc : CacheValid c p sk pk) (v : alloc.vec.Vec (LayerD2Entry N))
    (e : LayerD2Entry N) (size : v.val.length < Usize.max)
    (subset : ∀ a ∈ v.val, a ∈ c.layer_d2.val)
    (matchKey : e.tree_index = key)
    (built : e.nodes.length = treeSize p.hp ∧
      slhdsa.cache.Built (alloc.vec.Vec.deref e.nodes) p sk pk (layerAdrs (p.d - 2) key.val)) :
    front c v e ⦃ r => Post c p sk pk key r ⦄ := by
  let v1 := alloc.vec.Vec.from (e :: v.val) (by simpa using size)
  have hins : insert v 0#usize e = ok v1 := by
    simp [insert, size, v1]
  rw [front, hins]; simp only [bind_tc_ok]
  refine fromIndex_safe {c with layer_d2 := v1} ?_ 0#usize ?_ ?_
  · refine { hc with d2_built := ?_ }
    intro a ha
    simp only [v1, alloc.vec.Vec.from_val] at ha
    rcases List.mem_cons.mp ha with rfl | h
    · simpa only [matchKey] using built
    · exact hc.d2_built _ (subset _ h)
  · simp [v1]
  · simpa [v1] using matchKey

private def hit {N : Usize} (c : TopTreeCache N) (hp : U32) (pos : Usize) : Result (Answer N) := do
  if pos != 0#usize
  then
    let i := alloc.vec.Vec.len c.layer_d2
    let i1 ← 1#usize <<< hp
    if i < i1
    then
      let (entry, v) ←
        cache.mutation.remove alloc.alloc.Global c.layer_d2 pos
      let v1 ← cache.mutation.insert v 0#usize entry
      let lde ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          (cache.LayerD2Entry N)) v1 0#usize
      let s1 := alloc.vec.Vec.deref lde.nodes
      ok (some s1, { c with layer_d2 := v1 })
    else
      let lde ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          (cache.LayerD2Entry N)) c.layer_d2 pos
      let s1 := alloc.vec.Vec.deref lde.nodes
      ok (some s1, c)
  else
    let lde ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        (cache.LayerD2Entry N)) c.layer_d2 pos
    let s1 := alloc.vec.Vec.deref lde.nodes
    ok (some s1, c)

private theorem hit_safe {N : Usize} (c : TopTreeCache N) {p sk pk key}
    (hc : CacheValid c p sk pk) (hp : U32) (shift : hp.val < Usize.numBits)
    (pos : Usize) (inside : pos.val < c.layer_d2.val.length)
    (matched : c.layer_d2.val[pos.val].tree_index = key) :
    hit c hp pos ⦃ r => Post c p sk pk key r ⦄ := by
  unfold hit
  split
  · step as ⟨bound, hb⟩
    split
    · let entry := c.layer_d2.val[pos.val]
      let tail := alloc.vec.Vec.from (c.layer_d2.val.eraseIdx pos.val) (by
        rw [List.length_eraseIdx_of_lt inside]; have := c.layer_d2.property; omega)
      have hs : front c tail entry ⦃ r => Post c p sk pk key r ⦄ := by
        apply front_safe c hc _ _
        · simp only [tail, alloc.vec.Vec.from_val, List.length_eraseIdx_of_lt inside]
          have := c.layer_d2.property
          omega
        · intro a ha; simp only [tail, alloc.vec.Vec.from_val] at ha
          exact List.mem_of_mem_eraseIdx ha
        · exact matched
        · simpa only [matched] using hc.d2_built _ (List.getElem_mem inside)
      simp only [remove, inside, ↓reduceDIte, bind_ok]
      simp only [front, fromIndex, alloc.vec.Vec.index_slice_index, bind_tc_eq, tail, entry] at hs
      exact hs
    · exact fromIndex_safe c hc pos inside matched
  · exact fromIndex_safe c hc pos inside matched

private def install {N : Usize} (c : TopTreeCache N) (key : U64) (nodes : Nodes N) := do
  let v ← if alloc.vec.Vec.len c.layer_d2 >= c.layer_d2_capacity then do
    let (_, tail) ← pop alloc.alloc.Global c.layer_d2
    ok tail
  else ok c.layer_d2
  front c v ⟨key, nodes⟩

private theorem install_safe {N : Usize} (c : TopTreeCache N) {p sk pk}
    (hc : CacheValid c p sk pk) (key : U64) (nodes : Nodes N)
    (hcap : c.layer_d2_capacity ≠ 0#usize)
    (built : nodes.length = treeSize p.hp ∧
      slhdsa.cache.Built (alloc.vec.Vec.deref nodes) p sk pk (layerAdrs (p.d - 2) key.val)) :
    install c key nodes ⦃ r => Post c p sk pk key r ⦄ := by
  unfold install
  split
  · rename_i full
    simp only [pop, bind_tc_ok]
    apply front_safe c hc _ _ _ _ rfl built
    · simp only [alloc.vec.Vec.from_val, List.length_dropLast]
      have hpos : 0 < c.layer_d2.val.length := by scalar_tac
      have := c.layer_d2.property
      omega
    · intro a ha; simp only [alloc.vec.Vec.from_val] at ha
      exact List.dropLast_subset _ ha
  · rename_i fits
    simp only [bind_tc_ok]
    apply front_safe c hc _ _ _ (fun _ h => h) rfl built
    have hh : c.layer_d2.val.length < c.layer_d2_capacity.val := by scalar_tac
    scalar_tac

/-- The external builder contract is indexed by the exact arguments at this call,
including the layer, tree and both seeds. -/
def Builds {N : Usize} (builder : Builder N) (params : CacheopsRust.params.Params)
    (p : Spec.Params) (sk pk : Array U8 N) (key : U64) : Prop :=
  ∀ layer : U32, layer.val = p.d - 2 →
    builder params.hp layer key sk pk ⦃ ns => ns.length = treeSize p.hp ∧
      slhdsa.cache.Built (alloc.vec.Vec.deref ns) p (slhdsa.bytes sk.val) (slhdsa.bytes pk.val)
        (layerAdrs (p.d - 2) key.val) ⦄

private def miss {N : Usize} (sha2 shake : Builder N) (self : TopTreeCache N)
    (p : CacheopsRust.params.Params) (sk_seed pk_seed : Array U8 N) (tree_d2 : U64) :
    Result (Answer N) := do
  if self.layer_d2_capacity = 0#usize
  then ok (none, self)
  else
    if p.d < 2#u32
    then ok (none, self)
    else
      let (hf, nodes) ←
        match self.family with
        | cache.HashFamily.Sha2 =>
          do
          let i ← p.d - 2#u32
          let nodes1 ←
            sha2 p.hp i tree_d2 sk_seed pk_seed
          ok (cache.HashFamily.Sha2, nodes1)
        | cache.HashFamily.Shake =>
          do
          let i ← p.d - 2#u32
          let nodes1 ←
            shake p.hp i tree_d2 sk_seed pk_seed
          ok (cache.HashFamily.Shake, nodes1)
      let i := alloc.vec.Vec.len self.layer_d2
      let v ←
        if i >= self.layer_d2_capacity
        then
          do
          let (_, v1) ←
            cache.mutation.pop alloc.alloc.Global self.layer_d2
          ok v1
        else ok self.layer_d2
      let v1 ←
        cache.mutation.insert v 0#usize ({ tree_index := tree_d2, nodes } :
          cache.LayerD2Entry N)
      let lde ←
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
          (cache.LayerD2Entry N)) v1 0#usize
      let s1 := alloc.vec.Vec.deref lde.nodes
      ok (some s1, { self with family := hf, layer_d2 := v1 })

private theorem miss_safe {N : Usize} (sha2 shake : Builder N) (c : TopTreeCache N)
    (params : CacheopsRust.params.Params) (p : Spec.Params) (sk pk : Array U8 N) (key : U64)
    (hc : CacheValid c p (slhdsa.bytes sk.val) (slhdsa.bytes pk.val))
    (absent : ∀ e ∈ c.layer_d2.val, e.tree_index ≠ key)
    (hd : params.d.val = p.d)
    (hsha2 : c.family = .Sha2 → Builds sha2 params p sk pk key)
    (hshake : c.family = .Shake → Builds shake params p sk pk key) :
    miss sha2 shake c params sk pk key ⦃ r => Post c p (slhdsa.bytes sk.val) (slhdsa.bytes pk.val) key r ⦄ := by
  unfold miss
  split
  · rename_i zero
    rw [WP.spec_ok]; exact ⟨hc, rfl, rfl, fun _ => ⟨.inl zero, absent⟩, by simp⟩
  · rename_i cap
    split
    · rename_i small
      rw [WP.spec_ok]; exact ⟨hc, rfl, rfl, fun _ => ⟨.inr (by scalar_tac), absent⟩, by simp⟩
    · rename_i hd2
      cases hf : c.family with
      | Sha2 =>
        step as ⟨i, hi⟩
        step with hsha2 hf i (by omega) as ⟨nodes, hn, hb⟩
        have hs := install_safe c hc key nodes cap ⟨hn, hb⟩
        by_cases full : alloc.vec.Vec.len c.layer_d2 >= c.layer_d2_capacity <;>
          simp only [← hf, install, front, fromIndex, alloc.vec.Vec.index_slice_index,
            full, ↓reduceIte, pop, bind_tc_eq, bind_ok] at hs ⊢ <;>
          first | exact hs | (erw [bind_ok]; exact hs)
      | Shake =>
        step as ⟨i, hi⟩
        step with hshake hf i (by omega) as ⟨nodes, hn, hb⟩
        have hs := install_safe c hc key nodes cap ⟨hn, hb⟩
        by_cases full : alloc.vec.Vec.len c.layer_d2 >= c.layer_d2_capacity <;>
          simp only [← hf, install, front, fromIndex, alloc.vec.Vec.index_slice_index,
            full, ↓reduceIte, pop, bind_tc_eq, bind_ok] at hs ⊢ <;>
          first | exact hs | (erw [bind_ok]; exact hs)


/-- Total safety for the translated lookup/update, under the postcondition
of the selected external tree builder. The vector may start empty, full,
or even contain entries with a zero configured capacity. -/
theorem lookup_or_populate_safe {N : Usize} (sha2 shake : Builder N) (c : TopTreeCache N)
    (params : CacheopsRust.params.Params) (p : Spec.Params) (sk pk : Array U8 N) (key : U64)
    (hc : CacheValid c p (slhdsa.bytes sk.val) (slhdsa.bytes pk.val)) (hd : params.d.val = p.d)
    (shift : params.hp.val < Usize.numBits)
    (hsha2 : c.family = .Sha2 → Builds sha2 params p sk pk key)
    (hshake : c.family = .Shake → Builds shake params p sk pk key) :
    TopTreeCache.lookup_or_populate_d2 sha2 shake c params sk pk key ⦃ r =>
      Post c p (slhdsa.bytes sk.val) (slhdsa.bytes pk.val) key r ⦄ := by
  obtain ⟨ans, searchEq, found⟩ := slhdsa.spec_imp_exists
    (slhdsa.cache.search (toSearchSlice (alloc.vec.Vec.deref c.layer_d2)) key)
  change find (alloc.vec.Vec.deref c.layer_d2) key = ok ans at searchEq
  have branch : (match ans with
    | none => miss sha2 shake c params sk pk key
    | some pos => hit c params.hp pos) ⦃ r => Post c p (slhdsa.bytes sk.val) (slhdsa.bytes pk.val) key r ⦄ := by
    cases ans with
    | none =>
      apply miss_safe sha2 shake c params p sk pk key hc _ hd hsha2 hshake
      intro e he
      obtain ⟨idx, hi, rfl⟩ := List.getElem_of_mem he
      have hlen : idx < (toSearchSlice (alloc.vec.Vec.deref c.layer_d2)).length := by
        simpa [toSearchSlice, Slice.length, slhdsa.vec_deref_val] using hi
      have hmiss := found.1 idx hlen (by simpa using hlen)
      simpa [toSearchSlice, toSearchEntry, slhdsa.vec_deref_val] using hmiss
    | some pos =>
      obtain ⟨hpos, heq⟩ := found.2 pos rfl
      refine hit_safe c hc params.hp shift pos ?_ ?_
      · simpa [toSearchSlice, Slice.length, slhdsa.vec_deref_val] using hpos
      · simpa [toSearchSlice, toSearchEntry, slhdsa.vec_deref_val] using heq
  unfold TopTreeCache.lookup_or_populate_d2
  split
  · rename_i cap
    step as ⟨empty, he⟩
    split
    · rename_i isEmpty
      rw [WP.spec_ok]
      refine ⟨hc, rfl, rfl, fun _ => ⟨.inl cap, ?_⟩, by simp⟩
      have zero : c.layer_d2.val.length = 0 := he ▸ isEmpty
      simp [List.length_eq_zero_iff.mp zero]
    · cases ans <;>
        simpa only [miss, hit, searchEq, ite_eq_left cap, bind_tc_eq, bind_ok,
          alloc.vec.Vec.index_slice_index] using branch
  · rename_i cap
    cases ans <;> cases hf : c.family <;>
      simpa only [miss, hit, searchEq, ite_eq_right cap, hf, bind_tc_eq, bind_ok,
        alloc.vec.Vec.index_slice_index] using branch

end CacheopsRust.cache.mutation
