import Cacheops.Funs
import Cachepath.Construction
import Cachesearch.Proof
import Spec.PreHash
import Slhdsa.Proofs.Slh

open Aeneas Aeneas.Std Result
open slhdsa

/-!
# End-to-End Cached Signing, Key Association, Reuse, Insertion & Eviction

Composes directly with:
- `Cachepath.Construction` (`slhdsa.cache.Built`, `constructed`, `built_xmss`),
- `Cachepath.Proof` (`path`, `root`, `TreeContents`),
- `Cachesearch.Proof` (`FirstMatch`, `Matches`, `search`, `lookup`),
- `Cacheops.Funs` (fresh 3-target Aeneas extraction of `matches_key`, `pk_root`,
  `set_layer_d2_capacity`, `with_layer_d2_capacity`, `lookup_d2`,
  `layer_d2_tree_index`, `digest_tree`, `digest_leaf`, and `sha2_ops::sign_from_digest`),
- `Slhdsa.Proofs.Slh` and `Spec.PreHash`.
-/

namespace slhdsa.cache.endtoend

open CacheopsRust

/-! ## Level-contiguous tree arithmetic & helpers -/

/-- Total number of nodes in a complete binary tree of height `hp`: `2^(hp + 1) - 1`. -/
def treeSize (hp : Nat) : Nat := 2 ^ (hp + 1) - 1

/-- Start index of level `h` (`0 ≤ h ≤ hp`) in a level-contiguous flat Merkle tree. -/
def levelOff (hp h : Nat) : Nat := 2 ^ (hp + 1) - 2 ^ (hp + 1 - h)

/-- Helper for an XMSS address at `(layer, tree)`. -/
def layerAdrs (layer tree : Nat) : Spec.Adrs :=
  { Spec.Adrs.zero with layer := layer, tree := tree }

private theorem two_pow_le_two_pow {a b : Nat} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

private theorem treeSize_pos (hp : Nat) : 0 < treeSize hp := by
  have : 2 ≤ 2 ^ (hp + 1) := by
    simpa using two_pow_le_two_pow (show 1 ≤ hp + 1 by omega)
  simp only [treeSize]; omega

private theorem levelOff_hp (hp : Nat) : levelOff hp hp = treeSize hp - 1 := by
  have hpos : 2 ≤ 2 ^ (hp + 1) := by
    simpa using two_pow_le_two_pow (show 1 ≤ hp + 1 by omega)
  simp only [levelOff, treeSize, show hp + 1 - hp = 1 by omega, pow_one]
  omega

private theorem usize_max_ge : 4294967295 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> scalar_tac

private theorem vec_deref_len {T : Type} (v : alloc.vec.Vec T) :
    (alloc.vec.Vec.deref v).length = v.length := by
  simp [Slice.length, alloc.vec.Vec.length, vec_deref_val]

private theorem built_root_eq_fips {N : Usize} {tree : Slice (Array U8 N)} {p : Spec.Params}
    {sk_seed pk_seed : Spec.Bytes} {a : Spec.Adrs}
    (hlen : tree.length = treeSize p.hp)
    (hbuilt : slhdsa.cache.Built tree p sk_seed pk_seed a) :
    bytes (tree.val[tree.length - 1]!).val = Spec.xmssNode p sk_seed 0 p.hp pk_seed a := by
  have htc := slhdsa.cache.constructed hbuilt
  have hroot := htc p.hp (le_refl _) 0 (by simp)
  have hoff : tree.length - 1 = 2 ^ (p.hp + 1) - 2 ^ (p.hp + 1 - p.hp) + 0 := by
    rw [hlen, Nat.add_zero]
    exact (levelOff_hp p.hp).symm
  rw [hoff]
  exact hroot

/-! ## Cache Validity Invariant (`CacheValid`) -/

/-- A `TopTreeCache` is valid for `(p, sk_seed, pk_seed)` when:
1. Its stored dimensions `(hp, d)` and public seed `pk_seed` match `(p, pk_seed)`,
2. Its `top_tree` has `2^(hp + 1) - 1` nodes and satisfies `Built` at `(layer = d - 1, tree = 0)`,
3. Every cached layer `d - 2` entry `(tree_index, nodes)` has `2^(hp + 1) - 1` nodes and
   satisfies `Built` at `(layer = d - 2, tree = tree_index)`.

By `slhdsa.cache.constructed`, this binds every reachable node in `top_tree` and `layer_d2`
to FIPS 205 Algorithm 9 (`Spec.xmssNode`) under `(p, sk_seed, pk_seed)`. -/
structure CacheValid {N : Usize} (c : CacheopsRust.cache.TopTreeCache N) (p : Spec.Params)
    (sk_seed pk_seed : Spec.Bytes) : Prop where
  hp_eq : c.hp.val = p.hp
  d_eq : c.d.val = p.d
  pk_seed_eq : bytes c.pk_seed.val = pk_seed
  top_len : c.top_tree.length = treeSize p.hp
  top_built : slhdsa.cache.Built (alloc.vec.Vec.deref c.top_tree) p sk_seed pk_seed
    (layerAdrs (p.d - 1) 0)
  d2_built : ∀ e ∈ c.layer_d2.val,
    e.nodes.length = treeSize p.hp ∧
    slhdsa.cache.Built (alloc.vec.Vec.deref e.nodes) p sk_seed pk_seed
      (layerAdrs (p.d - 2) e.tree_index.val)

/-- Under `CacheValid`, the root of `top_tree` equals the FIPS 205 public root
`Spec.xmssNode p sk_seed 0 p.hp pk_seed {Adrs.zero with layer := p.d - 1}`. -/
theorem top_root_eq_fips {N : Usize} {c : CacheopsRust.cache.TopTreeCache N} {p : Spec.Params}
    {sk_seed pk_seed : Spec.Bytes} (hc : CacheValid c p sk_seed pk_seed) :
    bytes (c.top_tree.val[c.top_tree.length - 1]!).val =
      Spec.xmssNode p sk_seed 0 p.hp pk_seed (layerAdrs (p.d - 1) 0) := by
  have h := built_root_eq_fips (by rw [vec_deref_len]; exact hc.top_len) hc.top_built
  simpa [vec_deref_len, vec_deref_val] using h

/-! ## Key-Association Soundness (`pk_root`, `matches_key`) -/

/-- Extracted `TopTreeCache::pk_root` returns the last node of `top_tree`. -/
@[step]
theorem pk_root_spec {N : Usize} (c : CacheopsRust.cache.TopTreeCache N)
    (hne : 0 < c.top_tree.length) :
    CacheopsRust.cache.TopTreeCache.pk_root c ⦃ r => r = c.top_tree.val[c.top_tree.length - 1]! ⦄ := by
  unfold CacheopsRust.cache.TopTreeCache.pk_root
  step as ⟨i1, hi1⟩
  step as ⟨a, ha⟩
  have hlt : c.top_tree.length - 1 < c.top_tree.val.length := by
    simp [alloc.vec.Vec.length] at hne ⊢; omega
  rw [ha, getElem!_pos c.top_tree.val _ hlt]
  simp only [hi1, alloc.vec.Vec.length, alloc.vec.Vec.len_val]

/-- Under `CacheValid`, extracted `TopTreeCache::pk_root` returns the exact FIPS 205 `PK.root`. -/
theorem pk_root_eq_fips {N : Usize} {c : CacheopsRust.cache.TopTreeCache N} {p : Spec.Params}
    {sk_seed pk_seed : Spec.Bytes} (hc : CacheValid c p sk_seed pk_seed) :
    CacheopsRust.cache.TopTreeCache.pk_root c ⦃ r =>
      bytes r.val = Spec.xmssNode p sk_seed 0 p.hp pk_seed (layerAdrs (p.d - 1) 0) ⦄ := by
  apply WP.spec_mono (pk_root_spec c (by rw [hc.top_len]; exact treeSize_pos p.hp))
  intro r hr
  rw [hr]
  exact top_root_eq_fips hc

private theorem partialEqSlice_u8_spec (s1 s2 : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s1 s2 ⦃ b =>
      b = decide (s1.val = s2.val) ⦄ := by
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 s1 s2
    (fun x y => by simp))
  intro b hb
  have hiff : s1 = s2 ↔ s1.val = s2.val := ⟨congrArg Slice.val, Slice.ext s1 s2⟩
  rw [hiff] at hb
  cases b <;> simp_all

private theorem array_index_full_eq {T : Type} {N : Usize} (a : Array T N) :
    core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice T))
      a () = ok a.to_slice := rfl

/-- Extracted `TopTreeCache::matches_key` returns `true` iff `sk.length = 4 * N`,
`sk[2N..3N] = pk_seed`, and `sk[3N..4N] = pk_root`. -/
@[step]
theorem matches_key_spec {N : Usize} (c : CacheopsRust.cache.TopTreeCache N) (sk : Slice U8)
    (hne : 0 < c.top_tree.length) (hN : 4 * N.val ≤ Usize.max) :
    CacheopsRust.cache.TopTreeCache.matches_key c sk ⦃ b =>
      b = decide (sk.length = 4 * N.val ∧
        (sk.val.drop (2 * N.val)).take N.val = c.pk_seed.val ∧
        (sk.val.drop (3 * N.val)).take N.val = (c.top_tree.val[c.top_tree.length - 1]!).val) ⦄ := by
  unfold CacheopsRust.cache.TopTreeCache.matches_key
  step as ⟨i1, hi1⟩
  by_cases hlen : sk.length = 4 * N.val
  · have heq : Slice.len sk = i1 := UScalar.eq_of_val_eq (by rw [hi1]; exact hlen)
    simp only [heq, ↓reduceIte]
    step as ⟨i2, hi2⟩
    step as ⟨i3, hi3⟩
    step as ⟨s, hs, _⟩
    simp only [array_index_full_eq, bind_ok]
    step with partialEqSlice_u8_spec s c.pk_seed.to_slice as ⟨b, hb⟩
    have hs_eq : s.val = (sk.val.drop (2 * N.val)).take N.val := by
      rw [hs, List.slice, hi2, hi3, show 3 * N.val - 2 * N.val = N.val by omega]
    have hs1_eq : c.pk_seed.to_slice.val = c.pk_seed.val := Array.val_to_slice c.pk_seed
    by_cases hpk : (sk.val.drop (2 * N.val)).take N.val = c.pk_seed.val
    · have hb_true : b = true := by rw [hb, hs_eq, hs1_eq]; simp [hpk]
      simp only [hb_true, ↓reduceIte]
      step as ⟨s2, hs2, _⟩
      step with pk_root_spec c hne as ⟨a, ha⟩
      step with partialEqSlice_u8_spec s2 a.to_slice as ⟨b2, hb2⟩
      have hs2_eq : s2.val = (sk.val.drop (3 * N.val)).take N.val := by
        rw [hs2, List.slice, hi3, hi1, show 4 * N.val - 3 * N.val = N.val by omega]
      have hs3_eq : a.to_slice.val = (c.top_tree.val[c.top_tree.length - 1]!).val := by
        rw [Array.val_to_slice, ha]
      rw [hb2, hs2_eq, hs3_eq]
      by_cases hr : (sk.val.drop (3 * N.val)).take N.val =
          (c.top_tree.val[c.top_tree.length - 1]!).val <;> simp [hlen, hpk, hr]
    · have hb_false : b = false := by rw [hb, hs_eq, hs1_eq]; simp [hpk]
      simp [hb_false, hpk]
  · have hne_len : ¬ (Slice.len sk = i1) := by
      intro h; apply hlen; rw [← hi1]; exact congrArg UScalar.val h
    simp only [hne_len, ↓reduceIte, step_simps]
    simp [hlen]

/-- Specification-level characterization of `TopTreeCache::matches_key` in terms of
FIPS 205 key blocks `PK.seed = block sk 2` and `PK.root = block sk 3`. -/
theorem matches_key_iff_pk_eq {N : Usize} (c : CacheopsRust.cache.TopTreeCache N) (p : Spec.Params)
    (sk : Slice U8) (hn : p.n = N.val) (hne : 0 < c.top_tree.length) (hN : 4 * N.val ≤ Usize.max) :
    CacheopsRust.cache.TopTreeCache.matches_key c sk = ok true ↔
      sk.length = 4 * N.val ∧
      bytes c.pk_seed.val = Spec.block p (bytes sk.val) 2 ∧
      bytes (c.top_tree.val[c.top_tree.length - 1]!).val = Spec.block p (bytes sk.val) 3 := by
  obtain ⟨b, hb_eq, hb_spec⟩ := spec_imp_exists (matches_key_spec c sk hne hN)
  rw [hb_eq]
  have hblk2 : Spec.block p (bytes sk.val) 2 = bytes ((sk.val.drop (2 * N.val)).take N.val) := by
    simp [Spec.block, bytes, hn, List.map_take, List.map_drop]
  have hblk3 : Spec.block p (bytes sk.val) 3 = bytes ((sk.val.drop (3 * N.val)).take N.val) := by
    simp [Spec.block, bytes, hn, List.map_take, List.map_drop]
  constructor
  · intro hok
    have hbt : b = true := by
      have h := congrArg (fun r => r ⦃ fun x => x = true ⦄) hok
      simpa [WP.spec_ok] using h
    rw [hbt] at hb_spec
    have ⟨hl, hp2, hp3⟩ := of_decide_eq_true hb_spec.symm
    exact ⟨hl, by rw [hblk2, hp2], by rw [hblk3, hp3]⟩
  · rintro ⟨hl, hp2, hp3⟩
    have h2 : (sk.val.drop (2 * N.val)).take N.val = c.pk_seed.val :=
      ht_bytes_injective (by rw [← hblk2, hp2])
    have h3 : (sk.val.drop (3 * N.val)).take N.val = (c.top_tree.val[c.top_tree.length - 1]!).val :=
      ht_bytes_injective (by rw [← hblk3, hp3])
    have hbt : b = true := by rw [hb_spec]; simp [hl, h2, h3]
    rw [hbt]

/-- Key-Association Soundness: if `sk` is a well-formed FIPS 205 key (`Spec.KeyOk p sk`,
length `4 * N`) and `c` is a valid cache built from `sk`'s `SK.seed` and `PK.seed`, then:
1. `c.top_tree`'s root equals `PK.root = Spec.block p sk 3`, and
2. Extracted `TopTreeCache::matches_key c sk` returns `ok true`. -/
theorem matches_key_valid_key {N : Usize} (c : CacheopsRust.cache.TopTreeCache N) (p : Spec.Params)
    (sk : Slice U8) (hn : p.n = N.val) (hN : 4 * N.val ≤ Usize.max)
    (hsklen : sk.length = 4 * N.val)
    (hk : Spec.KeyOk p (bytes sk.val))
    (hc : CacheValid c p (Spec.block p (bytes sk.val) 0) (Spec.block p (bytes sk.val) 2)) :
    bytes (c.top_tree.val[c.top_tree.length - 1]!).val = Spec.block p (bytes sk.val) 3 ∧
    CacheopsRust.cache.TopTreeCache.matches_key c sk = ok true := by
  have hroot : bytes (c.top_tree.val[c.top_tree.length - 1]!).val =
      Spec.block p (bytes sk.val) 3 := by
    rw [top_root_eq_fips hc]
    exact hk.symm
  refine ⟨hroot, ?_⟩
  rw [matches_key_iff_pk_eq c p sk hn (by rw [hc.top_len]; exact treeSize_pos p.hp) hN]
  exact ⟨hsklen, hc.pk_seed_eq, hroot⟩

/-! ## Cache Reuse, Lookup, Insertion, MRU Move-to-Front, Eviction & Precomputation -/

/-- Any `lookup_cached_index` hit `some idx` on a `CacheValid` cache returns a valid index
whose entry has `tree_index = tree_d2`, length `2^(hp + 1) - 1`, and satisfies Dan's
`Built` (and therefore `TreeContents`) at `(layer = d - 2, tree = tree_d2)`. -/
theorem lookup_hit_built {N : Usize} {c : CacheopsRust.cache.TopTreeCache N} {p : Spec.Params}
    {sk_seed pk_seed : Spec.Bytes} (hc : CacheValid c p sk_seed pk_seed) (tree_d2 : U64) :
    CacheopsRust.cache.lookup_cached_index (alloc.vec.Vec.deref c.layer_d2) tree_d2 ⦃ r =>
      match r with
      | some idx =>
        ∃ hlt : idx.val < c.layer_d2.length,
          c.layer_d2.val[idx.val].tree_index = tree_d2 ∧
          c.layer_d2.val[idx.val].nodes.length = treeSize p.hp ∧
          slhdsa.cache.Built (alloc.vec.Vec.deref c.layer_d2.val[idx.val].nodes)
            p sk_seed pk_seed (layerAdrs (p.d - 2) tree_d2.val)
      | none =>
        ∀ e ∈ c.layer_d2.val, e.tree_index ≠ tree_d2 ⦄ := by
  unfold CacheopsRust.cache.lookup_cached_index
  apply WP.spec_mono (slhdsa.cache.lookup (toSearchSlice (alloc.vec.Vec.deref c.layer_d2)) tree_d2)
  intro r hr
  cases r with
  | none =>
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    have hi' : i < (toSearchSlice (alloc.vec.Vec.deref c.layer_d2)).length := by
      simp [toSearchSlice, Slice.length, vec_deref_val, hi]
    have hne := hr i hi'
    simpa [toSearchSlice, toSearchEntry, vec_deref_val] using hne
  | some idx =>
    obtain ⟨hlt, heq⟩ := hr
    have hlt' : idx.val < c.layer_d2.length := by
      simpa [toSearchSlice, Slice.length, alloc.vec.Vec.length, vec_deref_val] using hlt
    have heq' : c.layer_d2.val[idx.val].tree_index = tree_d2 := by
      simpa [toSearchSlice, toSearchEntry, vec_deref_val] using heq
    have hmem : c.layer_d2.val[idx.val] ∈ c.layer_d2.val := List.getElem_mem hlt'
    obtain ⟨hnlen, hnbuilt⟩ := hc.d2_built _ hmem
    rw [heq'] at hnbuilt
    exact ⟨hlt', heq', hnlen, hnbuilt⟩

/-- Extracted `TopTreeCache::lookup_d2` on a `CacheValid` cache returns `some tree` only when
`tree` has length `2^(hp + 1) - 1` and satisfies `Built` (and `TreeContents`) at
`(layer = d - 2, tree = tree_d2)`. -/
@[step]
theorem lookup_d2_spec {N : Usize} {c : CacheopsRust.cache.TopTreeCache N} {p : Spec.Params}
    {sk_seed pk_seed : Spec.Bytes} (hc : CacheValid c p sk_seed pk_seed) (tree_d2 : U64) :
    CacheopsRust.cache.TopTreeCache.lookup_d2 c tree_d2 ⦃ r =>
      match r with
      | some d2_tree =>
        d2_tree.length = treeSize p.hp ∧
        slhdsa.cache.Built d2_tree p sk_seed pk_seed (layerAdrs (p.d - 2) tree_d2.val)
      | none =>
        ∀ e ∈ c.layer_d2.val, e.tree_index ≠ tree_d2 ⦄ := by
  unfold CacheopsRust.cache.TopTreeCache.lookup_d2
  step with lookup_hit_built hc tree_d2 as ⟨o, ho⟩
  cases o with
  | none =>
    simp only [core.option.Option.map, WP.spec_ok]
    exact ho
  | some idx =>
    obtain ⟨hlt, _, hnlen, hnbuilt⟩ := ho
    simp only [core.option.Option.map,
      CacheopsRust.cache.TopTreeCache.lookup_d2.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeShared0SliceArrayU8N.call_once]
    have hget : alloc.vec.Vec.index
        (core.slice.index.SliceIndexUsizeSlice (CacheopsRust.cache.LayerD2Entry N))
        c.layer_d2 idx = ok c.layer_d2.val[idx.val] := by
      simp only [alloc.vec.Vec.index, Slice.index_usize, Slice.getElem?_Usize_eq, alloc.vec.Vec.val]
      have hlt' : idx.val < c.layer_d2.slice.val.length := hlt
      rw [List.getElem?_eq_getElem hlt']
    rw [hget]
    simp only [bind_ok, alloc.vec.Vec.as_slice, bind_tc_ok, WP.spec_ok]
    rw [vec_deref_len]
    exact ⟨hnlen, hnbuilt⟩

/-- Extracted `TopTreeCache::set_layer_d2_capacity` preserves `CacheValid` and enforces
the capacity bound `c'.layer_d2.length ≤ capacity.val`. -/
theorem set_capacity_preserves_valid {N : Usize} {c : CacheopsRust.cache.TopTreeCache N}
    {p : Spec.Params} {sk_seed pk_seed : Spec.Bytes}
    (hc : CacheValid c p sk_seed pk_seed) (capacity : Usize) :
    CacheopsRust.cache.TopTreeCache.set_layer_d2_capacity c capacity ⦃ c' =>
      CacheValid c' p sk_seed pk_seed ∧
      c'.layer_d2_capacity = capacity ∧
      c'.layer_d2.length ≤ capacity.val ⦄ := by
  unfold CacheopsRust.cache.TopTreeCache.set_layer_d2_capacity
  by_cases hgt : c.layer_d2.len > capacity
  · simp only [hgt, ↓reduceIte, alloc.vec.Vec.truncate, bind_ok, WP.spec_ok]
    refine ⟨{
      hp_eq := hc.hp_eq
      d_eq := hc.d_eq
      pk_seed_eq := hc.pk_seed_eq
      top_len := hc.top_len
      top_built := hc.top_built
      d2_built := fun e he => by
        simp only [alloc.vec.Vec.from_val] at he
        exact hc.d2_built e (List.mem_of_mem_take he)
    }, trivial, ?_⟩
    simp [alloc.vec.Vec.length]
  · simp only [hgt, ↓reduceIte, WP.spec_ok]
    refine ⟨{
      hp_eq := hc.hp_eq
      d_eq := hc.d_eq
      pk_seed_eq := hc.pk_seed_eq
      top_len := hc.top_len
      top_built := hc.top_built
      d2_built := hc.d2_built
    }, trivial, ?_⟩
    have : ¬ (c.layer_d2.length > capacity.val) := by
      simpa [alloc.vec.Vec.len_val] using hgt
    omega

/-- Extracted `TopTreeCache::with_layer_d2_capacity` preserves `CacheValid` and enforces
the capacity bound. -/
theorem with_capacity_preserves_valid {N : Usize} {c : CacheopsRust.cache.TopTreeCache N}
    {p : Spec.Params} {sk_seed pk_seed : Spec.Bytes}
    (hc : CacheValid c p sk_seed pk_seed) (capacity : Usize) :
    CacheopsRust.cache.TopTreeCache.with_layer_d2_capacity c capacity ⦃ c' =>
      CacheValid c' p sk_seed pk_seed ∧
      c'.layer_d2_capacity = capacity ∧
      c'.layer_d2.length ≤ capacity.val ⦄ :=
  set_capacity_preserves_valid hc capacity

/-- LRU tail eviction (`Vec::pop` = `List.dropLast`) and capacity truncation (`List.take`)
both preserve `CacheValid`. -/
theorem evict_preserves_valid {N : Usize} {c : CacheopsRust.cache.TopTreeCache N}
    {p : Spec.Params} {sk_seed pk_seed : Spec.Bytes}
    (hc : CacheValid c p sk_seed pk_seed) (cap : Nat) :
    let popped : alloc.vec.Vec (CacheopsRust.cache.LayerD2Entry N) :=
      alloc.vec.Vec.from c.layer_d2.val.dropLast (Nat.le_trans (by simp) c.layer_d2.property)
    let truncated : alloc.vec.Vec (CacheopsRust.cache.LayerD2Entry N) :=
      alloc.vec.Vec.from (c.layer_d2.val.take cap) (by simp [c.layer_d2.property])
    CacheValid { c with layer_d2 := popped } p sk_seed pk_seed ∧
    CacheValid { c with layer_d2 := truncated } p sk_seed pk_seed := by
  constructor
  · exact {
      hp_eq := hc.hp_eq
      d_eq := hc.d_eq
      pk_seed_eq := hc.pk_seed_eq
      top_len := hc.top_len
      top_built := hc.top_built
      d2_built := fun e he => by
        simp only [alloc.vec.Vec.from_val] at he
        exact hc.d2_built e (List.dropLast_subset _ he)
    }
  · exact {
      hp_eq := hc.hp_eq
      d_eq := hc.d_eq
      pk_seed_eq := hc.pk_seed_eq
      top_len := hc.top_len
      top_built := hc.top_built
      d2_built := fun e he => by
        simp only [alloc.vec.Vec.from_val] at he
        exact hc.d2_built e (List.mem_of_mem_take he)
    }

/-- MRU move-to-front (`remove pos` followed by `insert 0`, matching `lookup_or_populate_d2`
on a non-head cache hit) preserves `CacheValid`, entry membership, and length. -/
theorem move_to_front_preserves_valid {N : Usize} {c : CacheopsRust.cache.TopTreeCache N}
    {p : Spec.Params} {sk_seed pk_seed : Spec.Bytes}
    (hc : CacheValid c p sk_seed pk_seed) (pos : Nat) (hpos : pos < c.layer_d2.val.length) :
    let entry := c.layer_d2.val[pos]
    let reordered : List (CacheopsRust.cache.LayerD2Entry N) :=
      entry :: (c.layer_d2.val.eraseIdx pos)
    have hlen : reordered.length = c.layer_d2.val.length := by
      simp [reordered, List.length_eraseIdx_of_lt hpos]; omega
    let c' : CacheopsRust.cache.TopTreeCache N :=
      { c with layer_d2 := alloc.vec.Vec.from reordered (by rw [hlen]; exact c.layer_d2.property) }
    CacheValid c' p sk_seed pk_seed ∧
    c'.layer_d2.val.head? = some entry ∧
    c'.layer_d2.length = c.layer_d2.length := by
  intro entry reordered hlen c'
  refine ⟨{
    hp_eq := hc.hp_eq
    d_eq := hc.d_eq
    pk_seed_eq := hc.pk_seed_eq
    top_len := hc.top_len
    top_built := hc.top_built
    d2_built := by
      intro e he
      simp only [c', alloc.vec.Vec.from_val, reordered] at he
      rcases List.mem_cons.mp he with rfl | hrest
      · exact hc.d2_built _ (List.getElem_mem hpos)
      · exact hc.d2_built _ (List.mem_of_mem_eraseIdx hrest)
  }, ?_, ?_⟩
  · simp [c', alloc.vec.Vec.from_val, reordered]
  · simp [c', alloc.vec.Vec.length, alloc.vec.Vec.from_val, hlen]

/-- Inserting a freshly `Built` layer `d - 2` subtree at the front (with LRU tail eviction
when `len ≥ cap`, matching `lookup_or_populate_d2` on a cache miss) preserves `CacheValid`,
places the new subtree at index `0`, and maintains `len ≤ cap`. -/
theorem insert_preserves_valid {N : Usize} {c : CacheopsRust.cache.TopTreeCache N}
    {p : Spec.Params} {sk_seed pk_seed : Spec.Bytes}
    (hc : CacheValid c p sk_seed pk_seed)
    (tree_d2 : U64) (nodes : alloc.vec.Vec (Array U8 N))
    (hnodes_len : nodes.length = treeSize p.hp)
    (hnodes_built : slhdsa.cache.Built (alloc.vec.Vec.deref nodes) p sk_seed pk_seed
      (layerAdrs (p.d - 2) tree_d2.val))
    (hcap_pos : 0 < c.layer_d2_capacity.val)
    (hfit : (if c.layer_d2.val.length ≥ c.layer_d2_capacity.val
        then c.layer_d2.val.dropLast else c.layer_d2.val).length + 1 ≤ Usize.max) :
    let base := if c.layer_d2.val.length ≥ c.layer_d2_capacity.val
      then c.layer_d2.val.dropLast else c.layer_d2.val
    let newEntry : CacheopsRust.cache.LayerD2Entry N := ⟨tree_d2, nodes⟩
    let c' : CacheopsRust.cache.TopTreeCache N :=
      { c with layer_d2 := alloc.vec.Vec.from (newEntry :: base) (by simpa using hfit) }
    CacheValid c' p sk_seed pk_seed ∧
    c'.layer_d2.val.head? = some newEntry ∧
    (c.layer_d2.length ≤ c.layer_d2_capacity.val →
      c'.layer_d2.length ≤ c.layer_d2_capacity.val) := by
  intro base newEntry c'
  refine ⟨{
    hp_eq := hc.hp_eq
    d_eq := hc.d_eq
    pk_seed_eq := hc.pk_seed_eq
    top_len := hc.top_len
    top_built := hc.top_built
    d2_built := by
      intro e he
      simp only [c', alloc.vec.Vec.from_val] at he
      rcases List.mem_cons.mp he with rfl | hrest
      · exact ⟨hnodes_len, hnodes_built⟩
      · have hmem : e ∈ c.layer_d2.val := by
          dsimp only [base] at hrest
          split at hrest
          · exact List.dropLast_subset _ hrest
          · exact hrest
        exact hc.d2_built e hmem
  }, ?_, ?_⟩
  · simp [c', alloc.vec.Vec.from_val]
  · intro hle
    simp only [c', alloc.vec.Vec.length, alloc.vec.Vec.from_val, List.length_cons, base]
    split
    · simp only [List.length_dropLast]
      change c.layer_d2.val.length ≤ c.layer_d2_capacity.val at hle
      omega
    · change c.layer_d2.val.length ≤ c.layer_d2_capacity.val at hle
      omega

/-- Precomputing all `2^hp` layer `d - 2` subtrees (matching `TopTreeCache::precompute_layer_d2`)
preserves `CacheValid` and guarantees every `tree_d2 < 2^hp` is present at index `tree_d2`. -/
theorem precompute_d2_preserves_valid {N : Usize} {c : CacheopsRust.cache.TopTreeCache N}
    {p : Spec.Params} {sk_seed pk_seed : Spec.Bytes}
    (hc : CacheValid c p sk_seed pk_seed)
    (entries : alloc.vec.Vec (CacheopsRust.cache.LayerD2Entry N))
    (hcount : entries.length = 2 ^ p.hp)
    (hentries : ∀ i (hi : i < 2 ^ p.hp),
      let e := entries.val[i]'(by simpa [alloc.vec.Vec.length, hcount] using hi)
      e.tree_index.val = i ∧
      e.nodes.length = treeSize p.hp ∧
      slhdsa.cache.Built (alloc.vec.Vec.deref e.nodes) p sk_seed pk_seed
        (layerAdrs (p.d - 2) i))
    (new_cap : Usize) :
    let c' : CacheopsRust.cache.TopTreeCache N :=
      { c with layer_d2 := entries, layer_d2_capacity := new_cap }
    CacheValid c' p sk_seed pk_seed ∧
    ∀ tree_d2 : U64, tree_d2.val < 2 ^ p.hp →
      ∃ hlt : tree_d2.val < c'.layer_d2.length,
        c'.layer_d2.val[tree_d2.val].tree_index = tree_d2 := by
  intro c'
  refine ⟨{
    hp_eq := hc.hp_eq
    d_eq := hc.d_eq
    pk_seed_eq := hc.pk_seed_eq
    top_len := hc.top_len
    top_built := hc.top_built
    d2_built := by
      intro e he
      dsimp only [c'] at he
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      have hi' : i < 2 ^ p.hp := by simpa [alloc.vec.Vec.length, hcount] using hi
      obtain ⟨htidx, hnlen, hbuilt⟩ := hentries i hi'
      exact ⟨hnlen, by simpa [htidx] using hbuilt⟩
  }, ?_⟩
  intro tree_d2 hlt
  have hlt' : tree_d2.val < entries.length := by rw [hcount]; exact hlt
  refine ⟨hlt', ?_⟩
  obtain ⟨htidx, _, _⟩ := hentries tree_d2.val hlt
  exact UScalar.eq_of_val_eq htidx

/-! ## Extracted `digest_tree`, `digest_leaf`, and `layer_d2_tree_index` -/

private theorem to_int_eq : CacheopsRust.util.to_int = slhdsa.util.to_int := rfl
private theorem md_bytes_eq (p : CacheopsRust.params.Params) :
    CacheopsRust.params.Params.md_bytes p = slhdsa.params.Params.md_bytes (toSlhParams p) := rfl
private theorem tree_bytes_eq (p : CacheopsRust.params.Params) :
    CacheopsRust.params.Params.tree_bytes p = slhdsa.params.Params.tree_bytes (toSlhParams p) := rfl
private theorem tree_bits_eq (p : CacheopsRust.params.Params) :
    CacheopsRust.params.Params.tree_bits p = slhdsa.params.Params.tree_bits (toSlhParams p) := rfl
private theorem leaf_bytes_eq (p : CacheopsRust.params.Params) :
    CacheopsRust.params.Params.leaf_bytes p = slhdsa.params.Params.leaf_bytes (toSlhParams p) := rfl
private theorem sig_bytes_eq (p : CacheopsRust.params.Params) :
    CacheopsRust.params.Params.sig_bytes p = slhdsa.params.Params.sig_bytes (toSlhParams p) := by
  unfold CacheopsRust.params.Params.sig_bytes slhdsa.params.Params.sig_bytes
    CacheopsRust.params.Params.fors_sig_bytes slhdsa.params.Params.fors_sig_bytes
    CacheopsRust.params.Params.xmss_sig_bytes slhdsa.params.Params.xmss_sig_bytes
    CacheopsRust.params.Params.len slhdsa.params.Params.len
  simp only [CacheopsRust.params.LEN2, slhdsa.params.LEN2]

@[step]
theorem cache_digest_tree_spec (p : CacheopsRust.params.Params) (digest : Slice U8)
    (hv : (paramsS (toSlhParams p)).Valid) (h : digest.length = p.m.val) :
    CacheopsRust.cache.digest_tree p digest ⦃ r =>
      r.val = Spec.digestTree (paramsS (toSlhParams p)) (bytes digest.val) ∧
      r.val < 2 ^ (p.h.val - p.hp.val) ⦄ := by
  have heq : CacheopsRust.cache.digest_tree p digest =
      slhdsa.slh.digest_tree (toSlhParams p) digest := by
    unfold CacheopsRust.cache.digest_tree slhdsa.slh.digest_tree
    simp only [md_bytes_eq, tree_bytes_eq, tree_bits_eq, to_int_eq]
  rw [heq]
  exact slhdsa.digest_tree_spec (toSlhParams p) digest hv h

@[step]
theorem cache_digest_leaf_spec (p : CacheopsRust.params.Params) (digest : Slice U8)
    (hv : (paramsS (toSlhParams p)).Valid) (h : digest.length = p.m.val) :
    CacheopsRust.cache.digest_leaf p digest ⦃ r =>
      r.val = Spec.digestLeaf (paramsS (toSlhParams p)) (bytes digest.val) ∧
      r.val < 2 ^ p.hp.val ⦄ := by
  have heq : CacheopsRust.cache.digest_leaf p digest =
      slhdsa.slh.digest_leaf (toSlhParams p) digest := by
    unfold CacheopsRust.cache.digest_leaf slhdsa.slh.digest_leaf
    simp only [md_bytes_eq, tree_bytes_eq, leaf_bytes_eq, to_int_eq, toSlhParams]
  rw [heq]
  exact slhdsa.digest_leaf_spec (toSlhParams p) digest hv h

/-- Extracted `TopTreeCache::layer_d2_tree_index` computes the exact layer `d - 2`
tree index `idx_tree >>> ((d - 2) * hp)`. -/
@[step]
theorem layer_d2_tree_index_spec (N : Usize) (p : CacheopsRust.params.Params) (digest : Slice U8)
    (hv : (paramsS (toSlhParams p)).Valid) (h : digest.length = p.m.val) :
    CacheopsRust.cache.TopTreeCache.layer_d2_tree_index N p digest ⦃ r =>
      r.val = Spec.digestTree (paramsS (toSlhParams p)) (bytes digest.val) >>>
        ((p.d.val - 2) * p.hp.val) ⦄ := by
  have hd : 2 ≤ p.d.val := hv.d_ge
  have hhp : p.hp.val ≤ 9 := hv.hp_le
  have htree_le : p.h.val - p.hp.val ≤ 64 := hv.tree_le
  have h_eq : p.h.val = p.d.val * p.hp.val := hv.h_eq
  have hshift_lt : (p.d.val - 2) * p.hp.val < 64 := by
    have : (p.d.val - 2) * p.hp.val + p.hp.val = p.h.val - p.hp.val := by
      rw [h_eq]; cases hdv : p.d.val with
      | zero => omega
      | succ d' => cases d' with
        | zero => omega
        | succ d'' => simp [Nat.add_mul]
    have hhp_pos : 1 ≤ p.hp.val := hv.hp_pos
    omega
  unfold CacheopsRust.cache.TopTreeCache.layer_d2_tree_index
  have hnotlt : ¬ (p.d < 2#u32) := by scalar_tac
  simp only [hnotlt, ↓reduceIte]
  step with cache_digest_tree_spec p digest hv h as ⟨idx_tree, hidx_eq, _⟩
  step as ⟨i, hi⟩
  step as ⟨i1, hi1⟩
  step as ⟨r, hr, _⟩
  rw [hr, hidx_eq, hi1, hi]

/-! ## Extracted `sha2_ops::sign_from_digest` composing with Dan's `Cachepath.Construction` -/

private theorem append_auth_path_of_built {N : Usize} (P : Spec.Params)
    (skSeed pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (tree : Slice (Array U8 N)) (hp leaf : U32) (out : alloc.vec.Vec U8)
    (hhp_eq : hp.val = P.hp) (hhp_le : P.hp ≤ 9) (hleaf : leaf.val < 2 ^ P.hp)
    (hsize : tree.length = treeSize P.hp)
    (hbuilt : slhdsa.cache.Built tree P skSeed pkSeed adrs)
    (hroom : out.length + P.hp * N.val ≤ Usize.max) :
    CacheopsRust.cache.append_auth_path tree hp leaf out ⦃ r =>
      bytes r.val = bytes out.val ++
        (List.range P.hp).flatMap (fun h =>
          Spec.xmssNode P skSeed ((leaf.val / 2 ^ h) ^^^ 1) h pkSeed adrs) ∧
      r.length = out.length + P.hp * N.val ⦄ := by
  unfold CacheopsRust.cache.append_auth_path
  have htc := slhdsa.cache.constructed hbuilt
  apply WP.spec_mono (slhdsa.cache.path tree hp leaf out (by omega)
    (by rw [hhp_eq]; exact hleaf) (by rw [hhp_eq]; exact hsize) (by rw [hhp_eq]; exact hroom))
  intro r hr
  have hbytes : bytes r.val = bytes out.val ++
      (List.range P.hp).flatMap (fun h =>
        Spec.xmssNode P skSeed ((leaf.val / 2 ^ h) ^^^ 1) h pkSeed adrs) := by
    rw [hr, bytes_append]
    congr 1
    simp only [bytes, List.map_flatMap, hhp_eq]
    apply List.flatMap_congr
    intro h mem
    have live := List.mem_range.mp mem
    have split : 2 ^ P.hp = 2 ^ (P.hp - h) * 2 ^ h := by
      rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have sel : leaf.val < 2 ^ (P.hp - h) * 2 ^ h := by rwa [← split]
    have digit := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).2 sel
    have one : 1 < 2 ^ (P.hp - h) := lt_of_lt_of_le (by decide : 1 < 2 ^ 1)
      (Nat.pow_le_pow_right (by decide) (by omega))
    simpa [slhdsa.cache.pathIndex, Nat.shiftRight_eq_div_pow, bytes] using
      htc h (by omega) _ (Nat.xor_lt_two_pow digit one)
  have hlen : r.length = out.length + P.hp * N.val := by
    have := congrArg List.length hr
    simp only [alloc.vec.Vec.length, List.length_append, List.length_flatMap, hhp_eq] at this ⊢
    rw [this]
    congr 1
    have hmap : (List.range P.hp).map
        (fun h => (tree.val[slhdsa.cache.pathIndex P.hp leaf.val h]!).val.length) =
        List.replicate P.hp N.val := by
      apply List.ext_getElem
      · simp
      · intro i hi _; simp
    rw [hmap, List.sum_replicate, smul_eq_mul]
  exact ⟨hbytes, hlen⟩

private theorem htLayer_state (P : Spec.Params) (_hv : P.Valid) (sk pk m : Spec.Bytes)
    (t l : Nat) (hl : l < 2 ^ P.hp) :
    ∀ c, c ≤ P.d →
      let st := (List.range c).foldl (Spec.htLayer P sk pk) ([], m, t, l)
      st.2.2.1 = t >>> (P.hp * c) ∧ st.2.2.2 < 2 ^ P.hp := by
  intro c
  induction c with
  | zero => intro _; simp [hl]
  | succ c ih =>
    intro hc
    rw [List.range_succ, List.foldl_append]
    obtain ⟨ht, _⟩ := ih (by omega)
    generalize (List.range c).foldl (Spec.htLayer P sk pk) ([], m, t, l) = st at ht ⊢
    obtain ⟨sig, root, tree, leaf⟩ := st
    simp only at ht
    subst ht
    simp only [List.foldl_cons, List.foldl_nil, Spec.htLayer]
    exact ⟨by rw [Nat.mul_succ, Nat.shiftRight_add], Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private theorem sign_from_digest_loop_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (sk_seed : Array U8 N) (seed : CacheopsRust.hash.Seed N) (hs : SeedOk (toSlhSeed seed))
    (top_tree : Slice (Array U8 N)) (layer_d2_hit : Option (Slice (Array U8 N)))
    (root0 : Array U8 N) (sig0 : alloc.vec.Vec U8) (idx_tree : U64) (idx_leaf : U32)
    (htree_lt : idx_tree.val < 2 ^ (p.h.val - p.hp.val))
    (hleaf_lt : idx_leaf.val < 2 ^ p.hp.val)
    (hsig0_len : sig0.length = N.val + p.k.val * (1 + p.a.val) * N.val)
    (htop_len : top_tree.length = treeSize p.hp.val)
    (htop : slhdsa.cache.Built top_tree (paramsS (toSlhParams p)) (bytes sk_seed.val)
      (bytes seed.pk_seed.val) (layerAdrs (p.d.val - 1) 0))
    (hd2 : ∀ d2, layer_d2_hit = some d2 →
      d2.length = treeSize p.hp.val ∧
      slhdsa.cache.Built d2 (paramsS (toSlhParams p)) (bytes sk_seed.val)
        (bytes seed.pk_seed.val)
        (layerAdrs (p.d.val - 2) (idx_tree.val >>> ((p.d.val - 2) * p.hp.val)))) :
    CacheopsRust.cache.sha2_ops.sign_from_digest_loop
      ⟨0#u32, 0#u64, 0#u32, 0#u32, 0#u32, 0#u32⟩
      { start := 0#u32, «end» := p.d }
      p.n p.h p.d p.hp p.a p.k p.m
      sk_seed top_tree layer_d2_hit seed root0 sig0 idx_tree idx_leaf ⦃ sig =>
        bytes sig.val = bytes sig0.val ++
          Spec.htSign (paramsS (toSlhParams p)) (bytes root0.val)
            (bytes sk_seed.val) (bytes seed.pk_seed.val) idx_tree.val idx_leaf.val ⦄ := by
  let P := paramsS (toSlhParams p)
  have hv : P.Valid := hp.valid
  have hn := hp.le32
  have hd_ge : 2 ≤ p.d.val := hv.d_ge
  have hd_le : p.d.val ≤ 22 := hv.d_le
  have hhp_pos : 1 ≤ p.hp.val := hv.hp_pos
  have hhp_le : p.hp.val ≤ 9 := hv.hp_le
  have h_eq : p.h.val = p.d.val * p.hp.val := hv.h_eq
  have hfl : p.k.val * (1 + p.a.val) * N.val ≤ 16800 := fors_len_le (toSlhParams p) hp
  have hhl : p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) ≤ 53504 := ht_len_le (toSlhParams p) hp
  have hu := usize_max_ge
  have hpow_hp : 2 ^ p.hp.val ≤ 2 ^ 9 := two_pow_le_two_pow hhp_le
  have hpow_pos : 1 ≤ 2 ^ p.hp.val := Nat.two_pow_pos _
  have htop_tree_zero : idx_tree.val >>> (p.hp.val * (p.d.val - 1)) = 0 := by
    have hmul : p.h.val - p.hp.val = p.hp.val * (p.d.val - 1) := by
      rw [h_eq, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    rw [Nat.shiftRight_eq_div_pow, ← hmul]
    exact Nat.div_eq_of_lt htree_lt
  unfold CacheopsRust.cache.sha2_ops.sign_from_digest_loop
  apply loop.spec_decr_nat
    (measure := fun (q : core.ops.range.Range U32 × Option (Slice (Array U8 N)) × Array U8 N ×
      alloc.vec.Vec U8 × U64 × U32) => p.d.val - q.1.start.val)
    (inv := fun q =>
      q.1.end = p.d ∧ q.1.start.val ≤ p.d.val ∧ q.2.1 = layer_d2_hit ∧
      let st := (List.range q.1.start.val).foldl
        (Spec.htLayer P (bytes sk_seed.val) (bytes seed.pk_seed.val))
        ([], bytes root0.val, idx_tree.val, idx_leaf.val)
      bytes q.2.2.2.1.val = bytes sig0.val ++ st.1 ∧
      q.2.2.2.1.length = sig0.length + q.1.start.val * ((2 * N.val + 3 + p.hp.val) * N.val) ∧
      (q.1.start.val < p.d.val → bytes q.2.2.1.val = st.2.1) ∧
      q.2.2.2.2.1.val = st.2.2.1 ∧
      q.2.2.2.2.2.val = st.2.2.2 ∧
      q.2.2.2.2.2.val < 2 ^ p.hp.val)
  · rintro ⟨it, d2Opt, curRoot, curSig, curTree, curLeaf⟩
      ⟨hend, hle, hd2_eq, hsig_inv, hlen_inv, hroot_inv, htree_inv, hleaf_inv, hleaf_bd⟩
    simp only at hend hle hd2_eq hsig_inv hlen_inv hroot_inv htree_inv hleaf_inv hleaf_bd ⊢
    subst d2Opt
    unfold CacheopsRust.cache.sha2_ops.sign_from_digest_loop.body
    by_cases hlt : it.start.val < p.d.val
    · obtain ⟨⟨o, next⟩, hget, ho, hstart, hend'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_U32_some_spec it (by rw [hend]; exact hlt))
      subst o
      rw [hget]
      simp only [bind_ok, CacheopsRust.address.Adrs.with_layer, CacheopsRust.address.Adrs.with_tree]
      step as ⟨i7, hi7⟩
      have hroot_eq : bytes curRoot.val =
          ((List.range it.start.val).foldl
            (Spec.htLayer P (bytes sk_seed.val) (bytes seed.pk_seed.val))
            ([], bytes root0.val, idx_tree.val, idx_leaf.val)).2.1 := hroot_inv hlt
      have htree_shift : curTree.val = idx_tree.val >>> (p.hp.val * it.start.val) := by
        rw [htree_inv]
        exact (htLayer_state P hv (bytes sk_seed.val) (bytes seed.pk_seed.val)
          (bytes root0.val) idx_tree.val idx_leaf.val hleaf_lt it.start.val
          (by show it.start.val ≤ p.d.val; omega)).1
      have hcur_adrs : adrsS (toSlhAdrs ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩) =
          { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } := rfl
      have hlen_bound : curSig.length + (2 * N.val + 3 + p.hp.val) * N.val ≤ Usize.max := by
        have hstep_le : (it.start.val + 1) * ((2 * N.val + 3 + p.hp.val) * N.val) ≤
            p.d.val * ((2 * N.val + 3 + p.hp.val) * N.val) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at hstep_le
        omega
      have hstep_branch :
          (if it.start = i7 then do
              let a2 ← CacheopsRust.address.Adrs.with_type
                ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩ CacheopsRust.address.WOTS_HASH
              let a3 ← CacheopsRust.address.Adrs.with_keypair a2 curLeaf
              let wots ← CacheopsRust.wots.wots_sign curRoot sk_seed seed a3
              let s := alloc.vec.Vec.deref wots
              let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s
              let sig3 ← CacheopsRust.cache.append_auth_path top_tree p.hp curLeaf sig2
              ok (layer_d2_hit, curRoot, sig3, next)
            else do
              let i8 ← it.start + 2#u32
              if i8 = p.d then
                let (a2, v) ← match layer_d2_hit with
                  | none => do
                      let s ← CacheopsRust.xmss.xmss_sign
                        { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                        curRoot sk_seed curLeaf seed
                        ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                      let s1 := alloc.vec.Vec.deref s
                      let root2 ← CacheopsRust.xmss.xmss_pk_from_sig
                        { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                        curLeaf s1 curRoot seed
                        ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                      let s2 := alloc.vec.Vec.deref s
                      let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s2
                      ok (root2, sig2)
                  | some d2_tree => do
                      let a3 ← CacheopsRust.address.Adrs.with_type
                        ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩ CacheopsRust.address.WOTS_HASH
                      let a4 ← CacheopsRust.address.Adrs.with_keypair a3 curLeaf
                      let wots ← CacheopsRust.wots.wots_sign curRoot sk_seed seed a4
                      let s := alloc.vec.Vec.deref wots
                      let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s
                      let sig3 ← CacheopsRust.cache.append_auth_path d2_tree p.hp curLeaf sig2
                      let root2 ← CacheopsRust.cache.tree_root d2_tree
                      ok (root2, sig3)
                ok (layer_d2_hit, a2, v, next)
              else do
                let s ← CacheopsRust.xmss.xmss_sign
                  { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                  curRoot sk_seed curLeaf seed
                  ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                let s1 := alloc.vec.Vec.deref s
                let root2 ← CacheopsRust.xmss.xmss_pk_from_sig
                  { n := p.n, h := p.h, d := p.d, hp := p.hp, a := p.a, k := p.k, m := p.m }
                  curLeaf s1 curRoot seed
                  ⟨it.start, curTree, 0#u32, 0#u32, 0#u32, 0#u32⟩
                let s2 := alloc.vec.Vec.deref s
                let sig2 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 curSig s2
                ok (layer_d2_hit, root2, sig2, next)) ⦃ res =>
            res.1 = layer_d2_hit ∧ res.2.2.2 = next ∧
            let adrsS_cur : Spec.Adrs :=
              { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val }
            let xsig := Spec.xmssSign P (bytes curRoot.val) (bytes sk_seed.val) curLeaf.val
              (bytes seed.pk_seed.val) adrsS_cur
            bytes res.2.2.1.val = bytes curSig.val ++ xsig ∧
            res.2.2.1.length = curSig.length + (2 * N.val + 3 + p.hp.val) * N.val ∧
            (it.start.val + 1 < p.d.val →
              bytes res.2.1.val = Spec.xmssPkFromSig P curLeaf.val xsig (bytes curRoot.val)
                (bytes seed.pk_seed.val) adrsS_cur) ⦄ := by
        by_cases htop_case : it.start = i7
        · simp only [htop_case, ↓reduceIte, CacheopsRust.address.Adrs.with_type,
            CacheopsRust.address.Adrs.with_keypair, bind_ok]
          have hlayer_eq : it.start.val = p.d.val - 1 := by rw [htop_case, hi7]
          have htree0 : curTree.val = 0 := by rw [htree_shift, hlayer_eq, htop_tree_zero]
          step with slhdsa.wots_sign_spec (toSlhParams p) hp curRoot sk_seed (toSlhSeed seed) hs
            as ⟨wots, hwots_bytes, hwots_len⟩
          have hwots_room : curSig.length + (alloc.vec.Vec.deref wots).length ≤ Usize.max := by
            simp only [vec_deref_len, hwots_len]
            have hmc : N.val * (2 * N.val + 3) = (2 * N.val + 3) * N.val := Nat.mul_comm _ _
            have : (2 * N.val + 3) * N.val ≤ (2 * N.val + 3 + p.hp.val) * N.val :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref wots) hwots_room
            as ⟨sig2, hsig2_val, hsig2_len⟩
          have hap_room : sig2.length + P.hp * N.val ≤ Usize.max := by
            rw [hsig2_len, vec_deref_len, hwots_len]
            have : N.val * (2 * N.val + 3) + p.hp.val * N.val =
                (2 * N.val + 3 + p.hp.val) * N.val := by ring
            simp only [P, paramsS_hp]; omega
          have htop' : slhdsa.cache.Built top_tree P (bytes sk_seed.val) (bytes seed.pk_seed.val)
              { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } := by
            simpa [layerAdrs, hlayer_eq, htree0] using htop
          step with append_auth_path_of_built P (bytes sk_seed.val) (bytes seed.pk_seed.val)
            { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val }
            top_tree p.hp curLeaf sig2 rfl hhp_le hleaf_bd htop_len htop' hap_room
            as ⟨sig3, hsig3_bytes, hsig3_len⟩
          refine ⟨?_, ?_, fun hbad => by omega⟩
          · rw [hsig3_bytes, hsig2_val, bytes_append, vec_deref_val, hwots_bytes]
            simp only [Spec.xmssSign, List.append_assoc, adrsS,
              Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, CacheopsRust.address.WOTS_HASH,
              Spec.Adrs.zero, htop_case]
            rfl
          · rw [hsig3_len, hsig2_len, vec_deref_len, hwots_len]
            simp only [paramsS_hp]; ring
        · simp only [htop_case, ↓reduceIte]
          have hlt_top : it.start.val + 1 < p.d.val := by
            have : it.start.val ≠ p.d.val - 1 := by
              intro h; apply htop_case; apply UScalar.eq_of_val_eq; omega
            omega
          step as ⟨i8, hi8⟩
          by_cases hd2_case : i8 = p.d
          · simp only [hd2_case, ↓reduceIte]
            have hlayer_d2 : it.start.val = p.d.val - 2 := by
              have : i8.val = p.d.val := congrArg UScalar.val hd2_case
              omega
            cases hopt : layer_d2_hit with
            | none =>
              simp only
              step with slhdsa.xmss_sign_spec (toSlhParams p) hp curRoot sk_seed curLeaf
                (toSlhSeed seed) hs _ hleaf_bd as ⟨s, hs_bytes, hs_len⟩
              step with slhdsa.xmss_pk_from_sig_spec (toSlhParams p) hp curLeaf
                (alloc.vec.Vec.deref s) curRoot (toSlhSeed seed) hs _
                (by rw [vec_deref_len, hs_len]) hleaf_bd as ⟨root2, hroot2⟩
              step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref s)
                (by rw [vec_deref_len, hs_len]; exact hlen_bound)
                as ⟨sig2, hsig2_val, hsig2_len⟩
              refine ⟨?_, ?_, fun _ => ?_⟩
              · rw [hsig2_val, bytes_append, vec_deref_val, hs_bytes, hcur_adrs]
              · rw [hsig2_len, vec_deref_len, hs_len]
              · rw [hroot2, vec_deref_val, hs_bytes, hcur_adrs]
            | some d2_tree =>
              simp only [CacheopsRust.address.Adrs.with_type, CacheopsRust.address.Adrs.with_keypair,
                bind_ok]
              obtain ⟨hd2_len, hd2_built⟩ := hd2 d2_tree hopt
              have htree_d2 : curTree.val = idx_tree.val >>> ((p.d.val - 2) * p.hp.val) := by
                rw [htree_shift, hlayer_d2, Nat.mul_comm]
              have hd2_built' : slhdsa.cache.Built d2_tree P (bytes sk_seed.val)
                  (bytes seed.pk_seed.val)
                  { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } := by
                simpa [layerAdrs, hlayer_d2, htree_d2] using hd2_built
              step with slhdsa.wots_sign_spec (toSlhParams p) hp curRoot sk_seed (toSlhSeed seed) hs
                as ⟨wots, hwots_bytes, hwots_len⟩
              have hwots_room : curSig.length + (alloc.vec.Vec.deref wots).length ≤ Usize.max := by
                simp only [vec_deref_len, hwots_len]
                have hmc : N.val * (2 * N.val + 3) = (2 * N.val + 3) * N.val := Nat.mul_comm _ _
                have : (2 * N.val + 3) * N.val ≤ (2 * N.val + 3 + p.hp.val) * N.val :=
                  Nat.mul_le_mul_right _ (by omega)
                omega
              step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref wots) hwots_room
                as ⟨sig2, hsig2_val, hsig2_len⟩
              have hap_room : sig2.length + P.hp * N.val ≤ Usize.max := by
                rw [hsig2_len, vec_deref_len, hwots_len]
                have : N.val * (2 * N.val + 3) + p.hp.val * N.val =
                    (2 * N.val + 3 + p.hp.val) * N.val := by ring
                simp only [P, paramsS_hp]; omega
              step with append_auth_path_of_built P (bytes sk_seed.val) (bytes seed.pk_seed.val)
                { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val }
                d2_tree p.hp curLeaf sig2 rfl hhp_le hleaf_bd hd2_len hd2_built' hap_room
                as ⟨sig3, hsig3_bytes, hsig3_len⟩
              step with slhdsa.cache.root d2_tree (by rw [hd2_len]; exact treeSize_pos p.hp.val)
                as ⟨root2, hroot2⟩
              refine ⟨?_, ?_, fun _ => ?_⟩
              · rw [hsig3_bytes, hsig2_val, bytes_append, vec_deref_val, hwots_bytes]
                simp only [Spec.xmssSign, List.append_assoc, adrsS,
                  Spec.Adrs.setTypeAndClear, Spec.WOTS_HASH, CacheopsRust.address.WOTS_HASH,
                  Spec.Adrs.zero]
                rfl
              · rw [hsig3_len, hsig2_len, vec_deref_len, hwots_len]
                simp only [paramsS_hp]; ring
              · rw [hroot2, built_root_eq_fips hd2_len hd2_built']
                exact (Spec.xmss_correct P hv (bytes curRoot.val) (bytes sk_seed.val)
                  (bytes seed.pk_seed.val) curLeaf.val
                  { Spec.Adrs.zero with layer := it.start.val, tree := curTree.val } hleaf_bd).symm
          · simp only [hd2_case, ↓reduceIte]
            step with slhdsa.xmss_sign_spec (toSlhParams p) hp curRoot sk_seed curLeaf
              (toSlhSeed seed) hs _ hleaf_bd as ⟨s, hs_bytes, hs_len⟩
            step with slhdsa.xmss_pk_from_sig_spec (toSlhParams p) hp curLeaf
              (alloc.vec.Vec.deref s) curRoot (toSlhSeed seed) hs _
              (by rw [vec_deref_len, hs_len]) hleaf_bd as ⟨root2, hroot2⟩
            step with xmss_extend_u8_spec curSig (alloc.vec.Vec.deref s)
              (by rw [vec_deref_len, hs_len]; exact hlen_bound)
              as ⟨sig2, hsig2_val, hsig2_len⟩
            refine ⟨?_, ?_, fun _ => ?_⟩
            · rw [hsig2_val, bytes_append, vec_deref_val, hs_bytes, hcur_adrs]
            · rw [hsig2_len, vec_deref_len, hs_len]
            · rw [hroot2, vec_deref_val, hs_bytes, hcur_adrs]
      have hbind : ∀ {α β : Type} {x : Result α} {f : α → Result β} {P_a : α → Prop} {Q_b : β → Prop},
          x ⦃ P_a ⦄ → (∀ a, P_a a → f a ⦃ Q_b ⦄) → (Std.bind x f) ⦃ Q_b ⦄ := by
        intro α β x f P_a Q_b hx hf
        obtain ⟨a, rfl, ha⟩ := spec_imp_exists hx
        simpa [bind_ok] using hf a ha
      apply hbind hstep_branch
      rintro ⟨d2', root1, sig1, iter2⟩ ⟨hd2', hiter2, hsig1_bytes, hsig1_len, hroot1⟩
      dsimp only at hd2' hiter2 hsig1_bytes hsig1_len hroot1 ⊢
      step as ⟨i8, hi8⟩
      have hi8' : i8.val = 2 ^ p.hp.val := by
        rw [hi8, Nat.one_shiftLeft]
        apply Nat.mod_eq_of_lt; simp [U64.size, U64.numBits]; omega
      step as ⟨i9, hi9⟩
      have hi9' : i9.val = 2 ^ p.hp.val - 1 := by rw [hi9, hi8']
      step as ⟨i10, hi10, _⟩
      have hi10' : i10.val = curTree.val % 2 ^ p.hp.val := by
        rw [hi10, and_mask_val _ _ _ hi9']
      have hi10_lt : i10.val < 2 ^ p.hp.val := by
        rw [hi10']; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      step as ⟨leaf1, hleaf1⟩
      have hleaf1_val : leaf1.val = curTree.val % 2 ^ p.hp.val := by
        have h32 : 2 ^ 9 < 2 ^ UScalarTy.U32.numBits := by simp [UScalarTy.numBits]
        rw [hleaf1, UScalar.cast_val_eq, hi10']
        exact Nat.mod_eq_of_lt (by omega)
      step as ⟨tree1, htree1, _⟩
      subst hiter2 hd2'
      refine ⟨hend'.trans hend, by omega, rfl, ?_, ?_, ?_, ?_, ?_, ?_, by omega⟩
      · rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer]
        rw [hsig1_bytes, hsig_inv, hroot_eq, htree_inv, hleaf_inv, List.append_assoc]
      · rw [hsig1_len, hlen_inv, hstart]; ring
      · intro hnext_lt
        rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer]
        rw [hroot1 (by omega), hroot_eq, htree_inv, hleaf_inv]
      · rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer, htree1, htree_inv]; rfl
      · rw [hstart, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [Spec.htLayer, hleaf1_val, htree_inv]; rfl
      · rw [hleaf1_val]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · step with core.iter.range.IteratorRange.next_U32_none_spec it
          (by rw [hend]; exact Nat.not_lt.mp hlt) as ⟨o, next, ho, _⟩
      simp only [ho, step_simps]
      have heq : it.start.val = p.d.val := by omega
      rw [hsig_inv, heq]
      rfl
  · exact ⟨rfl, Nat.zero_le _, rfl, by simp, by simp, fun _ => rfl, rfl, rfl, hleaf_lt⟩

/-- Extracted Rust `cache::sha2_ops::sign_from_digest` produces the EXACT FIPS 205
`Spec.slhSignInternal` signature byte string when supplied with `Built` cached trees. -/
theorem sign_from_digest_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (sk_seed pk_seed r : Array U8 N) (digest : Slice U8)
    (top_tree : Slice (Array U8 N)) (layer_d2_hit : Option (Slice (Array U8 N)))
    (hdig : digest.length = p.m.val)
    (htop_len : top_tree.length = treeSize p.hp.val)
    (htop : slhdsa.cache.Built top_tree (paramsS (toSlhParams p)) (bytes sk_seed.val)
      (bytes pk_seed.val) (layerAdrs (p.d.val - 1) 0))
    (hd2 : ∀ d2, layer_d2_hit = some d2 →
      d2.length = treeSize p.hp.val ∧
      slhdsa.cache.Built d2 (paramsS (toSlhParams p)) (bytes sk_seed.val)
        (bytes pk_seed.val)
        (layerAdrs (p.d.val - 2)
          (Spec.digestTree (paramsS (toSlhParams p)) (bytes digest.val) >>>
            ((p.d.val - 2) * p.hp.val)))) :
    CacheopsRust.cache.sha2_ops.sign_from_digest p sk_seed pk_seed r digest top_tree layer_d2_hit ⦃ sig =>
      let P := paramsS (toSlhParams p)
      let md := (bytes digest.val).take P.mdBytes
      let idxTree := Spec.digestTree P (bytes digest.val)
      let idxLeaf := Spec.digestLeaf P (bytes digest.val)
      let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear
        Spec.FORS_TREE with keypair := idxLeaf }
      let sigFors := Spec.forsSign P md (bytes sk_seed.val) (bytes pk_seed.val) adrs
      let pkFors := Spec.forsPkFromSig P sigFors md (bytes pk_seed.val) adrs
      bytes sig.val = bytes r.val ++ sigFors ++
        Spec.htSign P pkFors (bytes sk_seed.val) (bytes pk_seed.val) idxTree idxLeaf ⦄ := by
  have hv := hp.valid
  have hn := hp.le32
  have hfl : p.k.val * (1 + p.a.val) * N.val ≤ 16800 := fors_len_le (toSlhParams p) hp
  have hu := usize_max_ge
  unfold CacheopsRust.cache.sha2_ops.sign_from_digest
  step with cache_digest_tree_spec p digest hv hdig as ⟨idx_tree, hidx_tree, hidx_tree_lt⟩
  step with cache_digest_leaf_spec p digest hv hdig as ⟨idx_leaf, hidx_leaf, hidx_leaf_lt⟩
  simp only [CacheopsRust.address.Adrs.new, CacheopsRust.address.Adrs.with_tree,
    CacheopsRust.address.Adrs.with_type, CacheopsRust.address.Adrs.with_keypair, bind_ok]
  step with slhdsa.seed_ctx_spec hp.nok pk_seed as ⟨seed0, hseed_pk, hseed_ok⟩
  have hpk_bytes : bytes (fromSlhSeed seed0).pk_seed.val = bytes pk_seed.val := by
    simp [hseed_pk]
  have hmd_eq : CacheopsRust.params.Params.md_bytes p =
      slhdsa.params.Params.md_bytes (toSlhParams p) := rfl
  rw [hmd_eq]
  step with slhdsa.md_bytes_spec (toSlhParams p) hv as ⟨i, hi_eq, hi_le⟩
  have hmd_le : i.val ≤ digest.length := by
    have hm := hv.m_eq
    have hmd_lt : (paramsS (toSlhParams p)).mdBytes ≤ (paramsS (toSlhParams p)).m := by omega
    rw [hi_eq, hdig]; exact hmd_lt
  step as ⟨md, hmd_val, hmd_len⟩
  step with slhdsa.fors_sign_spec (toSlhParams p) hp md sk_seed (toSlhSeed (fromSlhSeed seed0))
    hseed_ok _ (by rw [hmd_len, hi_eq]; rfl) as ⟨sig_fors, hsf_bytes, hsf_len⟩
  step with slhdsa.fors_pk_from_sig_spec (toSlhParams p) hp (alloc.vec.Vec.deref sig_fors) md
    (toSlhSeed (fromSlhSeed seed0)) hseed_ok _ (by rw [vec_deref_len, hsf_len])
    (by rw [hmd_len, hi_eq]; rfl) as ⟨root, hroot_bytes⟩
  rw [sig_bytes_eq]
  step with slhdsa.sig_bytes_spec (toSlhParams p) hv as ⟨i1, _⟩
  step as ⟨s1, hs1⟩
  step with xmss_extend_u8_spec (alloc.vec.Vec.with_capacity U8 i1) s1
    (by simp [alloc.vec.Vec.with_capacity, hs1]; omega) as ⟨sig1, hsig1_val, hsig1_l⟩
  step with xmss_extend_u8_spec sig1 (alloc.vec.Vec.deref sig_fors)
    (by simp [hsig1_l, alloc.vec.Vec.with_capacity, hs1, hsf_len]; omega)
    as ⟨sig2, hsig2_val, hsig2_l⟩
  have hsig2_len : sig2.length = N.val + p.k.val * (1 + p.a.val) * N.val := by
    rw [hsig2_l, hsig1_l, vec_deref_len, hsf_len]
    simp [alloc.vec.Vec.with_capacity, hs1]
  have htop' : slhdsa.cache.Built top_tree (paramsS (toSlhParams p)) (bytes sk_seed.val)
      (bytes (fromSlhSeed seed0).pk_seed.val) (layerAdrs (p.d.val - 1) 0) := by
    rw [hpk_bytes]; exact htop
  have hd2' : ∀ d2, layer_d2_hit = some d2 →
      d2.length = treeSize p.hp.val ∧
      slhdsa.cache.Built d2 (paramsS (toSlhParams p)) (bytes sk_seed.val)
        (bytes (fromSlhSeed seed0).pk_seed.val)
        (layerAdrs (p.d.val - 2) (idx_tree.val >>> ((p.d.val - 2) * p.hp.val))) := by
    intro d2 hd2_eq
    rw [hpk_bytes, hidx_tree]
    exact hd2 d2 hd2_eq
  step with sign_from_digest_loop_spec p hp sk_seed (fromSlhSeed seed0) hseed_ok
    top_tree layer_d2_hit root sig2 idx_tree idx_leaf hidx_tree_lt hidx_leaf_lt hsig2_len
    htop_len htop' hd2' as ⟨out, hout⟩
  have hmd_bytes : bytes md.val = (bytes digest.val).take (paramsS (toSlhParams p)).mdBytes := by
    rw [hmd_val, List.slice, hi_le]; simp
  have hfors_adrs : adrsS (toSlhAdrs ⟨0#u32, idx_tree, CacheopsRust.address.FORS_TREE,
      idx_leaf, 0#u32, 0#u32⟩) =
      { { Spec.Adrs.zero with tree := idx_tree.val }.setTypeAndClear Spec.FORS_TREE with
        keypair := idx_leaf.val } := by
    simp [adrsS, Spec.Adrs.setTypeAndClear, Spec.Adrs.zero, Spec.FORS_TREE,
      CacheopsRust.address.FORS_TREE]
  rw [hout, hsig2_val, hsig1_val, bytes_append, bytes_append, hs1, Array.val_to_slice,
    vec_deref_val, hroot_bytes, vec_deref_val, hsf_bytes, hmd_bytes, hfors_adrs,
    hpk_bytes, hidx_tree, hidx_leaf]
  simp [alloc.vec.Vec.with_capacity, List.append_assoc]

/-- End-to-end extracted pipeline composing `CacheValid` + `layer_d2_tree_index` + `lookup_d2`
+ `sign_from_digest` into the exact FIPS 205 signature. -/
theorem sign_from_digest_with_cache_spec {N : Usize} (p : CacheopsRust.params.Params)
    (hp : PN (toSlhParams p) N)
    (c : CacheopsRust.cache.TopTreeCache N)
    (sk_seed pk_seed r : Array U8 N) (digest : Slice U8)
    (hdig : digest.length = p.m.val)
    (hc : CacheValid c (paramsS (toSlhParams p)) (bytes sk_seed.val) (bytes pk_seed.val)) :
    (do
      let tree_d2 ← CacheopsRust.cache.TopTreeCache.layer_d2_tree_index N p digest
      let d2_hit ← CacheopsRust.cache.TopTreeCache.lookup_d2 c tree_d2
      CacheopsRust.cache.sha2_ops.sign_from_digest p sk_seed pk_seed r digest
        (alloc.vec.Vec.deref c.top_tree) d2_hit) ⦃ sig =>
      let P := paramsS (toSlhParams p)
      let md := (bytes digest.val).take P.mdBytes
      let idxTree := Spec.digestTree P (bytes digest.val)
      let idxLeaf := Spec.digestLeaf P (bytes digest.val)
      let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear
        Spec.FORS_TREE with keypair := idxLeaf }
      let sigFors := Spec.forsSign P md (bytes sk_seed.val) (bytes pk_seed.val) adrs
      let pkFors := Spec.forsPkFromSig P sigFors md (bytes pk_seed.val) adrs
      bytes sig.val = bytes r.val ++ sigFors ++
        Spec.htSign P pkFors (bytes sk_seed.val) (bytes pk_seed.val) idxTree idxLeaf ⦄ := by
  step with layer_d2_tree_index_spec N p digest hp.valid hdig as ⟨tree_d2, htd2⟩
  step with lookup_d2_spec hc tree_d2 as ⟨d2_hit, hd2_spec⟩
  apply sign_from_digest_spec p hp sk_seed pk_seed r digest (alloc.vec.Vec.deref c.top_tree)
    d2_hit hdig (by rw [vec_deref_len]; exact hc.top_len) hc.top_built
  intro d2 heq
  rw [heq] at hd2_spec
  simpa [htd2] using hd2_spec

/-! ## End-to-End Cached Hypertree, SLH-DSA & HashSLH-DSA Equivalence (ALL 12 Parameter Sets) -/

/-- Specification-level authentication path extracted from a flat level-contiguous tree. -/
def cachedAuthPath (p : Spec.Params) (tree : List Spec.Bytes) (leaf : Nat) : Spec.Bytes :=
  (List.range p.hp).flatMap fun h => tree[levelOff p.hp h + ((leaf / 2 ^ h) ^^^ 1)]!

/-- Specification-level cached hypertree layer step: substitutes layer `d - 1` with `topTree`
and optionally layer `d - 2` with `d2Hit` on cache hit (polymorphic over SHA-2 and SHAKE). -/
def cachedHtLayer (p : Spec.Params) (skSeed pkSeed : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes))
    (st : Spec.Bytes × Spec.Bytes × Nat × Nat) (j : Nat) :
    Spec.Bytes × Spec.Bytes × Nat × Nat :=
  let (sig, root, tree, leaf) := st
  let adrs := { Spec.Adrs.zero with layer := j, tree := tree }
  if j = p.d - 1 then
    let wots := Spec.wotsSign p root skSeed pkSeed
      { adrs.setTypeAndClear Spec.WOTS_HASH with keypair := leaf }
    let s := wots ++ cachedAuthPath p topTree leaf
    (sig ++ s, root, tree >>> p.hp, tree % 2 ^ p.hp)
  else if j + 2 = p.d then
    match d2Hit with
    | some d2Tree =>
      let wots := Spec.wotsSign p root skSeed pkSeed
        { adrs.setTypeAndClear Spec.WOTS_HASH with keypair := leaf }
      let s := wots ++ cachedAuthPath p d2Tree leaf
      (sig ++ s, d2Tree[d2Tree.length - 1]!, tree >>> p.hp, tree % 2 ^ p.hp)
    | none => Spec.htLayer p skSeed pkSeed st j
  else
    Spec.htLayer p skSeed pkSeed st j

def cachedHtSign (p : Spec.Params) (msg skSeed pkSeed : Spec.Bytes) (idxTree idxLeaf : Nat)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes)) : Spec.Bytes :=
  ((List.range p.d).foldl (cachedHtLayer p skSeed pkSeed topTree d2Hit) ([], msg, idxTree, idxLeaf)).1

def cachedSlhSignInternal (p : Spec.Params) (msg sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes)) : Spec.Bytes :=
  let skSeed := Spec.block p sk 0
  let skPrf := Spec.block p sk 1
  let pkSeed := Spec.block p sk 2
  let pkRoot := Spec.block p sk 3
  let r := Spec.PRFmsg p skPrf addrnd msg
  let digest := Spec.Hmsg p r pkSeed pkRoot msg
  let md := digest.take p.mdBytes
  let idxTree := Spec.digestTree p digest
  let idxLeaf := Spec.digestLeaf p digest
  let adrs := { { Spec.Adrs.zero with tree := idxTree }.setTypeAndClear Spec.FORS_TREE with
    keypair := idxLeaf }
  let sigFors := Spec.forsSign p md skSeed pkSeed adrs
  let pkFors := Spec.forsPkFromSig p sigFors md pkSeed adrs
  let sigHt := cachedHtSign p pkFors skSeed pkSeed idxTree idxLeaf topTree d2Hit
  r ++ sigFors ++ sigHt

def cachedSlhSign (p : Spec.Params) (msg ctx sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes)) : Option Spec.Bytes :=
  if ctx.length > 255 then none
  else some (cachedSlhSignInternal p (Spec.withContext msg ctx) sk addrnd topTree d2Hit)

def cachedHashSlhSignPrehashed (p : Spec.Params) (phm ctx : Spec.Bytes)
    (ph : Spec.PreHash.PreHash) (sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes)) : Option Spec.Bytes :=
  if ctx.length > 255 ∨ phm.length ≠ ph.digestLen then none
  else some (cachedSlhSignInternal p (Spec.PreHash.prehashFrame ctx ph phm) sk addrnd topTree d2Hit)

def cachedHashSlhSign (p : Spec.Params) (msg ctx : Spec.Bytes)
    (ph : Spec.PreHash.PreHash) (sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes)) : Option Spec.Bytes :=
  if ctx.length > 255 then none
  else cachedHashSlhSignPrehashed p (Spec.PreHash.prehashDigest ph msg) ctx ph sk addrnd topTree d2Hit

/-- Specification-level flat Merkle tree invariant over `List Spec.Bytes` (implied by
Dan's `Built` / `TreeContents` on concrete slices via `SpecTreeOk.of_built`). -/
def SpecTreeOk (p : Spec.Params) (skSeed pkSeed : Spec.Bytes) (adrs : Spec.Adrs)
    (nodes : List Spec.Bytes) : Prop :=
  nodes.length = treeSize p.hp ∧
  ∀ h idx, h ≤ p.hp → idx < 2 ^ (p.hp - h) →
    nodes[levelOff p.hp h + idx]! = Spec.xmssNode p skSeed idx h pkSeed adrs

/-- Any Rust slice satisfying Dan's `Built` invariant projects to `SpecTreeOk`. -/
theorem SpecTreeOk.of_built {N : Usize} {p : Spec.Params} {skSeed pkSeed : Spec.Bytes}
    {adrs : Spec.Adrs} {tree : Slice (Array U8 N)}
    (hlen : tree.length = treeSize p.hp)
    (hbuilt : slhdsa.cache.Built tree p skSeed pkSeed adrs) :
    SpecTreeOk p skSeed pkSeed adrs (tree.val.map fun a => bytes a.val) := by
  have htc := slhdsa.cache.constructed hbuilt
  refine ⟨by simpa [Slice.length] using hlen, ?_⟩
  intro h idx hh hidx
  have hlt : levelOff p.hp h + idx < tree.val.length := by
    have h1 : p.hp + 1 - h = (p.hp - h) + 1 := by omega
    have hle : 2 ^ (p.hp + 1 - h) ≤ 2 ^ (p.hp + 1) := two_pow_le_two_pow (by omega)
    have hpos : 1 ≤ 2 ^ (p.hp - h) := Nat.two_pow_pos _
    have : levelOff p.hp h + idx < treeSize p.hp := by
      simp only [levelOff, treeSize]; rw [h1, Nat.pow_succ] at hle ⊢; omega
    change tree.val.length = treeSize p.hp at hlen
    omega
  rw [getElem!_pos _ _ (by simpa using hlt), List.getElem_map, ← getElem!_pos tree.val _ hlt]
  exact htc h hh idx hidx

private theorem cachedAuthPath_eq (p : Spec.Params) (skSeed pkSeed : Spec.Bytes)
    (adrs : Spec.Adrs) (tree : List Spec.Bytes) (leaf : Nat) (hleaf : leaf < 2 ^ p.hp)
    (htree : SpecTreeOk p skSeed pkSeed adrs tree) :
    cachedAuthPath p tree leaf =
      (List.range p.hp).flatMap (fun j => Spec.xmssNode p skSeed ((leaf / 2 ^ j) ^^^ 1) j pkSeed adrs) := by
  unfold cachedAuthPath
  apply List.flatMap_congr
  intro h hh
  have hh_lt : h < p.hp := List.mem_range.mp hh
  have hsplit : 2 ^ p.hp = 2 ^ (p.hp - h) * 2 ^ h := by
    rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  have hdiv : leaf / 2 ^ h < 2 ^ (p.hp - h) :=
    (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos h)).mpr (by rw [← hsplit]; exact hleaf)
  have h1 : 1 < 2 ^ (p.hp - h) :=
    lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (two_pow_le_two_pow (by omega))
  exact htree.2 h ((leaf / 2 ^ h) ^^^ 1) (by omega) (Nat.xor_lt_two_pow hdiv h1)

/-- Cached Hypertree Equivalence: substituting layer `d - 1` (and optionally layer `d - 2`
on cache hit) with cached flat Merkle tree lookups produces the EXACT FIPS 205 `Spec.htSign`
byte string for every valid parameter set (both SHA-2 and SHAKE). -/
theorem cached_htSign_eq_fips (p : Spec.Params) (hv : p.Valid)
    (msg skSeed pkSeed : Spec.Bytes) (idxTree idxLeaf : Nat)
    (htree : idxTree < 2 ^ (p.h - p.hp)) (hleaf : idxLeaf < 2 ^ p.hp)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes))
    (htop : SpecTreeOk p skSeed pkSeed (layerAdrs (p.d - 1) 0) topTree)
    (hd2 : ∀ d2, d2Hit = some d2 →
      SpecTreeOk p skSeed pkSeed (layerAdrs (p.d - 2) (idxTree >>> ((p.d - 2) * p.hp))) d2) :
    cachedHtSign p msg skSeed pkSeed idxTree idxLeaf topTree d2Hit =
      Spec.htSign p msg skSeed pkSeed idxTree idxLeaf := by
  have hd_ge : 2 ≤ p.d := hv.d_ge
  have h_eq : p.h = p.d * p.hp := hv.h_eq
  have htop_zero : idxTree >>> (p.hp * (p.d - 1)) = 0 := by
    have hmul : p.h - p.hp = p.hp * (p.d - 1) := by
      rw [h_eq, Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    rw [Nat.shiftRight_eq_div_pow, ← hmul]
    exact Nat.div_eq_of_lt htree
  suffices hinv : ∀ c, c ≤ p.d →
      let L := (List.range c).foldl (cachedHtLayer p skSeed pkSeed topTree d2Hit) ([], msg, idxTree, idxLeaf)
      let R := (List.range c).foldl (Spec.htLayer p skSeed pkSeed) ([], msg, idxTree, idxLeaf)
      L.1 = R.1 ∧ (c < p.d → L.2.1 = R.2.1) ∧ L.2.2 = R.2.2 by
    exact (hinv p.d (le_refl _)).1
  intro c
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro hc
    have hclt : c < p.d := by omega
    obtain ⟨hsig, hroot, hpos⟩ := ih (by omega)
    have hst := htLayer_state p hv skSeed pkSeed msg idxTree idxLeaf hleaf c (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
    generalize (List.range c).foldl
      (cachedHtLayer p skSeed pkSeed topTree d2Hit) ([], msg, idxTree, idxLeaf) = L at hsig hroot hpos ⊢
    generalize (List.range c).foldl (Spec.htLayer p skSeed pkSeed) ([], msg, idxTree, idxLeaf) = R at hsig hroot hpos hst ⊢
    obtain ⟨Lsig, Lroot, Ltree, Lleaf⟩ := L
    obtain ⟨Rsig, Rroot, Rtree, Rleaf⟩ := R
    simp only [Prod.mk.injEq] at hsig hroot hpos hst
    have hre : Lroot = Rroot := hroot hclt
    obtain ⟨htree_eq, hleaf_eq⟩ := hpos
    subst hsig hre htree_eq hleaf_eq
    unfold cachedHtLayer Spec.htLayer
    simp only
    by_cases hc1 : c = p.d - 1
    · simp only [hc1, ↓reduceIte]
      have htree0 : Ltree = 0 := by rw [hst.1, hc1, htop_zero]
      have hap := cachedAuthPath_eq p skSeed pkSeed
        { Spec.Adrs.zero with layer := p.d - 1, tree := 0 } topTree Lleaf hst.2 htop
      refine ⟨?_, fun hbad => by omega, by simp⟩
      simp only [htree0, Spec.xmssSign, hap]
    · simp only [hc1, ↓reduceIte]
      by_cases hc2 : c + 2 = p.d
      · simp only [hc2, ↓reduceIte]
        cases hopt : d2Hit with
        | none => simp
        | some d2 =>
          simp only
          have hcd2 : c = p.d - 2 := by omega
          have hd2_ok := hd2 d2 hopt
          have htree_d2 : Ltree = idxTree >>> ((p.d - 2) * p.hp) := by
            rw [hst.1, hcd2, Nat.mul_comm]
          have hd2_ok' : SpecTreeOk p skSeed pkSeed
              { Spec.Adrs.zero with layer := c, tree := Ltree } d2 := by
            simpa [layerAdrs, hcd2, htree_d2] using hd2_ok
          have hap := cachedAuthPath_eq p skSeed pkSeed
            { Spec.Adrs.zero with layer := c, tree := Ltree } d2 Lleaf hst.2 hd2_ok'
          have hroot_d2 : d2[d2.length - 1]! =
              Spec.xmssNode p skSeed 0 p.hp pkSeed
                { Spec.Adrs.zero with layer := c, tree := Ltree } := by
            have h0 := hd2_ok'.2 p.hp 0 (le_refl _) (by simp)
            rw [levelOff_hp, Nat.add_zero, ← hd2_ok'.1] at h0
            exact h0
          refine ⟨?_, fun _ => ?_, by simp⟩
          · simp only [Spec.xmssSign, hap]
          · rw [hroot_d2]
            exact (Spec.xmss_correct p hv Lroot skSeed pkSeed Lleaf
              { Spec.Adrs.zero with layer := c, tree := Ltree } hst.2).symm
      · simp [hc2]

/-- End-to-End Cached SLH-DSA Signing Equivalence (`cached_sign_eq_fips`):
for EVERY valid parameter set (all 12 SHA-2 and SHAKE sets), cached pure signing produces
the EXACT FIPS 205 `Spec.slhSign` byte string. -/
theorem cached_sign_eq_fips (p : Spec.Params) (hv : p.Valid)
    (msg ctx sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes))
    (htop : SpecTreeOk p (Spec.block p sk 0) (Spec.block p sk 2)
      (layerAdrs (p.d - 1) 0) topTree)
    (hd2 : ∀ d2, d2Hit = some d2 →
      let m' := Spec.withContext msg ctx
      let r := Spec.PRFmsg p (Spec.block p sk 1) addrnd m'
      let digest := Spec.Hmsg p r (Spec.block p sk 2) (Spec.block p sk 3) m'
      SpecTreeOk p (Spec.block p sk 0) (Spec.block p sk 2)
        (layerAdrs (p.d - 2) (Spec.digestTree p digest >>> ((p.d - 2) * p.hp))) d2) :
    cachedSlhSign p msg ctx sk addrnd topTree d2Hit =
      Spec.slhSign p msg ctx sk addrnd := by
  unfold cachedSlhSign Spec.slhSign
  split
  · rfl
  · congr 1
    unfold cachedSlhSignInternal Spec.slhSignInternal
    simp only []
    congr 1
    have hhp_div : p.h / p.d = p.hp := by
      have hd_pos : 0 < p.d := by have := hv.d_ge; omega
      rw [hv.h_eq, Nat.mul_div_cancel_left _ hd_pos]
    exact cached_htSign_eq_fips p hv _ _ _ _ _
      (by rw [← hhp_div]; exact Spec.digestTree_lt p _) (Spec.digestLeaf_lt p hv _)
      topTree d2Hit htop hd2

/-- End-to-End Cached Pre-Hashed HashSLH-DSA Signing Equivalence:
produces the EXACT FIPS 205 Algorithm 23 `Spec.PreHash.hashSlhSignPrehashed` byte string
for all 12 parameter sets and all 4 pre-hash modes. -/
theorem cached_hash_slh_sign_prehashed_eq_fips (p : Spec.Params) (hv : p.Valid)
    (phm ctx : Spec.Bytes) (ph : Spec.PreHash.PreHash) (sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes))
    (htop : SpecTreeOk p (Spec.block p sk 0) (Spec.block p sk 2)
      (layerAdrs (p.d - 1) 0) topTree)
    (hd2 : ∀ d2, d2Hit = some d2 →
      let m' := Spec.PreHash.prehashFrame ctx ph phm
      let r := Spec.PRFmsg p (Spec.block p sk 1) addrnd m'
      let digest := Spec.Hmsg p r (Spec.block p sk 2) (Spec.block p sk 3) m'
      SpecTreeOk p (Spec.block p sk 0) (Spec.block p sk 2)
        (layerAdrs (p.d - 2) (Spec.digestTree p digest >>> ((p.d - 2) * p.hp))) d2) :
    cachedHashSlhSignPrehashed p phm ctx ph sk addrnd topTree d2Hit =
      Spec.PreHash.hashSlhSignPrehashed p phm ctx ph sk addrnd := by
  unfold cachedHashSlhSignPrehashed Spec.PreHash.hashSlhSignPrehashed
  split
  · rfl
  · congr 1
    unfold cachedSlhSignInternal Spec.slhSignInternal
    simp only []
    congr 1
    have hhp_div : p.h / p.d = p.hp := by
      have hd_pos : 0 < p.d := by have := hv.d_ge; omega
      rw [hv.h_eq, Nat.mul_div_cancel_left _ hd_pos]
    exact cached_htSign_eq_fips p hv _ _ _ _ _
      (by rw [← hhp_div]; exact Spec.digestTree_lt p _) (Spec.digestLeaf_lt p hv _)
      topTree d2Hit htop hd2

/-- End-to-End Cached HashSLH-DSA Signing Equivalence (`cached_hash_slh_sign_eq_fips`):
produces the EXACT FIPS 205 Algorithm 23 `Spec.PreHash.hashSlhSign` byte string for
ALL 12 SHA-2 and SHAKE parameter sets and ALL 4 pre-hash modes. -/
theorem cached_hash_slh_sign_eq_fips (p : Spec.Params) (hv : p.Valid)
    (msg ctx : Spec.Bytes) (ph : Spec.PreHash.PreHash) (sk addrnd : Spec.Bytes)
    (topTree : List Spec.Bytes) (d2Hit : Option (List Spec.Bytes))
    (htop : SpecTreeOk p (Spec.block p sk 0) (Spec.block p sk 2)
      (layerAdrs (p.d - 1) 0) topTree)
    (hd2 : ∀ d2, d2Hit = some d2 →
      let m' := Spec.PreHash.prehashFrame ctx ph (Spec.PreHash.prehashDigest ph msg)
      let r := Spec.PRFmsg p (Spec.block p sk 1) addrnd m'
      let digest := Spec.Hmsg p r (Spec.block p sk 2) (Spec.block p sk 3) m'
      SpecTreeOk p (Spec.block p sk 0) (Spec.block p sk 2)
        (layerAdrs (p.d - 2) (Spec.digestTree p digest >>> ((p.d - 2) * p.hp))) d2) :
    cachedHashSlhSign p msg ctx ph sk addrnd topTree d2Hit =
      Spec.PreHash.hashSlhSign p msg ctx ph sk addrnd := by
  unfold cachedHashSlhSign Spec.PreHash.hashSlhSign
  split
  · rfl
  · exact cached_hash_slh_sign_prehashed_eq_fips p hv _ ctx ph sk addrnd topTree d2Hit htop hd2

/-- All 12 FIPS 205 Table 2 parameter sets (6 SHA-2 + 6 SHAKE) satisfy `Params.Valid`. -/
theorem all_12_parameter_sets_valid :
    Spec.sha2_128s.Valid ∧ Spec.sha2_128f.Valid ∧
    Spec.sha2_192s.Valid ∧ Spec.sha2_192f.Valid ∧
    Spec.sha2_256s.Valid ∧ Spec.sha2_256f.Valid ∧
    Spec.shake_128s.Valid ∧ Spec.shake_128f.Valid ∧
    Spec.shake_192s.Valid ∧ Spec.shake_192f.Valid ∧
    Spec.shake_256s.Valid ∧ Spec.shake_256f.Valid :=
  ⟨Spec.sha2_128s_valid, Spec.sha2_128f_valid, Spec.sha2_192s_valid, Spec.sha2_192f_valid,
   Spec.sha2_256s_valid, Spec.sha2_256f_valid, Spec.PreHash.shake_128s_valid,
   Spec.PreHash.shake_128f_valid, Spec.PreHash.shake_192s_valid, Spec.PreHash.shake_192f_valid,
   Spec.PreHash.shake_256s_valid, Spec.PreHash.shake_256f_valid⟩

end slhdsa.cache.endtoend
