import Cachepath.ConstructorProgram

open Aeneas Aeneas.Std Result
open slhdsa.cache.endtoend
namespace CacheopsRust.cache.constructor

open slhdsa (bytes)

/-- Contract of the selected tree kernel at arbitrary layer, tree and seeds. -/
def TreeKernel {N : Usize} (builder : mutation.Builder N) (p : Spec.Params) : Prop :=
  ∀ (hp layer : U32) (tree : U64) (sk pk : Array U8 N), hp.val = p.hp →
    builder hp layer tree sk pk ⦃ nodes =>
      nodes.length = treeSize p.hp ∧ slhdsa.cache.Built (alloc.vec.Vec.deref nodes)
        p (bytes sk.val) (bytes pk.val) (layerAdrs layer.val tree.val) ⦄

private theorem keyBlock {N : Usize} (p : Spec.Params) (hn : p.n = N.val) (sk : Slice U8)
    (i : Usize) (h : (i.val + 1) * N.val ≤ sk.length) :
    CacheopsRust.util.block N sk i ⦃ a => bytes a.val = Spec.block p (bytes sk.val) i.val ⦄ := by
  apply WP.spec_mono (slhdsa.block_spec N sk i h)
  intro a ha
  simp [Spec.block, hn, ha, bytes, List.map_take, List.map_drop]

private theorem setup {N : Usize} (builder : mutation.Builder N) (params : CacheopsRust.params.Params)
    (p : Spec.Params) (hd : params.d.val = p.d) (hp : params.hp.val = p.hp) (pos : 0 < p.d)
    (sk pk : Array U8 N) (kernel : TreeKernel builder p) :
    (do let layer ← params.d - 1#u32; builder params.hp layer 0#u64 sk pk) ⦃ nodes =>
      nodes.length = treeSize p.hp ∧ slhdsa.cache.Built (alloc.vec.Vec.deref nodes) p
        (bytes sk.val) (bytes pk.val) (layerAdrs (p.d - 1) 0) ⦄ := by
  step as ⟨layer, hl⟩
  step with kernel _ _ _ _ _ hp as ⟨nodes, hn, hb⟩
  exact ⟨hn, by simpa [hl,hd] using hb⟩

/-- Public cache construction both establishes the invariant and accepts the same key on reuse.
The selected kernel is required only at the hash family actually dispatched. -/
theorem valid {N : Usize} (sha2 shake : mutation.Builder N) (family : HashFamily)
    (params : CacheopsRust.params.Params) (p : Spec.Params)
    (hn : N = params.n) (hnSpec : p.n = N.val) (hd : params.d.val = p.d)
    (hp : params.hp.val = p.hp) (pos : 0 < p.d)
    (sk : Slice U8) (len : sk.length = 4 * N.val) (key : Spec.KeyOk p (bytes sk.val))
    (hsha2 : family = .Sha2 → TreeKernel sha2 p)
    (hshake : family = .Shake → TreeKernel shake p) :
    newCache N sha2 shake family params sk ⦃ c =>
      CacheValid c p (Spec.block p (bytes sk.val) 0) (Spec.block p (bytes sk.val) 2) ∧
      c.family = family ∧ c.layer_d2.val = [] ∧ c.layer_d2_capacity = 0#usize ∧
      TopTreeCache.matches_key c sk = ok true ⦄ := by
  have bound : 4 * N.val ≤ Usize.max := len ▸ sk.property
  have hwrap : Slice.len sk = Usize.wrapping_mul 4#usize N := by
    apply UScalar.eq_of_val_eq
    simp [len, Nat.mod_eq_of_lt (by scalar_tac : 4 * N.val < Usize.size)]
  unfold newCache
  simp only [ite_eq_left hn, lift, bind_ok, ite_eq_left hwrap]
  step as ⟨_,_⟩
  step with keyBlock p hnSpec sk 0#usize (by scalar_tac) as ⟨secret, hs⟩
  step with keyBlock p hnSpec sk 2#usize (by scalar_tac) as ⟨pub, hpk⟩
  step with keyBlock p hnSpec sk 3#usize (by scalar_tac) as ⟨root, hr⟩
  have build :
      (match family with
        | .Sha2 => do let l ← params.d - 1#u32; sha2 params.hp l 0#u64 secret pub
        | .Shake => do let l ← params.d - 1#u32; shake params.hp l 0#u64 secret pub) ⦃ nodes =>
      nodes.length = treeSize p.hp ∧ slhdsa.cache.Built (alloc.vec.Vec.deref nodes) p
        (bytes secret.val) (bytes pub.val) (layerAdrs (p.d - 1) 0) ⦄ := by
    cases family
    · exact setup _ _ _ hd hp pos _ _ (hsha2 rfl)
    · exact setup _ _ _ hd hp pos _ _ (hshake rfl)
  step with build as ⟨nodes, hnlen, hb⟩
  rw [hs, hpk] at hb
  let c : TopTreeCache N := ⟨family, params.hp, params.d, pub, nodes, alloc.vec.Vec.new _, 0#usize⟩
  have hc : CacheValid c p (Spec.block p (bytes sk.val) 0) (Spec.block p (bytes sk.val) 2) :=
    ⟨hp,hd,hpk,hnlen,hb,by intro e he; change e ∈ ([] : List _) at he; simp at he⟩
  have link := matches_key_valid_key c p sk hnSpec bound len key hc
  step with slhdsa.cache.root (alloc.vec.Vec.deref nodes)
    (by rw [vec_deref_len,hnlen]; exact treeSize_pos _) as ⟨actual,ha⟩
  step with slhdsa.ht_array_eq_spec actual root as ⟨same,hsame⟩
  have heq : actual.val = root.val := by
    apply slhdsa.ht_bytes_injective
    rw [ha, vec_deref_len, slhdsa.vec_deref_val,hr]
    exact link.1
  simp only [hsame,heq,decide_true,↓reduceIte,WP.spec_ok]
  exact ⟨hc, trivial, rfl, trivial, link.2⟩

/-- An arbitrary finite sequence of requests to the extracted d-2 lookup/update. -/
def populate {N : Usize} (sha2 shake : mutation.Builder N) (params : CacheopsRust.params.Params)
    (sk pk : Array U8 N) : List U64 → TopTreeCache N → Result (TopTreeCache N)
  | [], c => ok c
  | k :: ks, c => do
    let (_,next) ← TopTreeCache.lookup_or_populate_d2 sha2 shake c params sk pk k
    populate sha2 shake params sk pk ks next

theorem reuse {N : Usize} (sha2 shake : mutation.Builder N) (params : CacheopsRust.params.Params)
    (p : Spec.Params) (hd : params.d.val = p.d) (hp : params.hp.val = p.hp)
    (bound : params.hp.val < Usize.numBits) (sk pk : Array U8 N) (keys : List U64)
    (c : TopTreeCache N) (hc : CacheValid c p (bytes sk.val) (bytes pk.val))
    (hsha2 : c.family = .Sha2 → TreeKernel sha2 p) (hshake : c.family = .Shake → TreeKernel shake p) :
    populate sha2 shake params sk pk keys c ⦃ out =>
      CacheValid out p (bytes sk.val) (bytes pk.val) ∧ out.family = c.family ⦄ := by
  induction keys generalizing c with
  | nil => simp only [populate,WP.spec_ok]; exact ⟨hc,trivial⟩
  | cons k ks ih =>
    have localBuild (b : mutation.Builder N) (h : TreeKernel b p) : mutation.Builds b params p sk pk k := by
      intro l hl
      simpa only [hl] using h params.hp l k sk pk hp
    simp only [populate]
    apply WP.spec_bind (mutation.lookup_or_populate_safe sha2 shake c params p sk pk k hc hd bound
      (fun h => localBuild _ (hsha2 h)) (fun h => localBuild _ (hshake h)))
    rintro ⟨_,next⟩ ⟨hn,hf,_⟩
    have hs := ih next hn (fun h => hsha2 (hf.symm.trans h)) (fun h => hshake (hf.symm.trans h))
    apply WP.spec_mono hs
    rintro out ⟨valid,family⟩
    exact ⟨valid,family.trans hf⟩

end CacheopsRust.cache.constructor
