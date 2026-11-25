import Armwide.KeyDispatch
import Cachepath.Keygen
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Armwide.XmssLeaves.Generate
open Keygen Public.Dispatcher
noncomputable section
section
variable [Cpu] [Features]
abbrev wots.wots_pk_gen {N : Usize} := @Keygen.Dispatcher.wots.wots_pk_gen _ _ N

@[rust_loop_body]
def cache.sha2_ops.build_xmss_tree_loop0.body
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (iter : core.ops.range.Range Std.Usize)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done nodes)
  | some i =>
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let i1 ← lift (UScalar.cast .U32 i)
    let a1 ← address.Adrs.with_keypair a i1
    let a2 ← wots.wots_pk_gen sk_seed seed a1
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
        Std.U8 N)) nodes i
    let nodes1 := index_mut_back a2
    ok (cont (iter1, nodes1))

@[rust_loop]
def cache.sha2_ops.build_xmss_tree_loop0
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs)
  (nodes : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, nodes1) => cache.sha2_ops.build_xmss_tree_loop0.body sk_seed
      seed adrs iter1 nodes1)
    (iter, nodes)

def cache.sha2_ops.build_xmss_tree
  {N : Std.Usize} (hp : Std.U32) (layer : Std.U32) (tree_index : Std.U64)
  (sk_seed : Array Std.U8 N) (pk_seed : Array Std.U8 N) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let seed ← hash.seed_ctx pk_seed
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_layer a layer
  let adrs ← address.Adrs.with_tree a1 tree_index
  let num_leaves ← 1#usize <<< hp
  let total ← cache.tree_node_count hp
  let a2 := Array.repeat N 0#u8
  let nodes ←
    alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a2 total
  let nodes1 ←
    cache.sha2_ops.build_xmss_tree_loop0
      { start := 0#usize, «end» := num_leaves } sk_seed seed adrs nodes
  let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
  cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes1

end

theorem bind_right {α β} {r : Result α} {f g : α → Result β} (h : ∀ a, f a=g a) :
    Std.bind r f = Std.bind r g := by rw [funext h]

theorem leaf_loop [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (it : core.ops.range.Range Usize)
    (v : alloc.vec.Vec (Array U8 N)) :
    cache.sha2_ops.build_xmss_tree_loop0 it sk seed a v = slhdsa.cache.sha2_ops.build_xmss_tree_loop0 it sk seed a v := by
  unfold cache.sha2_ops.build_xmss_tree_loop0 slhdsa.cache.sha2_ops.build_xmss_tree_loop0
  congr 1
  funext q
  rcases q with ⟨range,nodes⟩
  unfold cache.sha2_ops.build_xmss_tree_loop0.body slhdsa.cache.sha2_ops.build_xmss_tree_loop0.body
  apply bind_right
  rintro ⟨opt,next⟩
  cases opt with
  | none => rfl
  | some i =>
    dsimp only
    simp only [address.Adrs.with_type,address.Adrs.with_keypair,lift,bind_ok,wots.wots_pk_gen]
    let normalized := {a with typ:=address.WOTS_HASH,keypair:=UScalar.cast .U32 i,word2:=0#u32,word3:=0#u32}
    change Std.bind (Keygen.Dispatcher.wots.wots_pk_gen sk seed normalized) _ = Std.bind (slhdsa.wots.wots_pk_gen sk seed normalized) _
    rw [Keygen.Dispatcher.dispatch_eq_scalar p hp sk seed hs normalized (by with_unfolding_all rfl)]

theorem cache_builder_eq [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (height layer : U32)
    (treeIndex : U64) (sk pk : Array U8 N) :
    cache.sha2_ops.build_xmss_tree height layer treeIndex sk pk =
      slhdsa.cache.sha2_ops.build_xmss_tree height layer treeIndex sk pk := by
  unfold cache.sha2_ops.build_xmss_tree slhdsa.cache.sha2_ops.build_xmss_tree
  obtain ⟨seed,ret,_,hs⟩ := spec_imp_exists (seed_ctx_spec hp.nok pk)
  simp only [ret,bind_ok,address.Adrs.new,address.Adrs.with_layer,address.Adrs.with_tree]
  apply bind_right; intro leaves
  apply bind_right; intro total
  apply bind_right; intro nodes
  rw [leaf_loop p hp sk seed hs]

theorem tree_kernel [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N) :
    CacheopsRust.cache.constructor.TreeKernel (@cache.sha2_ops.build_xmss_tree _ _ N) (paramsS p) := by
  intro height layer i sk pk correct
  rw [cache_builder_eq p hp]
  exact slhdsa.cache.builder.sha2_kernel p hp height layer i sk pk correct

theorem cached_keys [Cpu] [Features] {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (CacheopsRust.toSlhParams p) N)
    (shake : CacheopsRust.cache.mutation.Builder N) (seeds sk pk : Slice U8) (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    CacheopsRust.cache.generatedKeys.keygen N (@cache.sha2_ops.build_xmss_tree _ _ N) shake
      .Sha2 p seeds sk pk ⦃ out => CacheopsRust.cache.generatedKeys.Generated (paramsS (CacheopsRust.toSlhParams p))
        .Sha2 seeds out ⦄ := by
  apply CacheopsRust.cache.generatedKeys.keygen_spec _ _ _ p _ hp.n_eq.symm hp.n rfl rfl hp.valid
  · intro _; exact tree_kernel _ hp
  · intro h; cases h
  all_goals assumption

end
end slhdsa.Armwide.XmssLeaves.Generate
