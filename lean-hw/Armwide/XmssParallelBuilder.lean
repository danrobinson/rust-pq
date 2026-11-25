import Armwide.XmssCacheBuilder
import Cachepath.ParallelFillWorkers

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Armwide.XmssLeaves.Generate
open Keygen Public.Dispatcher slhdsa.cache.builder slhdsa.cache.builder.workers
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 1000000
section
variable [Cpu] [Features]

@[rust_loop_body]
def sha2Batch_loop.body
  {N : Std.Usize} (sk_seed : Array Std.U8 N) (seed : hash.Seed N)
  (adrs : address.Adrs) (iter : core.ops.range.Range Std.Usize)
  (out : alloc.vec.Vec (Array Std.U8 N)) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (alloc.vec.Vec
    (Array Std.U8 N))) (alloc.vec.Vec (Array Std.U8 N)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done out)
  | some i =>
    let a ← address.Adrs.with_type adrs address.WOTS_HASH
    let i1 ← lift (UScalar.cast .U32 i)
    let a1 ← address.Adrs.with_keypair a i1
    let a2 ← wots.wots_pk_gen sk_seed seed a1
    let out1 ← alloc.vec.Vec.push out a2
    ok (cont (iter1, out1))

@[rust_loop]
def sha2Batch_loop
  {N : Std.Usize} (iter : core.ops.range.Range Std.Usize)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs)
  (out : alloc.vec.Vec (Array Std.U8 N)) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  loop
    (fun (iter1, out1) => sha2Batch_loop.body sk_seed
      seed adrs iter1 out1)
    (iter, out)

def sha2Batch
  {N : Std.Usize} (start : Std.Usize) («end» : Std.Usize)
  (sk_seed : Array Std.U8 N) (seed : hash.Seed N) (adrs : address.Adrs) :
  Result (alloc.vec.Vec (Array Std.U8 N))
  := do
  let i ← «end» - start
  let out := alloc.vec.Vec.with_capacity (Array Std.U8 N) i
  sha2Batch_loop { start, «end» } sk_seed seed adrs out

variable [Pool]

def sha2Tree
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
  let (s, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice
      (Array Std.U8 N)) nodes { «end» := num_leaves }
  let (built_parallel, s1) ←
    Pool.sha2 num_leaves sk_seed seed adrs s
  if built_parallel
  then
    let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
    let nodes1 := index_mut_back s1
    cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes1
  else
    let nodes1 := index_mut_back s1
    let nodes2 ←
      cache.sha2_ops.build_xmss_tree_loop0
        { start := 0#usize, «end» := num_leaves } sk_seed seed adrs nodes1
    let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
    cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes2

end

private theorem ticket [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (start stop : Usize) :
    sha2Batch start stop sk seed a = fill.sha2Batch start stop sk seed a := by
  unfold sha2Batch fill.sha2Batch
  apply bind_right; intro size
  unfold sha2Batch_loop fill.sha2Batch_loop
  dsimp only
  congr 1
  funext q
  rcases q with ⟨range,nodes⟩
  unfold sha2Batch_loop.body fill.sha2Batch_loop.body
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

private def word (n : Nat) : Usize := ⟨BitVec.ofNat _ n⟩
private def chunk {N : Usize} (job : Usize → Usize → Result (Nodes N)) (start len : Nat) :
    Result (List (Array U8 N)) := do
  let r ← job (word start) (word (start+len))
  ok r.val

/-- The worker publication protocol evaluates the native WOTS worker at every claimed ticket. -/
def workerPool [Cpu] [Features] (threads : Usize) : Pool :=
  { @fill.pool nativeShake.scalar threads with
    sha2 := fun n sk seed a out => fill.runtimeAttempt threads n out (chunk (fun l r => sha2Batch l r sk seed a)) }

private theorem native_fill [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (sk : Array U8 N)
    (seed : hash.Seed N) (hs : SeedOk seed) (a : address.Adrs) (threads n : Usize) (dest : nativeShake.Rows N) :
    (workerPool threads).sha2 n sk seed a dest = (@fill.pool nativeShake.scalar threads).sha2 n sk seed a dest := by
  change fill.runtimeAttempt threads n dest (chunk (fun l r => sha2Batch l r sk seed a)) =
    fill.runtimeAttempt threads n dest (chunk (fun l r => fill.sha2Batch l r sk seed a))
  simp only [ticket p hp sk seed hs a]

/-- The shared continuation after seeding. Exposing both callbacks lets the kernel check
    their equalities once, independently of allocation, writeback and tree reduction. -/
private def after_seed {N : Usize} (seed : hash.Seed N) (hp layer : U32) (tree_index : U64)
    (parallel : Usize → address.Adrs → nativeShake.Rows N → Result (Bool × nativeShake.Rows N))
    (serial : core.ops.range.Range Usize → address.Adrs → alloc.vec.Vec (Array U8 N) → Result (alloc.vec.Vec (Array U8 N))) :
    Result (alloc.vec.Vec (Array U8 N)) := do
  let a ← address.Adrs.new
  let a1 ← address.Adrs.with_layer a layer
  let adrs ← address.Adrs.with_tree a1 tree_index
  let num_leaves ← 1#usize <<< hp
  let total ← cache.tree_node_count hp
  let a2 := Array.repeat N 0#u8
  let nodes ←
    alloc.vec.from_elem (core.clone.CloneArray N core.clone.CloneU8) a2 total
  let (s, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice
      (Array Std.U8 N)) nodes { «end» := num_leaves }
  let (built_parallel, s1) ←
    parallel num_leaves adrs s
  if built_parallel
  then
    let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
    let nodes1 := index_mut_back s1
    cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes1
  else
    let nodes1 := index_mut_back s1
    let nodes2 ←
      serial { start := 0#usize, «end» := num_leaves } adrs nodes1
    let iter ← core.ops.range.RangeInclusive.new 1#u32 hp
    cache.sha2_ops.build_xmss_tree_loop1 iter hp seed adrs num_leaves nodes2

private theorem bind_checked {α β} {r : Result α} {P : α → Prop} {f g : α → Result β}
    (hr : r ⦃ x => P x ⦄) (h : ∀ x, P x → f x=g x) : Std.bind r f=Std.bind r g := by
  obtain ⟨x,ret,hx⟩ := spec_imp_exists hr
  simp only [ret, bind_ok]
  exact h x hx

private theorem builder_congr [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (pool1 pool2 : Pool)
    (same : ∀ (n : Usize) (sk : Array U8 N) (seed : hash.Seed N) (_ : SeedOk seed) (a : address.Adrs) out,
      pool1.sha2 n sk seed a out=pool2.sha2 n sk seed a out)
    (h l : U32) (treeIndex : U64) (sk pk : Array U8 N) :
    @sha2Tree _ _ pool1 N h l treeIndex sk pk =
      @workers.sha2Tree pool2 N h l treeIndex sk pk := by
  unfold sha2Tree workers.sha2Tree
  apply bind_checked (seed_ctx_spec hp.nok pk)
  rintro seed ⟨_,hs⟩
  change after_seed seed h l treeIndex (fun n a dest => pool1.sha2 n sk seed a dest)
    (fun it a v => cache.sha2_ops.build_xmss_tree_loop0 it sk seed a v) =
    after_seed seed h l treeIndex (fun n a dest => pool2.sha2 n sk seed a dest)
      (fun it a v => slhdsa.cache.sha2_ops.build_xmss_tree_loop0 it sk seed a v)
  exact congrArg₂ (after_seed seed h l treeIndex)
    (funext fun n => funext fun a => funext fun dest => same n sk seed hs a dest)
    (funext fun it => funext fun a => funext fun v => leaf_loop p hp sk seed hs a it v)

theorem parallel_builder_eq [Cpu] [Features] {N} (p : params.Params) (hp : PN p N) (threads : Usize)
    (h l : U32) (treeIndex : U64) (sk pk : Array U8 N) :
    @sha2Tree _ _ (workerPool threads) N h l treeIndex sk pk =
      @workers.sha2Tree (@fill.pool nativeShake.scalar threads) N h l treeIndex sk pk :=
  builder_congr p hp _ _ (fun n sk seed hs a dest => native_fill p hp sk seed hs a threads n dest) h l treeIndex sk pk

theorem parallel_tree_kernel [Cpu] [Features] {N : Usize} (p : params.Params) (hp : PN p N) (threads : Usize) :
    CacheopsRust.cache.constructor.TreeKernel (@sha2Tree _ _ (workerPool threads) N) (paramsS p) := by
  intro h l i sk pk correct
  rw [parallel_builder_eq p hp threads]
  let single : nativeShake.Subtree.Single := ⟨slhdsa.shake.wots.wots_pk_gen⟩
  have checked := @fill.pool_correct nativeShake.scalar single threads N ⟨false,rfl⟩
    (fun enabled => False.elim (Bool.noConfusion (Result.ok_injective enabled : false=true)))
  exact @workers.sha2_kernel N (@fill.pool nativeShake.scalar threads) checked p hp h l i sk pk correct

theorem parallel_cached_keys [Cpu] [Features] {N : Usize} (p : CacheopsRust.params.Params) (hp : PN (CacheopsRust.toSlhParams p) N)
    (threads : Usize) (shake : CacheopsRust.cache.mutation.Builder N) (seeds sk pk : Slice U8)
    (ss : seeds.length=3*N.val) (ks : sk.length=4*N.val) (ps : pk.length=2*N.val) :
    CacheopsRust.cache.generatedKeys.keygen N (@sha2Tree _ _ (workerPool threads) N) shake .Sha2 p seeds sk pk
      ⦃ out => CacheopsRust.cache.generatedKeys.Generated (paramsS (CacheopsRust.toSlhParams p)) .Sha2 seeds out ⦄ := by
  apply CacheopsRust.cache.generatedKeys.keygen_spec _ _ _ p _ hp.n_eq.symm hp.n rfl rfl hp.valid
  · intro _; exact parallel_tree_kernel _ hp threads
  · intro h; cases h
  all_goals assumption

end
end slhdsa.Armwide.XmssLeaves.Generate
