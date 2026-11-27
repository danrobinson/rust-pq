import Cachepath.BuilderProgram
import Cachepath.BuilderLoops
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder
open sha2_ops


def leaf {N : Usize} (sk_seed : Array U8 N) (seed : hash.Seed N) (adrs : address.Adrs) (i : Usize) (nodes : Nodes N) : Result (Nodes N) := do
  let a ← address.Adrs.with_type adrs address.WOTS_HASH
  let i1 ← lift (UScalar.cast .U32 i)
  let a1 ← address.Adrs.with_keypair a i1
  let a2 ← wots.wots_pk_gen sk_seed seed a1
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
      Std.U8 N)) nodes i
  let nodes1 := index_mut_back a2
  ok nodes1

theorem leaf_body {N : Usize} (sk_seed : Array U8 N) (seed : hash.Seed N) (adrs : address.Adrs)  :
    (fun (s : Range × Nodes N) => build_xmss_tree_loop0.body sk_seed seed adrs s.1 s.2) = rangeBody (leaf sk_seed seed adrs) := by
  funext s
  unfold build_xmss_tree_loop0.body rangeBody
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> simp [leaf,Std.bind_assoc]
  all_goals
    repeat' (congr 1; funext arg)
    rename_i arg
    cases arg
    simp [Std.bind]
    exact (bind_ok _ (fun (out : Nodes N) => ok (ControlFlow.cont (β := Nodes N) (it,out)))).symm

def parent {N : Usize} (seed : hash.Seed N) (adrs : address.Adrs) (z : U32) (prev cur i : Usize) (nodes : Nodes N) : Result (Nodes N) := do
  let a ← address.Adrs.with_type adrs address.TREE
  let a1 ← address.Adrs.with_word2 a z
  let i1 ← lift (UScalar.cast .U32 i)
  let a2 ← address.Adrs.with_word3 a1 i1
  let i2 ← 2#usize * i
  let i3 ← prev + i2
  let a3 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
      N)) nodes i3
  let i4 ← prev + i2
  let i5 ← i4 + 1#usize
  let a4 ←
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8
      N)) nodes i5
  let a5 ← xmss.hash2 seed a2 a3 a4
  let i6 ← cur + i
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice (Array
      Std.U8 N)) nodes i6
  let nodes1 := index_mut_back a5
  ok nodes1

theorem parent_body {N : Usize} (seed : hash.Seed N) (adrs : address.Adrs) (z : U32) (prev cur : Usize) :
    (fun (s : Range × Nodes N) => build_xmss_tree_loop1_loop0.body seed adrs z prev cur s.1 s.2) = rangeBody (parent seed adrs z prev cur) := by
  funext s
  unfold build_xmss_tree_loop1_loop0.body rangeBody
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> simp [parent,Std.bind_assoc]
  all_goals
    repeat' (congr 1; funext arg)
    rename_i arg
    cases arg
    simp [Std.bind]
    exact (bind_ok _ (fun (out : Nodes N) => ok (ControlFlow.cont (β := Nodes N) (it,out)))).symm

def level {N : Usize} (hp : U32) (seed : hash.Seed N) (adrs : address.Adrs) (num_leaves : Usize) (z : U32) (nodes : Nodes N) : Result (Nodes N) := do
  let i ← z - 1#u32
  let prev ← cache.level_offset hp i
  let cur ← cache.level_offset hp z
  let count ← num_leaves >>> z
  let nodes1 ←
    cache.sha2_ops.build_xmss_tree_loop1_loop0
      { start := 0#usize, «end» := count } seed adrs nodes z prev cur
  ok nodes1

theorem level_body {N : Usize} (hp : U32) (seed : hash.Seed N) (adrs : address.Adrs) (num_leaves : Usize)  :
    (fun (s : Inclusive × Nodes N) => build_xmss_tree_loop1.body hp seed adrs num_leaves s.1 s.2) = inclusiveBody (level hp seed adrs num_leaves) := by
  funext s
  unfold build_xmss_tree_loop1.body inclusiveBody
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> simp [level,Std.bind_assoc]
end slhdsa.cache.builder
