import Cachepath.BuilderShakeLeaves
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.nativeShake
set_option linter.concreteInstances false

def one {N : Usize} (pk_seed : Array U8 N) (adrs : address.Adrs) (z : U32) (children : Rows N) (i : Usize) (parents : Rows N) : Result (Rows N) := do
  let a ← address.Adrs.with_type adrs address.TREE
  let a1 ← address.Adrs.with_word2 a z
  let i1 ← lift (UScalar.cast .U32 i)
  let a2 ← address.Adrs.with_word3 a1 i1
  let i2 ← 2#usize * i
  let a3 ← Slice.index_usize children i2
  let i3 ← i2 + 1#usize
  let a4 ← Slice.index_usize children i3
  let a5 ← shake.hash.thash_pair pk_seed a2 a3 a4
  let s ← Slice.update parents i a5
  ok s

theorem one_body {N : Usize} (pk_seed : Array U8 N) (adrs : address.Adrs) (z : U32) (children : Rows N) :
    (fun (s : Range × Rows N) => build_xmss_tree_loop0_loop0.body pk_seed adrs z children s.1 s.2) = rangeBody (one pk_seed adrs z children) := by
  funext s
  unfold build_xmss_tree_loop0_loop0.body rangeBody
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> simp [one,Std.bind_assoc, bind_tc_eq]

def stage {N : Usize} [Backend] (hp : U32) (pk_seed : Array U8 N) (adrs : address.Adrs) (num_leaves : Usize) (z : U32) (nodes : Nodes N) : Result (Nodes N) := do
  let i ← z - 1#u32
  let prev ← cache.level_offset hp i
  let cur ← cache.level_offset hp z
  let count ← num_leaves >>> z
  let (s, deref_mut_back) ← lift (alloc.vec.Vec.deref_mut nodes)
  let ((children_slice, parents_slice), split_at_mut_back) ←
    core.slice.Slice.split_at_mut s cur
  let i1 ← 2#usize * count
  let i2 ← prev + i1
  let children ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
      (Array Std.U8 N)) children_slice { start := prev, «end» := i2 }
  let (parents, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice (Array Std.U8 N))
      parents_slice { «end» := count }
  let b ← Backend.available N
  if b
  then
    let parents1 ←
      Backend.pairs pk_seed adrs z 0#usize children parents
    let parents_slice1 := index_mut_back parents1
    let s1 := split_at_mut_back (children_slice, parents_slice1)
    let nodes1 := deref_mut_back s1
    ok nodes1
  else
    let parents1 ←
      build_xmss_tree_loop0_loop0
        { start := 0#usize, «end» := count } pk_seed adrs z children
        parents
    let parents_slice1 := index_mut_back parents1
    let s1 := split_at_mut_back (children_slice, parents_slice1)
    let nodes1 := deref_mut_back s1
    ok nodes1

theorem stage_body {N : Usize} [Backend] (hp : U32) (pk_seed : Array U8 N) (adrs : address.Adrs) (num_leaves : Usize) :
    (fun (s : Inclusive × Nodes N) => build_xmss_tree_loop0.body hp pk_seed adrs num_leaves s.1 s.2) = inclusiveBody (stage hp pk_seed adrs num_leaves) := by
  funext s
  unfold build_xmss_tree_loop0.body inclusiveBody
  congr 1
  funext pair
  rcases pair with ⟨o,it⟩
  cases o <;> simp [stage,Std.bind_assoc,bind_tc_eq,lift,alloc.vec.Vec.deref_mut]
  iterate 5 (congr 1; funext arg)
  rcases arg with ⟨⟨left,right⟩,restore⟩
  simp [Std.bind_assoc]
  iterate 4 (congr 1; funext arg)
  rcases arg with ⟨parents,write⟩
  simp [Std.bind_assoc]
  congr 1
  funext enabled
  cases enabled <;> simp [Std.bind_assoc]
end slhdsa.cache.builder.nativeShake
