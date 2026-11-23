import Parentdriver.Model
import Parentblock.Fips
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.PlatformParent.Driver

@[step] theorem make_block_spec (N : Usize) (a : address.Adrs) (l r : Slice U8)
    (shape : N.val = 24 ∨ N.val = 32) (hl : l.length = N.val) (hr : r.length = N.val) :
    makeBlock N (Array.repeat 128#usize 0#u8) a l r ⦃ b =>
      bytes b.val = S512.padFrom 128 ((adrsS a).compress ++ bytes l.val ++ bytes r.val) ⦄ :=
  parent_block_spec N (blockAddress a) l r shape hl hr



/- The two extractions specialize this program to different batch widths and
compression kernels. The architecture-specific proofs check definitional equality. -/
def treeBlockStep {G : Usize}
  {N : Usize} (adrs : slhdsa.address.Adrs) (first : U32)
  (values : Nodes N) (j : Usize)
  (iter : core.ops.range.Range Usize)
  (blocks : Blocks G) :
  Result (ControlFlow ((core.ops.range.Range Usize) × (Blocks G)) (Blocks G))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done blocks)
  | some lane =>
    let (block, index_mut_back) ← Array.index_mut_usize blocks lane
    let i ← j + lane
    let i1 ← lift (UScalar.cast .U32 i)
    let i2 ← first + i1
    let a ← slhdsa.address.Adrs.with_word3 adrs i2
    let i3 ← 2#usize * i
    let a1 ← Slice.index_usize values i3
    let s ← lift (Array.to_slice a1)
    let i4 ← i3 + 1#usize
    let a2 ← Slice.index_usize values i4
    let s1 ← lift (Array.to_slice a2)
    let block1 ← makeBlock N block a s s1
    let a3 := index_mut_back block1
    ok (cont (iter1, a3))

def treeBlocks {G : Usize}
  {N : Usize} (iter : core.ops.range.Range Usize) (adrs : slhdsa.address.Adrs)
  (first : U32) (values : Nodes N) (j : Usize)
  (blocks : Blocks G) :
  Result (Blocks G)
  := do
  loop
    (fun (iter1, blocks1) => treeBlockStep
      adrs first values j iter1 blocks1)
    (iter, blocks)

def treeBatchStep {G : Usize} (K : Kernel G)
  {N : Usize} (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (first : U32)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
  (values : Nodes N) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Usize)) × (Nodes N)) (Nodes N))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done values)
  | some j =>
    let a := Array.repeat 128#usize 0#u8
    let blocks := Array.repeat G a
    let blocks1 ←
      treeBlocks
        { start := 0#usize, «end» := G } adrs first values
        j blocks
    let i ← j + G
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N)) values
        { start := j, «end» := i }
    let s1 ← K.compress state blocks1 s
    let values1 := index_mut_back s1
    ok (cont (iter1, values1))

def treeBatches {G : Usize} (K : Kernel G)
  {N : Usize}
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
  (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs) (first : U32)
  (values : Nodes N) :
  Result (Nodes N)
  := do
  loop
    (fun (iter1, values1) => treeBatchStep K state
      adrs first iter1 values1)
    (iter, values)

def treeActive {G : Usize} (K : Kernel G)
  {N : Usize} (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (first : U32) (values : Nodes N) (count : Usize) :
  Result (Usize × (Nodes N))
  := do
  let i ← count / G
  let «end» ← i * G
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» } G
  let values1 ←
    treeBatches K iter state adrs first values
  ok («end», values1)

def treeParents {G : Usize} (K : Kernel G)
  {N : Usize} (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (first : U32) (values : Nodes N) (count : Usize) :
  Result (Usize × (Nodes N))
  := do
  let b ← match N.val with
            | 24 => ok true
            | 32 => ok true
            | _ => ok false
  if b
  then
    if count < G
    then ok (0#usize, values)
    else
      let b1 ← K.available
      if b1
      then treeActive K state adrs first values count
      else ok (0#usize, values)
  else ok (0#usize, values)

def pathBlockStep {G : Usize}
  {N : Usize} (adrs : slhdsa.address.Adrs) (values : Nodes N)
  (sig : Slice U8) (height : Usize) (offset : Usize)
  (j : Usize) (iter : core.ops.range.Range Usize)
  (indices : Slice U32) (blocks : Blocks G) :
  Result (ControlFlow ((core.ops.range.Range Usize) × (Slice U32) ×
    (Blocks G)) ((Slice U32) × (Blocks G)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (indices, blocks))
  | some lane =>
    let (block, index_mut_back) ← Array.index_mut_usize blocks lane
    let i ← j + lane
    let position ← Slice.index_usize indices i
    let i1 ← position >>> 1#i32
    let indices1 ← Slice.update indices i i1
    let i2 ← height + 1#usize
    let i3 ← i * i2
    let i4 ← i3 + 1#usize
    let i5 ← i4 + offset
    let start ← N * i5
    let i6 ← start + N
    let sibling ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        U8) sig { start, «end» := i6 }
    let a ← Slice.index_usize values i
    let node ← lift (Array.to_slice a)
    let i7 ← lift (position &&& 1#u32)
    let (left, right) ←
      if i7 = 0#u32
      then ok (node, sibling)
      else ok (sibling, node)
    let i8 ← Slice.index_usize indices1 i
    let a1 ← slhdsa.address.Adrs.with_word3 adrs i8
    let block1 ← makeBlock N block a1 left right
    let a2 := index_mut_back block1
    ok (cont (iter1, indices1, a2))

def pathBlocks {G : Usize}
  {N : Usize} (iter : core.ops.range.Range Usize) (adrs : slhdsa.address.Adrs)
  (values : Nodes N) (indices : Slice U32)
  (sig : Slice U8) (height : Usize) (offset : Usize)
  (j : Usize) (blocks : Blocks G) :
  Result ((Slice U32) × (Blocks G))
  := do
  loop
    (fun (iter1, indices1, blocks1) =>
      pathBlockStep adrs values sig
      height offset j iter1 indices1 blocks1)
    (iter, indices, blocks)

def pathBatchStep {G : Usize} (K : Kernel G)
  {N : Usize} (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (sig : Slice U8) (height : Usize) (offset : Usize)
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
  (values : Nodes N) (indices : Slice U32) :
  Result (ControlFlow ((core.iter.adapters.step_by.StepBy (core.ops.range.Range
    Usize)) × (Nodes N) × (Slice U32)) ((Slice (Array
    U8 N)) × (Slice U32)))
  := do
  let (o, iter1) ←
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (values, indices))
  | some j =>
    let a := Array.repeat 128#usize 0#u8
    let blocks := Array.repeat G a
    let (indices1, blocks1) ←
      pathBlocks
        { start := 0#usize, «end» := G } adrs values
        indices sig height offset j blocks
    let i ← j + G
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N)) values
        { start := j, «end» := i }
    let s1 ← K.compress state blocks1 s
    let values1 := index_mut_back s1
    ok (cont (iter1, values1, indices1))

def pathBatches {G : Usize} (K : Kernel G)
  {N : Usize}
  (iter : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
  (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (values : Nodes N) (indices : Slice U32)
  (sig : Slice U8) (height : Usize) (offset : Usize) :
  Result ((Nodes N) × (Slice U32))
  := do
  loop
    (fun (iter1, values1, indices1) =>
      pathBatchStep K state adrs sig height
      offset iter1 values1 indices1)
    (iter, values, indices)

def pathActive {G : Usize} (K : Kernel G)
  {N : Usize} (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (values : Nodes N) (indices : Slice U32)
  (sig : Slice U8) (height : Usize) (offset : Usize) :
  Result (Usize × (Nodes N) × (Slice U32))
  := do
  let i := Slice.len values
  let i1 ← i / G
  let «end» ← i1 * G
  let iter ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      { start := 0#usize, «end» } G
  let (values1, indices1) ←
    pathBatches K iter state adrs values indices sig
      height offset
  ok («end», values1, indices1)

def pathParents {G : Usize} (K : Kernel G)
  {N : Usize} (state : Array U64 8#usize) (adrs : slhdsa.address.Adrs)
  (values : Nodes N) (indices : Slice U32)
  (sig : Slice U8) (height : Usize) (offset : Usize) :
  Result (Usize × (Nodes N) × (Slice U32))
  := do
  let b ← match N.val with
            | 24 => ok true
            | 32 => ok true
            | _ => ok false
  if b
  then
    let i := Slice.len values
    if i < G
    then ok (0#usize, values, indices)
    else
      let b1 ← K.available
      if b1
      then
        pathActive K state adrs values indices sig height
          offset
      else ok (0#usize, values, indices)
  else ok (0#usize, values, indices)

end slhdsa.PlatformParent.Driver
