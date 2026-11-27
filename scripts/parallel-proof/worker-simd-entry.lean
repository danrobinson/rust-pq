open ParallelWorkerInterleave ParallelWorkerScatter

abbrev Group (N : Usize) := Array (Array U8 N) WIDTH#usize

/-- The direct SIMD job has finished all hash computations before entering
the write loop. Its actual mask, address indices and lane order are retained. -/
theorem direct_simd_entry {N : Usize} {H : Type}
    (stride : Usize) (a : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (choices : alloc.vec.Vec U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (item : shake.slh.parallel.WorkItem) (first : U16) (active height : U8)
    (kind : item.kind = .ForsShakeDirect first active height)
    (ids : Array U32 WIDTH#usize) (rows : Group N)
    (constructed : core.array.from_fn WIDTH#usize
      (shake.slh.parallel.dispatch.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (UScalar.cast .Usize first, UScalar.cast .Usize active, a,
        core.convert.num.FromU32U8.from height, choices) = ok ids)
    (hashed : shake.slh.parallel.shake_fors_simd.nodes_active sk seed addr ids
      (UScalar.cast .Usize active) (core.convert.num.FromU32U8.from height) = ok rows) :
    interpreted.dispatch concurrentOps stride a addr sk seed layers choices xmss leaves direct split item =
      interpreted.dispatch_loop3 concurrentOps ⟨0#usize,UScalar.cast .Usize active⟩
        stride direct (UScalar.cast .Usize first) (core.convert.num.FromU32U8.from height) rows := by
  simp only [interpreted.dispatch,kind,lift,lifted_ok,pure_bind,constructed,hashed]

theorem split_simd_entry {N : Usize} {H : Type}
    (stride : Usize) (a : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (choices : alloc.vec.Vec U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (item : shake.slh.parallel.WorkItem) (first : U16) (active height subH : U8)
    (chunk : U32) (base chunks : Usize)
    (kind : item.kind = .ForsShakeSplit first active height subH chunk base chunks)
    (remaining : U32) (ids : Array U32 WIDTH#usize) (rows : Group N)
    (checked : core.convert.num.FromU32U8.from height - core.convert.num.FromU32U8.from subH = ok remaining)
    (constructed : core.array.from_fn WIDTH#usize
      (shake.slh.parallel.dispatch.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (UScalar.cast .Usize first, UScalar.cast .Usize active, a, core.convert.num.FromU32U8.from height,
        choices,remaining,chunk) = ok ids)
    (hashed : shake.slh.parallel.shake_fors_simd.nodes_active sk seed addr ids
      (UScalar.cast .Usize active) (core.convert.num.FromU32U8.from subH) = ok rows) :
    interpreted.dispatch concurrentOps stride a addr sk seed layers choices xmss leaves direct split item =
      interpreted.dispatch_loop4 concurrentOps ⟨0#usize,UScalar.cast .Usize active⟩
        split chunk base chunks rows := by
  simp only [interpreted.dispatch,kind,lift,lifted_ok,pure_bind,checked,constructed,hashed]

theorem low_simd_entry {N : Usize} {H : Type}
    (stride : Usize) (a : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (choices : alloc.vec.Vec U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (item : shake.slh.parallel.WorkItem) (first : U16) (active low : U8)
    (kind : item.kind = .ForsShakeLow first active low)
    (ids : Array U32 WIDTH#usize) (secrets : Group N)
    (constructed : core.array.from_fn WIDTH#usize
      (shake.slh.parallel.dispatch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (UScalar.cast .Usize first,UScalar.cast .Usize active,a,choices) = ok ids)
    (hashed : shake.slh.parallel.shake_fors_simd.secrets sk seed addr ids
      (UScalar.cast .Usize active) = ok secrets) :
    interpreted.dispatch concurrentOps stride a addr sk seed layers choices xmss leaves direct split item =
      (do interpreted.dispatch_loop1 concurrentOps ⟨0#usize,UScalar.cast .Usize active⟩
            stride direct (UScalar.cast .Usize first) secrets
          interpreted.dispatch_loop2 concurrentOps ⟨0#u32,core.convert.num.FromU32U8.from low⟩
            stride addr sk seed direct (UScalar.cast .Usize first) (UScalar.cast .Usize active) ids) := by
  simp only [interpreted.dispatch,kind,lift,lifted_ok,pure_bind,constructed,hashed]

/-- At each authentication height the native group computes a new array.
The complete row loop is resumed at lane zero with those exact bytes. -/
theorem low_simd_round {N : Usize} {H A : Type}
    (stride first active : Usize) (addr : address.Adrs) (sk seed : Array U8 N)
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (ids : Array U32 WIDTH#usize) (it : core.ops.range.Range U32)
    (siblings : Array U32 WIDTH#usize) (rows : Group N) (k : Unit → Program H A)
    (live : it.start.val < it.end.val)
    (constructed : core.array.Array.map
      (shake.slh.parallel.dispatch.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N) ids it.start = ok siblings)
    (hashed : shake.slh.parallel.shake_fors_simd.nodes_active sk seed addr siblings active it.start = ok rows) :
    ∃ next : core.ops.range.Range U32, next.start.val=it.start.val+1 ∧ next.end=it.end ∧
      (interpreted.dispatch_loop2 concurrentOps it stride addr sk seed refs first active ids >>= k) =
      (interpreted.dispatch_loop2_loop0 concurrentOps ⟨0#usize,active⟩ stride refs first it.start rows >>=
        fun () => interpreted.dispatch_loop2 concurrentOps next stride addr sk seed refs first active ids >>= k) := by
  obtain ⟨⟨tag,next⟩, advance, tagEq, inc, stop⟩ := spec_imp_exists
    (core.iter.range.IteratorRange.next_U32_some_spec it live)
  subst tag
  refine ⟨next,inc,stop,?_⟩
  let body := interpreted.dispatch_loop2.body concurrentOps stride addr sk seed refs first active ids
  have current : body it =
      (do interpreted.dispatch_loop2_loop0 concurrentOps ⟨0#usize,active⟩ stride refs first it.start rows
          pure (cont next)) := by
    simp only [body,interpreted.dispatch_loop2.body,advance,lifted_ok,pure_bind,constructed,hashed]
  change (runLoop body it >>= k) = (_ >>= fun () => runLoop body next >>= k)
  rw [runLoop_unfold body it,current]
  simp only [bind_assoc,pure_bind]

/-- Each height has its own native array of sibling nodes. Peer operations
inside each height use the same heap as the next height and the caller. -/
inductive LowHeights {N : Usize} {H A : Type}
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (first stride active limit : Nat) (values : Nat → Group N) :
    Nat → H → List (Program H A) → H → List (Program H A) → Prop where
  | done {j h peers} (past : limit ≤ j) : LowHeights refs first stride active limit values j h peers h peers
  | height {j h mid dest peers peers' others} (live : j < limit)
      (lanes : Scatter active (storeAt refs (values j).val (fun i => (first+i)*stride+1+j))
        0 h peers mid peers')
      (rest : LowHeights refs first stride active limit values (j+1) mid peers' dest others) :
      LowHeights refs first stride active limit values j h peers dest others

theorem low_simd_rounds_complete {N : Usize} {H A : Type}
    (stride first active : Usize) (limit : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (ids : Array U32 WIDTH#usize) (values : Nat → Group N) (k : Unit → Program H A)
    (width : ∀ j < limit.val, active.val ≤ (values j).length)
    (sumFits : ∀ i < active.val, first.val+i ≤ Usize.max)
    (room : ∀ j < limit.val, ∀ i < active.val, (first.val+i)*stride.val+1+j < refs.length)
    (hashes : ∀ j : U32, j.val < limit.val → ∃ siblings,
      core.array.Array.map (shake.slh.parallel.dispatch.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N)
        ids j = ok siblings ∧ shake.slh.parallel.shake_fors_simd.nodes_active sk seed addr siblings active j =
        ok (values j.val))
    {j h peers dest others}
    (sched : LowHeights refs first.val stride.val active.val limit.val values j h peers dest others)
    (it : core.ops.range.Range U32) (start : it.start.val = j) (stop : it.end = limit) :
    Steps h ((interpreted.dispatch_loop2 concurrentOps it stride addr sk seed refs first active ids >>= k) :: peers)
      dest (k () :: others) := by
  induction sched generalizing it with
  | done past =>
    obtain ⟨⟨opt,tail⟩, no, optEq, tailEq⟩ := spec_imp_exists
      (core.iter.range.IteratorRange.next_U32_none_spec it (by rw [stop,start]; exact past))
    subst opt tail
    change Steps _ ((runLoop _ it >>= k) :: _) _ _
    rw [runLoop_unfold]
    simp only [interpreted.dispatch_loop2.body,no,lifted_ok,pure_bind]
    exact .refl
  | height live lanes rest ih =>
    have enabled : it.start.val < limit.val := start ▸ live
    obtain ⟨siblings,mapped,hashed⟩ := hashes it.start enabled
    obtain ⟨next,inc,ends,current⟩ := low_simd_round stride first active addr sk seed refs ids it
      siblings (values it.start.val) k (stop ▸ enabled) mapped hashed
    rw [current]
    exact Relation.ReflTransGen.trans
      (lane_2_loop0_complete refs stride first it.start (values it.start.val) active
        (fun () => interpreted.dispatch_loop2 concurrentOps next stride addr sk seed refs first active ids >>= k)
        (width _ enabled) sumFits (room _ enabled) _ _ _ _ (start ▸ lanes))
      (ih next (by omega) (ends.trans stop))

/-- An entire grouped low-FORS job, from the generated enum arm, through
secret publication, through every sibling-height and lane, into its caller. -/
theorem low_simd_job {N : Usize} {H A : Type}
    (stride : Usize) (a : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (choices : alloc.vec.Vec U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (item : shake.slh.parallel.WorkItem) (first : U16) (active low : U8)
    (kind : item.kind = .ForsShakeLow first active low)
    (ids : Array U32 WIDTH#usize) (secrets : Group N)
    (constructed : core.array.from_fn WIDTH#usize
      (shake.slh.parallel.dispatch.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (UScalar.cast .Usize first,UScalar.cast .Usize active,a,choices) = ok ids)
    (hashed : shake.slh.parallel.shake_fors_simd.secrets sk seed addr ids
      (UScalar.cast .Usize active) = ok secrets)
    (values : Nat → Group N) (k : Unit → Program H A)
    (width : (UScalar.cast .Usize active).val ≤ secrets.length)
    (widths : ∀ j < (core.convert.num.FromU32U8.from low).val,
      (UScalar.cast .Usize active).val ≤ (values j).length)
    (sumFits : ∀ i < (UScalar.cast .Usize active).val, (UScalar.cast .Usize first).val+i ≤ Usize.max)
    (space : ∀ i < (UScalar.cast .Usize active).val, ((UScalar.cast .Usize first).val+i)*stride.val < direct.length)
    (rooms : ∀ j < (core.convert.num.FromU32U8.from low).val, ∀ i < (UScalar.cast .Usize active).val,
      ((UScalar.cast .Usize first).val+i)*stride.val+1+j < direct.length)
    (hashes : ∀ j : U32, j.val < (core.convert.num.FromU32U8.from low).val → ∃ siblings,
      core.array.Array.map (shake.slh.parallel.dispatch.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U32 N)
        ids j = ok siblings ∧ shake.slh.parallel.shake_fors_simd.nodes_active sk seed addr siblings
          (UScalar.cast .Usize active) j = ok (values j.val))
    {h mid dest : H} {peers peers' others : List (Program H A)}
    (firstPass : Scatter (UScalar.cast .Usize active).val
      (storeAt direct secrets.val (fun i => ((UScalar.cast .Usize first).val+i)*stride.val)) 0 h peers mid peers')
    (remaining : LowHeights direct (UScalar.cast .Usize first).val stride.val (UScalar.cast .Usize active).val
      (core.convert.num.FromU32U8.from low).val values 0 mid peers' dest others) :
    Steps h ((interpreted.dispatch concurrentOps stride a addr sk seed layers choices xmss leaves direct split item >>= k)
      :: peers) dest (k () :: others) := by
  rw [low_simd_entry stride a addr sk seed layers choices xmss leaves direct split item first active low
    kind ids secrets constructed hashed, bind_assoc]
  apply Relation.ReflTransGen.trans (lane_1_complete direct stride _ secrets _ _ width sumFits space _ _ _ _ firstPass)
  exact low_simd_rounds_complete stride _ _ _ addr sk seed direct ids values k widths sumFits rooms hashes
    remaining _ rfl rfl
