"""Certificates for the three remaining one-publication dispatch variants."""


def scalar_witness(generated):
    cases = (
        (
            "xmss_subtree",
            "XmssSubtree layer idx height slot",
            "xmss",
            "slot",
            "shake.xmss.xmss_node sk idx height seed leafAddr",
            "unique XMSS subtree slot",
        ),
        (
            "xmss_leaf",
            "XmssLeafPk layer",
            "leaves",
            "(UScalar.cast .Usize layer)",
            "shake.xmss.xmss_node sk key 0#u32 seed leafAddr",
            "unique XMSS leaf PK slot",
        ),
        (
            "fors_split",
            "ForsNodeSplit idx height slot",
            "split",
            "slot",
            "shake.fors.fors_node sk idx height seed addr",
            "unique FORS split slot",
        ),
    )
    text = []
    for name, arm, vector, slot, primitive, message in cases:
        if message not in generated:
            raise ValueError(f"missing scalar publication {message}")
        is_xmss = vector != "split"
        text.append(f"""
theorem {name}_step {{N : Std.Usize}} {{H : Type}}
    (stride : Std.Usize) (a : Std.U32) (addr : address.Adrs)
    {"(layer : Std.U16) (leafAddr : address.Adrs) (key : Std.U32)" if is_xmss else ""}
    {"(idx height : Std.U32) (slot : Std.Usize)" if vector != "leaves" else ""}
    (sk seed node : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (indices : alloc.vec.Vec Std.U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array Std.U8 N)))
    (ref : ParallelWorkerCells.Ref H (Array Std.U8 N)) (h : H)
    (l r : List (ParallelWorkerInterleave.Program H Unit))
    (item : shake.slh.parallel.WorkItem) (kind : item.kind = .{arm})
    {"(layerRead : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) layers (UScalar.cast .Usize layer) = ok (leafAddr,key))" if is_xmss else ""}
    (computed : {primitive} = ok node)
    (indexed : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) {vector} {slot} = ok ref)
    (empty : ref.read h = none) :
    ParallelWorkerInterleave.Step h
      (l ++ interpreted.dispatch concurrentOps stride a addr sk seed layers indices
        xmss leaves direct split item :: r) (ref.write node h) (l ++ pure () :: r) := by
  have lifted {{T : Type}} (x : T) :
      (liftM (ok x) : ParallelWorkerInterleave.Program H T) = pure x :=
    ParallelWorkerInterleave.lift_ok x
  simp only [interpreted.dispatch,kind,{("lift,layerRead," if is_xmss else "")}computed,indexed,lifted,pure_bind]
  exact (by
    simpa [concurrentOps,empty,core.result.Result.expect,lifted] using
      ParallelWorkerInterleave.set_step ref node
        (fun v => (liftM (core.result.Result.expect (Array.Insts.CoreFmtDebug N core.fmt.DebugU8) v
          (toStr "{message}")) : ParallelWorkerInterleave.Program H Unit)) h l r)
""")
    return "\n".join(text)
