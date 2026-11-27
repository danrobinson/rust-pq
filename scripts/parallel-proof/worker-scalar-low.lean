open ParallelWorkerScalarLow ParallelWorkerInterleave ParallelWorkerScatter

/-- Under the actual subtree primitive result, the next caller-selected
physical write is the sibling of the message-selected FORS path at height j. -/
theorem scalar_auth_advance {N : Usize} {H A : Type}
    (a t digit low : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N))) (base : Usize)
    (values : List (Array U8 N)) (k : Unit → Program H A)
    (height : a.val < 32) (range : low.val ≤ a.val) (width : low.val ≤ values.length)
    (room : base.val + low.val < refs.length)
    (fits : ∀ j < low.val, sibling t.val a.val j digit.val ≤ U32.max)
    (nodes : ∀ (j pos : U32) (hj : j.val < low.val), pos.val = sibling t.val a.val j.val digit.val →
      shake.fors.fors_node sk pos j seed addr = ok (values[j.val]'(by omega)))
    (it : core.ops.range.Range U32) (h dest : H) (peers : List (Program H A))
    (ends : it.end = low) (live : it.start.val < low.val)
    (written : storeAt refs values (fun j => base.val + 1 + j) it.start.val h = some dest) :
    ∃ next : core.ops.range.Range U32, next.start.val = it.start.val + 1 ∧ next.end = low ∧
      Step h ((interpreted.dispatch_loop0 concurrentOps it a addr sk seed refs t digit base >>= k) :: peers)
        dest ((interpreted.dispatch_loop0 concurrentOps next a addr sk seed refs t digit base >>= k) :: peers) := by
  obtain ⟨free, rfl⟩ := (storeAt_eq refs values (fun j => base.val+1+j) _ h dest (by omega) (by omega)).mp written
  obtain ⟨⟨tag,next⟩, advance, tagEq, inc, stop⟩ := spec_imp_exists
    (core.iter.range.IteratorRange.next_U32_some_spec it (ends ▸ live))
  subst tag
  obtain ⟨pos, calculated, pv⟩ := spec_imp_exists
    (index_spec digit a t it.start height (by omega) (fits _ live))
  obtain ⟨q,shift,start,eqQ,eqShift,eqStart,eqPos⟩ := intermediate digit a t it.start pos calculated
  have node := nodes it.start pos live pv
  have cap := refs.property
  change refs.length ≤ Usize.max at cap
  obtain ⟨off,eqOff,ov⟩ := spec_imp_exists (UScalar.add_spec (x:=base) (y:=1#usize)
    (by rw [UScalar.max_USize_eq]; change _+1 ≤ _; omega))
  obtain ⟨slot,eqSlot,sv⟩ := spec_imp_exists (UScalar.add_spec (x:=off) (y:=UScalar.cast .Usize it.start)
    (by rw [UScalar.max_USize_eq, U32.cast_Usize_val_eq,ov]; change _+1+_ ≤ _; omega))
  have position : slot.val = base.val + 1 + it.start.val := by rw [sv,ov,U32.cast_Usize_val_eq]; rfl
  obtain ⟨ref,indexRef,rfl⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec refs slot (by omega))
  refine ⟨next,inc,stop.trans ends,?_⟩
  let body := interpreted.dispatch_loop0.body concurrentOps a addr sk seed refs t digit base
  let ref := refs.val[slot.val]'(by change slot.val < refs.length; omega)
  let value := values[it.start.val]'(by omega)
  let check := fun r => (liftM (core.result.Result.expect (Array.Insts.CoreFmtDebug N core.fmt.DebugU8) r
      (toStr "unique FORS low node slot")) : Program H Unit)
  have current : body it = (do let r ← ParallelWorkerInterleave.set ref value
                               check r; pure (cont next)) := by
    simp only [body, interpreted.dispatch_loop0.body, advance, lifted_ok, pure_bind, eqQ, lift, eqShift,
      eqStart, eqPos, node, eqOff, eqSlot, alloc.vec.Vec.index_slice_index, indexRef, concurrentOps,
      ref, value, check]
  change Step h ((runLoop body it >>= k) :: peers) _ ((runLoop body next >>= k) :: peers)
  rw [runLoop_unfold body it, current]
  simp only [bind_assoc,pure_bind]
  have store := set_step ref value (fun r => do check r; runLoop body next >>= k) h [] peers
  simp only [ref,value,position,free,check,core.result.Result.expect,lifted_ok,pure_bind,
    List.nil_append] at store ⊢
  exact store

theorem scalar_auth_done {N : Usize} {H A : Type}
    (a t digit low : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N))) (base : Usize)
    (k : Unit → Program H A) (it : core.ops.range.Range U32) (ends : it.end = low)
    (past : low.val ≤ it.start.val) :
    (interpreted.dispatch_loop0 concurrentOps it a addr sk seed refs t digit base >>= k) = k () := by
  obtain ⟨⟨opt,tail⟩, no, optEq, tailEq⟩ := spec_imp_exists
    (core.iter.range.IteratorRange.next_U32_none_spec it (ends ▸ past))
  subst opt tail
  change (runLoop _ it >>= k) = _
  rw [runLoop_unfold]
  simp only [interpreted.dispatch_loop0.body, no, lifted_ok, pure_bind]

theorem scalar_auth_complete {N : Usize} {H A : Type}
    (a t digit low : U32) (addr : address.Adrs) (sk seed : Array U8 N)
    (refs : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N))) (base : Usize)
    (values : List (Array U8 N)) (k : Unit → Program H A)
    (height : a.val < 32) (range : low.val ≤ a.val) (width : low.val ≤ values.length)
    (room : base.val + low.val < refs.length)
    (fits : ∀ j < low.val, sibling t.val a.val j digit.val ≤ U32.max)
    (nodes : ∀ (j pos : U32) (hj : j.val < low.val), pos.val = sibling t.val a.val j.val digit.val →
      shake.fors.fors_node sk pos j seed addr = ok (values[j.val]'(by omega)))
    {h dest : H} {peers others : List (Program H A)}
    (trace : Scatter low.val (storeAt refs values (fun j => base.val+1+j)) 0 h peers dest others) :
    Steps h ((interpreted.dispatch_loop0 concurrentOps ⟨0#u32,low⟩ a addr sk seed refs t digit base >>= k)
      :: peers) dest (k () :: others) :=
  realize low _ _ _ (scalar_auth_advance a t digit low addr sk seed refs base values k height range width room fits nodes)
    (scalar_auth_done a t digit low addr sk seed refs base k) trace _ rfl rfl

/-- The scalar low tree job publishes its secret before its first
authentication sibling. Both values come from the generated hash calls. -/
theorem scalar_secret_step {N : Usize} {H A : Type}
    (stride : Usize) (a t low : U32) (addr : address.Adrs) (sk seed secret : Array U8 N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (choices : alloc.vec.Vec U32)
    (xmss leaves refs split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (item : shake.slh.parallel.WorkItem) (kind : item.kind = .ForsTreeLow t low)
    (k : Unit → Program H A) (h : H) (l r : List (Program H A))
    (selected : t.val < choices.length) (height : a.val < 32)
    (fits : t.val * 2^a.val + choices.val[t.val].val ≤ U32.max)
    (room : t.val * stride.val < refs.length)
    (empty : refs.val[t.val * stride.val].read h = none)
    (computed : ∀ pos : U32, pos.val = t.val*2^a.val + choices.val[t.val].val →
      shake.fors.fors_sk_gen sk seed addr pos = ok secret) :
    ∃ base : Usize, base.val = t.val * stride.val ∧
      Step h (l ++ (interpreted.dispatch concurrentOps stride a addr sk seed layers choices
        xmss leaves refs split item >>= k) :: r)
        (refs.val[t.val * stride.val].write secret h)
        (l ++ (interpreted.dispatch_loop0 concurrentOps ⟨0#u32,low⟩ a addr sk seed refs t
          choices.val[t.val] base >>= k) :: r) := by
  let ti := UScalar.cast .Usize t
  have tv : ti.val = t.val := U32.cast_Usize_val_eq t
  obtain ⟨digit,getDigit,indexed⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec choices ti (tv ▸ selected))
  obtain ⟨pos,calculated,pv⟩ := spec_imp_exists (secret_index_spec t a digit height (by simpa only [indexed,tv] using fits))
  obtain ⟨shifted,shift,added⟩ := secret_intermediate t a digit pos calculated
  have hash := computed pos (by simpa only [indexed,tv] using pv)
  have cap := refs.property
  change refs.length ≤ Usize.max at cap
  obtain ⟨base,getBase,bv⟩ := spec_imp_exists (UScalar.mul_spec (x:=ti) (y:=stride)
    (by rw [tv,UScalar.max_USize_eq]; omega))
  rw [tv] at bv
  obtain ⟨ref,getRef,indexRef⟩ := spec_imp_exists (alloc.vec.Vec.index_usize_spec refs base (by omega))
  refine ⟨base,bv,?_⟩
  let check := fun b => (liftM (core.result.Result.expect (Array.Insts.CoreFmtDebug N core.fmt.DebugU8) b
    (toStr "unique FORS sk slot")) : Program H Unit)
  let next := interpreted.dispatch_loop0 concurrentOps ⟨0#u32,low⟩ a addr sk seed refs t digit base
  have current : interpreted.dispatch concurrentOps stride a addr sk seed layers choices
        xmss leaves refs split item = (do let b ← ParallelWorkerInterleave.set ref secret
                                          check b; next) := by
    simp only [interpreted.dispatch,kind,lift, lifted_ok,pure_bind,alloc.vec.Vec.index_slice_index,
      ←show ti = UScalar.cast .Usize t from rfl, getDigit, getBase,shift,added,hash,getRef,
      concurrentOps,next,check]
  rw [current]
  simp only [bind_assoc]
  have store := set_step ref secret (fun b => do check b; next >>= k) h l r
  simp only [check,next,indexRef,bv,indexed,tv,empty,core.result.Result.expect,lifted_ok,pure_bind] at store ⊢
  exact store

theorem scalar_low_job {N : Usize} {H A : Type}
    (stride : Usize) (a t low : U32) (addr : address.Adrs) (sk seed secret : Array U8 N)
    (layers : alloc.vec.Vec (address.Adrs × U32)) (choices : alloc.vec.Vec U32)
    (xmss leaves refs split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array U8 N)))
    (item : shake.slh.parallel.WorkItem) (kind : item.kind = .ForsTreeLow t low)
    (k : Unit → Program H A) (h final : H) (peers finalPeers : List (Program H A))
    (selected : t.val < choices.length) (height : a.val < 32) (range : low.val ≤ a.val)
    (fits : t.val*2^a.val + choices.val[t.val].val ≤ U32.max)
    (room : t.val*stride.val + low.val < refs.length)
    (empty : (refs.val[t.val*stride.val]'(by change t.val*stride.val < refs.length; omega)).read h = none)
    (skgen : ∀ pos : U32, pos.val = t.val*2^a.val + choices.val[t.val].val →
      shake.fors.fors_sk_gen sk seed addr pos = ok secret)
    (values : List (Array U8 N)) (width : low.val ≤ values.length)
    (nodeFits : ∀ j < low.val, sibling t.val a.val j choices.val[t.val].val ≤ U32.max)
    (nodes : ∀ (j pos : U32) (hj : j.val < low.val),
      pos.val = sibling t.val a.val j.val choices.val[t.val].val →
      shake.fors.fors_node sk pos j seed addr = ok (values[j.val]'(by omega)))
    (remaining : Scatter low.val (storeAt refs values (fun j => t.val*stride.val+1+j)) 0
      ((refs.val[t.val*stride.val]'(by change t.val*stride.val < refs.length; omega)).write secret h) peers final finalPeers) :
    Steps h ((interpreted.dispatch concurrentOps stride a addr sk seed layers choices
        xmss leaves refs split item >>= k) :: peers) final (k () :: finalPeers) := by
  obtain ⟨base,position,first⟩ := scalar_secret_step stride a t low addr sk seed secret layers choices
    xmss leaves refs split item kind k h [] peers selected height fits (by omega) empty skgen
  apply Relation.ReflTransGen.trans first.single
  exact scalar_auth_complete a t choices.val[t.val] low addr sk seed refs base values k
    height range width (by omega) nodeFits nodes (by simpa only [position] using remaining)
