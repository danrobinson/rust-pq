import Cachepath.WotsRowsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.cache.builder.nativeShake.Vector
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
abbrev Batch (N : Usize) := Array (Array U8 N) machine.width
abbrev Make (N : Usize) := Usize → Usize → Result (Batch N)

private def body {N : Usize} (mk : Make N) (len : Usize) (q : Rows N × Usize) :
    Result (ControlFlow (Rows N × Usize) (Rows N)) := do
  let out := q.1
  let off := q.2
  if off < len then
    let i ← len - off
    let active ← lift (core.cmp.impls.OrdUsize.min i machine.width)
    let batch ← mk off active
    let stop ← off + active
    let (s,back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice (Array U8 N)) out ⟨off,stop⟩
    let src ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) batch ⟨active⟩
    let updated ← core.slice.Slice.copy_from_slice (Array.Insts.CoreMarkerCopy N core.marker.CopyU8) s src
    ok (cont (back updated,stop))
  else ok (done out)

def MakeCorrect {N : Usize} (mk : Make N) (len : Usize) (f : Nat → Spec.Bytes) :=
  ∀ (off active : Usize), off.val < len.val → active.val = min (len.val-off.val) machine.width.val →
    mk off active ⦃ b => ∀ j < active.val, bytes b.val[j]!.val = f (off.val+j) ⦄

omit machine in
theorem min_val (a b : Usize) : (core.cmp.impls.OrdUsize.min a b).val = min a.val b.val := by
  change (if b.val < a.val then b else a).val=_
  split <;> omega

theorem row_loop {N : Usize} (mk : Make N) (out : Rows N) (f : Nat → Spec.Bytes)
    (positive : 0 < machine.width.val) (correct : MakeCorrect mk out.len f) :
    loop (body mk out.len) (out,0#usize) ⦃ r => Row r out.length f ⦄ := by
  apply loop.spec_decr_nat (measure := fun q : Rows N × Usize => out.length-q.2.val)
    (inv := fun q => q.1.length=out.length ∧ q.2.val≤out.length ∧ ∀ j < q.2.val, bytes q.1.val[j]!.val=f j)
  · rintro ⟨s,off⟩ ⟨len,limit,prev⟩
    simp only at len limit prev ⊢
    simp only [body]
    by_cases live : off < out.len
    · have lt : off.val < out.length := live
      simp only [ite_eq_left live]
      step as ⟨diff,eq⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min diff machine.width
      have activeVal : active.val=min (out.length-off.val) machine.width.val := by rw [min_val,eq,Slice.len_val]
      have aw : active.val≤machine.width.val := activeVal ▸ Nat.min_le_right _ _
      have enough : off.val+active.val≤out.length := by omega
      have bump : 0 < active.val := by omega
      step with correct off active lt activeVal as ⟨batch,values⟩
      step as ⟨stop,next⟩
      step as ⟨dst,back,_,dlen,backEq⟩
      step as ⟨src,srcEq,slen⟩
      step as ⟨w,cp⟩
      all_goals try omega
      change stop.val = off.val + active.val at next
      change src.length = active.val at slen
      change src.val = batch.to_slice.val.slice 0 active.val at srcEq
      subst w
      rw [backEq]
      refine ⟨by simpa using len,by omega,?_,by omega⟩
      intro j hj
      rw [Slice.setSlice!_val]
      by_cases before : j < off.val
      · rw [List.getElem!_setSlice!_prefix _ _ _ _ before,prev j before]
      · have inside : j-off.val < active.val := by omega
        rw [List.getElem!_setSlice!_middle _ _ _ _ (by change off.val ≤ j ∧ j-off.val < src.length ∧ j < s.length; omega),
          srcEq,Array.val_to_slice,List.getElem!_slice _ _ _ _ (by simpa using And.intro aw inside),Nat.zero_add,values _ inside]
        congr 1; omega
    · simp only [ite_eq_right live,step_simps]
      exact ⟨len,fun j hj => prev j (by change ¬off.val < out.length at live; omega)⟩
  · exact ⟨rfl,by simp,by simp⟩


variable [leaves : Leaves machine]

private def makeLeaves {N : Usize} (sk seed : Array U8 N) (a : address.Adrs) (base : Usize) : Make N :=
  fun off active => do
    let keys ← core.array.from_fn machine.width (fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N) (base,off,active)
    Leaves.gen sk seed a keys

private def makeParents {N : Usize} (seed : Array U8 N) (a : address.Adrs) (h : U32)
    (base : Usize) (children : Rows N) : Make N := fun off active => do
  let ids ← core.array.from_fn machine.width (hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N) (off,active)
  let addresses ← core.array.Array.map (hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N) ids (a,h,base)
  let left ← core.array.Array.map (hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids children
  let right ← core.array.Array.map (hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids children
  ShakeBatch.shake.batch.pair seed addresses left right

private theorem leaves_loop_eq {N : Usize} (sk seed : Array U8 N) (a : address.Adrs)
    (base len : Usize) : (fun (out,off) => fill_xmss_leaves_loop.body sk seed a base len out off) =
    body (makeLeaves sk seed a base) len := by
  funext ⟨out,off⟩
  simp only [fill_xmss_leaves_loop.body,body,makeLeaves,Std.bind_assoc]

omit leaves in
private theorem parents_loop_eq {N : Usize} (seed : Array U8 N) (a : address.Adrs) (h : U32)
    (base : Usize) (children : Rows N) (len : Usize) :
    (fun (out,off) => hash_pairs_loop.body seed a h base children len out off) =
    body (makeParents seed a h base children) len := by
  funext ⟨out,off⟩
  simp only [hash_pairs_loop.body,body,makeParents,Std.bind_assoc]

def LeavesCorrect {N : Usize} (p : params.Params) :=
  ∀ (sk seed : Array U8 N) (a : address.Adrs) (keys : Array U32 machine.width),
    Leaves.gen sk seed a keys ⦃ batch => ∀ j < machine.width.val,
      bytes batch.val[j]!.val = Value p sk seed a 0 keys.val[j]!.val ⦄

omit leaves in
private theorem leafKeys {N : Usize} (base off active : Usize) (pos : 0 < active.val)
    (fits : base.val+off.val+active.val ≤ 512) :
    core.array.from_fn machine.width (fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32 N)
      (base,off,active) ⦃ keys => ∀ j < machine.width.val, keys.val[j]!.val = base.val+off.val+min j (active.val-1) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width _ (base,off,active)
    (fun j (x : U32) => x.val = base.val+off.val+min j (active.val-1)) ?_)
  · intro ks spec j hj; simpa only [Array.getElem!_Nat_eq] using spec j hj
  intro i hi
  change fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut (N:=N) (base,off,active) i ⦃ _ ⦄
  unfold fill_xmss_leaves.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut
  have bits := System.Platform.numBits_eq
  step as ⟨first,eq⟩
  step as ⟨last,leq⟩
  simp only [lift,bind_ok]
  have mv := min_val i last
  step as ⟨v,veq⟩
  have cast : (UScalar.cast .U32 v).val=v.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change v.val < 2^32;omega)
  simp [cast,veq,mv,leq,eq]

theorem fill_spec {N : Usize} (p : params.Params) (gen : LeavesCorrect p (N:=N)) (positive : 0 < machine.width.val)
    (sk seed : Array U8 N) (a : address.Adrs) (base : Usize) (out : Rows N) (fits : base.val+out.length≤512) :
    fill_xmss_leaves sk seed a base out ⦃ r => Row r out.length (fun j => Value p sk seed a 0 (base.val+j)) ⦄ := by
  unfold fill_xmss_leaves fill_xmss_leaves_loop
  dsimp only
  rw [leaves_loop_eq sk seed a base out.len]
  apply row_loop _ _ _ positive
  intro off active live av
  rw [Slice.len_val] at live av
  have aw : active.val ≤ machine.width.val := by omega
  unfold makeLeaves
  step with leafKeys (N:=N) base off active (by omega) (by omega) as ⟨keys,ks⟩
  step with gen sk seed a keys as ⟨batch,bs⟩
  rename_i j hj
  rw [bs j (by omega),ks j (by omega),min_eq_left (by omega),Nat.add_assoc]

omit leaves in
private theorem pairIds {N : Usize} (off active : Usize) (pos : 0 < active.val) (fits : off.val+active.val≤512) :
    core.array.from_fn machine.width (hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize N) (off,active)
      ⦃ ids => ∀ j < machine.width.val, ids.val[j]!.val=off.val+min j (active.val-1) ⦄ := by
  apply WP.spec_mono (core.array.from_fn.spec_stateless_getElem! machine.width _ (off,active)
    (fun j (x : Usize) => x.val = off.val+min j (active.val-1)) ?_)
  · intro ks spec j hj; simpa only [Array.getElem!_Nat_eq] using spec j hj
  intro i hi
  change hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut (N:=N) (off,active) i ⦃ _ ⦄
  unfold hash_pairs.closure.Insts.CoreOpsFunctionFnMutTupleUsizeUsize.call_mut
  step as ⟨last,l⟩
  simp only [lift,bind_ok]
  have mv := min_val i last
  step as ⟨v,veq⟩
  simp [veq,mv,l]

omit leaves in
private theorem pairAddresses {N : Usize} (ids : Array Usize machine.width) (a : address.Adrs) (h : U32)
    (base : Usize) (bound : ∀ j < machine.width.val, base.val+ids.val[j]!.val≤512) :
    core.array.Array.map (hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N) ids (a,h,base)
      ⦃ addrs => ∀ j < machine.width.val, adrsS addrs.val[j]! = { (adrsS a).setTypeAndClear Spec.TREE with
        word2 := h.val, word3 := base.val+ids.val[j]!.val } ⦄ := by
  apply map_spec (hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs N) ids (a,h,base)
    (fun j r => adrsS r = { (adrsS a).setTypeAndClear Spec.TREE with word2 := h.val, word3 := base.val+ids.val[j]!.val })
  intro j hj
  change hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut (N:=N) (a,h,base) ids.val[j]! ⦃ _ ⦄
  unfold hash_pairs.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeAdrs.call_mut
  dsimp only
  have small := bound j hj
  step with with_type_spec as ⟨a1,_,e1⟩
  step with with_word2_spec as ⟨a2,e2⟩
  step as ⟨v,ev⟩
  simp only [lift,bind_ok]
  step with with_word3_spec as ⟨a3,e3⟩
  have cast : (UScalar.cast .U32 v).val=v.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change v.val < 2^32;omega)
  simp [e3,e2,e1,adrsS,Spec.Adrs.setTypeAndClear,address.TREE,Spec.TREE,cast,ev]

omit leaves in
private theorem leftRows {N : Usize} (ids : Array Usize machine.width) (children : Rows N)
    (bound : ∀ j < machine.width.val, 2*ids.val[j]!.val+1<children.length) :
    core.array.Array.map (hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids children
      ⦃ left => ∀ j < machine.width.val, left.val[j]! =children.val[2*ids.val[j]!.val]! ⦄ := by
  apply map_spec (hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids children
    (fun j r => r = children.val[2*ids.val[j]!.val]!)
  intro j hj
  change hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut (N:=N) children ids.val[j]! ⦃ _ ⦄
  unfold hash_pairs.closure_2.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  have room := children.property
  change children.length ≤ Usize.max at room
  have ok := bound j hj
  step as ⟨i,ie⟩
  step as ⟨l,read⟩
  simp only [read,← getElem!_pos,ie]

omit leaves in
private theorem rightRows {N : Usize} (ids : Array Usize machine.width) (children : Rows N)
    (bound : ∀ j < machine.width.val, 2*ids.val[j]!.val+1<children.length) :
    core.array.Array.map (hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids children
      ⦃ right => ∀ j < machine.width.val, right.val[j]! = children.val[2*ids.val[j]!.val+1]! ⦄ := by
  apply map_spec (hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N N) ids children
    (fun j r => r = children.val[2*ids.val[j]!.val+1]!)
  intro j hj
  change hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut (N:=N) children ids.val[j]! ⦃ _ ⦄
  unfold hash_pairs.closure_3.Insts.CoreOpsFunctionFnMutTupleUsizeArrayU8N.call_mut
  have room := children.property
  change children.length ≤ Usize.max at room
  have ok := bound j hj
  step as ⟨i,ie⟩
  step as ⟨k,ke⟩
  step as ⟨r,read⟩
  simp only [read,← getElem!_pos,ke,ie]

omit leaves in
theorem parents_spec {N : Usize} (p : params.Params) (hp : PN p N) (positive : 0 < machine.width.val)
    (permutes : PermutationCorrect) (sk seed : Array U8 N) (a : address.Adrs) (h : U32) (base : Usize)
    (children out : Rows N) (pos : 0 < h.val) (fits : base.val+out.length≤512)
    (child : Row children (2*out.length) (fun j => Value p sk seed a (h.val-1) (2*base.val+j))) :
    hash_pairs seed a h base children out ⦃ r => Row r out.length (fun j => Value p sk seed a h.val (base.val+j)) ⦄ := by
  unfold hash_pairs hash_pairs_loop
  dsimp only
  rw [parents_loop_eq seed a h base children out.len]
  apply row_loop _ _ _ positive
  intro off active live av
  rw [Slice.len_val] at live av
  unfold makeParents
  step with pairIds (N:=N) off active (by omega) (by omega) as ⟨ids,idv⟩
  have within (j : Nat) (hj : j<machine.width.val) : ids.val[j]!.val<out.length := by rw [idv j hj];omega
  have pairBound (j : Nat) (hj : j<machine.width.val) : 2*ids.val[j]!.val+1<children.length := by
    rw [child.1]; have := within j hj; omega
  step with pairAddresses (N:=N) ids a h base (by intro j hj; have := within j hj;omega) as ⟨addresses,addr⟩
  step with leftRows ids children pairBound as ⟨left,ls⟩
  step with rightRows ids children pairBound as ⟨right,rs⟩
  have align : N.val%8=0 := by rcases hp.nok with e|e|e <;> omega
  step with pair_fips seed addresses left right permutes hp.le32 align as ⟨batch,bs⟩
  rename_i j hj
  have jw : j<machine.width.val := by omega
  have idEq := idv j jw
  rw [min_eq_left (by omega)] at idEq
  have haveRoom := within j jw
  rw [bs j jw,addr j jw,ls j jw,rs j jw,child.2 _ (by omega),child.2 _ (by omega),idEq]
  have pred : h.val-1+1 = h.val := by omega
  unfold Value
  conv_rhs => rw [← pred,Spec.xmssNode]
  simp [Spec.H,Shake.params,paramsS_n,hp.n_eq,pred,Nat.mul_add,Nat.add_assoc]

theorem ops [stream : Stream] [StreamCorrect] {N : Usize} (p : params.Params) (hp : PN p N)
    (positive : 0 < machine.width.val) (width : machine.width.val ≤ 8) (permutes : PermutationCorrect)
    (gen : LeavesCorrect p (N:=N)) (available : Usize → Result Bool) :
    Subtree.Ops (backend available) single (N:=N) p where
  leaf := CacheopsRust.WotsCallbacks.single_eq p hp positive width permutes
  leaves := fill_spec p gen positive
  parents sk pk a h base child out hpos _ bound nodes :=
    parents_spec p hp positive permutes sk pk a h base child out hpos
      (Nat.le_trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos h.val)) bound) nodes

end slhdsa.cache.builder.nativeShake.Vector
