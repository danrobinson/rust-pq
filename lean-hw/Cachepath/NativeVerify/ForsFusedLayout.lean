import Cachepath.NativeVerify.ForsFusedRows
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.ForsFused
open ShakeBatch NativeVerify.Wots NativeShakeWots
set_option linter.concreteInstances false
set_option maxHeartbeats 1000000
variable [machine : Machine]
/-- Writes the seeded PRF block to a fresh zero matrix. The Rust caller retains
    the high padding bit for the second block. -/
def first {α} (K : Matrix machine.width → U64 → Result α) (n offset pad : Usize)
    (sw skw aw_prf : Array U64 4#usize) (w31 : Array U64 machine.width) : Result α := do
  let a4 := Array.repeat machine.width 0#u64
  let state := Array.repeat 25#usize a4
  let state1 ←
    fused_loop1 { start := 0#usize, «end» := n }
      offset sw skw state
  let i ← Array.index_usize aw_prf 0#usize
  let a5 := Array.repeat machine.width i
  let state2 ← Array.update state1 n a5
  let i1 ← Array.index_usize aw_prf 1#usize
  let i2 ← n + 1#usize
  let a6 := Array.repeat machine.width i1
  let state3 ← Array.update state2 i2 a6
  let i3 ← Array.index_usize aw_prf 2#usize
  let i4 ← n + 2#usize
  let a7 := Array.repeat machine.width i3
  let state4 ← Array.update state3 i4 a7
  let i5 ← n + 3#usize
  let state5 ← Array.update state4 i5 w31
  let a8 := Array.repeat machine.width 31#u64
  let state6 ← Array.update state5 pad a8
  let i6 ← 1#u64 <<< 63#i32
  let a9 := Array.repeat machine.width i6
  let state7 ← Array.update state6 16#usize a9
  K state7 i6

/-- Reuses the permuted rows as the leaf payload and zeros the overwritten suffix. -/
def second {α} (K : Matrix machine.width → Result α) (n offset pad : Usize)
    (sw aw_tree : Array U64 4#usize) (w31 : Array U64 machine.width) (state8 : Matrix machine.width)
    (i6 : U64) : Result α := do
  let state9 ←
    fused_loop2 { start := 0#usize, «end» := n }
      offset sw state8
  let i7 ← Array.index_usize aw_tree 0#usize
  let a10 := Array.repeat machine.width i7
  let state10 ← Array.update state9 n a10
  let i8 ← Array.index_usize aw_tree 1#usize
  let i9 ← n + 1#usize
  let a11 := Array.repeat machine.width i8
  let state11 ← Array.update state10 i9 a11
  let i10 ← Array.index_usize aw_tree 2#usize
  let i11 ← n + 2#usize
  let a12 := Array.repeat machine.width i10
  let state12 ← Array.update state11 i11 a12
  let i12 ← n + 3#usize
  let state13 ← Array.update state12 i12 w31
  let a13 := Array.repeat machine.width 31#u64
  let state14 ← Array.update state13 pad a13
  let i13 ← pad + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state14 { start := i13, «end» := 25#usize }
  let (iter, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ←
    fused_loop3 iter (fun im1 => im1)
  let im1 := back im
  let s1 := into_iter_back im1
  let state15 := index_mut_back s1
  let a14 := Array.repeat machine.width i6
  let state16 ← Array.update state15 16#usize a14
  K state16

abbrev addrLane (aw : Array U64 4#usize) := Array.repeat machine.width aw.val[2]!

theorem first_spec {α} (Q : α → Prop) (K : Matrix machine.width → U64 → Result α) (n offset pad : Usize)
    (sw skw aw : Array U64 4#usize) (w : Array U64 machine.width)
    (small : n.val≤4) (off : offset.val=n.val+4) (padding : pad.val=offset.val+n.val)
    (continuation : ∀ st hi, hi.bv=(1#64 <<< 63) →
      (∀ k < 25, ∀ l < machine.width.val, cell st k l =
        packedWord n.val sw aw.val[0]! aw.val[1]! (addrLane aw) w (fun j _ => skw.val[j]!.bv) k l) →
      K st hi ⦃ Q ⦄) : first K n offset pad sw skw aw w ⦃ Q ⦄ := by
  unfold first
  let z := Array.repeat 25#usize (Array.repeat machine.width 0#u64)
  have eq : fused_loop1 ⟨0#usize,n⟩ offset sw skw z = fill_prf_loop0 ⟨0#usize,n⟩ z sw skw offset := rfl
  dsimp only
  rw [eq]
  step with fill_prefix n offset z sw skw small off as ⟨s1,pre⟩
  step as ⟨w0,a0⟩
  step as ⟨s2,u0⟩
  step as ⟨w1,a1⟩
  step as ⟨r1,v1⟩
  step as ⟨s3,u1⟩
  step as ⟨w2,a2⟩
  step as ⟨r2,v2⟩
  step as ⟨s4,u2⟩
  step as ⟨r3,v3⟩
  step as ⟨s5,u3⟩
  step as ⟨s6,marker⟩
  step as ⟨hi,_,high⟩
  step as ⟨s7,finish⟩
  apply continuation s7 hi high
  intro k hk l hl
  rw [finish,broadcast _ _ _ _ _ (by decide) hl,marker,broadcast _ _ _ _ _ (by omega) hl,
      u3,setRow _ _ _ _ _ (by omega),u2,broadcast _ _ _ _ _ (by omega) hl,
      u1,broadcast _ _ _ _ _ (by omega) hl,u0,broadcast _ _ _ _ _ (by omega) hl,pre k l hl]
  have zero : cell z k l=0 := by
    simp only [z,cell,Array.repeat_val,List.getElem!_replicate _ (show k < (25#usize).val from hk),List.getElem!_replicate _ hl]
    rfl
  simp only [packedWord,headerWord,addrLane,Array.repeat_val,List.getElem!_replicate _ hl,
    show (16#usize).val=16 by rfl,v1,v2,v3,padding,off,high,a0,a1,a2,← getElem!_pos]
  split_ifs <;> first | rfl | omega

theorem second_spec {α} (Q : α → Prop) (K : Matrix machine.width → Result α) (n offset pad : Usize)
    (sw aw : Array U64 4#usize) (w : Array U64 machine.width) (st : Matrix machine.width) (hi : U64)
    (small : n.val≤4) (off : offset.val=n.val+4) (padding : pad.val=offset.val+n.val)
    (high : hi.bv=1#64 <<< 63)
    (continuation : ∀ out, (∀ k < 25, ∀ l < machine.width.val, cell out k l =
        packedWord n.val sw aw.val[0]! aw.val[1]! (addrLane aw) w (cell st) k l) →
      K out ⦃ Q ⦄) : second K n offset pad sw aw w st hi ⦃ Q ⦄ := by
  unfold second
  have eq : fused_loop2 ⟨0#usize,n⟩ offset sw st = refill_short_inplace_loop0 ⟨0#usize,n⟩ st sw offset := rfl
  rw [eq]
  step with refill_prefix n offset st sw small off as ⟨mid,pre⟩
  step as ⟨w0,a0⟩
  step as ⟨s1,u0⟩
  step as ⟨w1,a1⟩
  step as ⟨j1,v1⟩
  step as ⟨s2,u1⟩
  step as ⟨w2,a2⟩
  step as ⟨j2,v2⟩
  step as ⟨s3,u2⟩
  step as ⟨j3,v3⟩
  step as ⟨s4,u3⟩
  step as ⟨s5,marker⟩
  step as ⟨first,fv⟩
  step as ⟨part,back,partVal,partLen,write⟩
  simp only [core.slice.Slice.iter_mut,bind_ok]
  have zeros : fused_loop3 ⟨part,0⟩ id ⦃ it restore => (restore it).slice.length=part.length ∧
      ∀ j < part.length, (restore it).slice.val[j]! = Array.repeat machine.width 0#u64 ⦄ :=
    NativeVerify.Fors.zero_leaf_tail part
  obtain ⟨⟨it,restore⟩,hz,length,zero⟩ := spec_imp_exists zeros
  change fused_loop3 ⟨part,0⟩ (fun x=>x) = ok (it,restore) at hz
  change (do let (im,b) ← fused_loop3 ⟨part,0⟩ (fun x=>x)
             let out ← Array.update (back (b im).slice) 16#usize (Array.repeat machine.width hi)
             K out) ⦃ Q ⦄
  rw [hz]
  simp only [bind_ok]
  try dsimp only
  step as ⟨out,finish⟩
  apply continuation out
  intro k hk l hl
  rw [finish,broadcast _ _ _ _ _ (by decide) hl]
  by_cases endWord : k=16
  · simp only [show (16#usize).val=16 by rfl,endWord,ite_true,packedWord,headerWord]
    exact high
  · simp only [show (16#usize).val=16 by rfl,endWord,ite_false]
    have tail : cell (back (restore it).slice) k l = if pad.val<k then 0 else cell s5 k l := by
      unfold cell
      rw [write]
      by_cases beyond : pad.val<k
      · rw [ite_eq_left beyond,List.getElem!_setSlice!_middle _ _ _ _ (by simp; change _ ∧ _ < (restore it).slice.length ∧ _ < 25; omega),
          zero _ (by omega),Array.repeat_val]
        simp [hl]
      · rw [ite_eq_right beyond,List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
    rw [tail,marker,broadcast _ _ _ _ _ (by omega) hl,u3,setRow _ _ _ _ _ (by omega),u2,broadcast _ _ _ _ _ (by omega) hl,
        u1,broadcast _ _ _ _ _ (by omega) hl,u0,broadcast _ _ _ _ _ (by omega) hl,pre k l hl]
    simp only [packedWord,headerWord,endWord,ite_false,v1,v2,v3,padding,off,a0,a1,a2,← getElem!_pos,
      addrLane,Array.repeat_val,List.getElem!_replicate _ hl]
    split_ifs <;> first | rfl | omega

end slhdsa.NativeVerify.ForsFused
