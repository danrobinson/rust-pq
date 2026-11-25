import Cachepath.NativeVerify.WotsPack
import Cachepath.NativeVerify.ForsPadding
import Shakebatch.Short
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine] [accel : Dispatch machine]

def round {α : Type} (n offset : Usize) (sw aw_hash : Array U64 4#usize) (pad active : Usize)
    (lane_id : Array Usize machine.width) (lane_step : Array U32 machine.width)
    (lane_val : LaneValues machine.width) (state : Matrix machine.width) (after : Matrix machine.width → Result α) : Result α := do
  let state1 ←
    recover_loop2_loop0 { start := 0#usize, «end» := n } offset
      sw active lane_val state
  let i ← Array.index_usize aw_hash 0#usize
  let a := Array.repeat machine.width i
  let state2 ← Array.update state1 n a
  let i1 ← Array.index_usize aw_hash 1#usize
  let i2 ← n + 1#usize
  let a1 := Array.repeat machine.width i1
  let state3 ← Array.update state2 i2 a1
  let i3 ← Array.index_usize aw_hash 2#usize
  let i4 ← n + 2#usize
  let a2 := Array.repeat machine.width i3
  let a3 ← Array.update state3 i4 a2
  let state4 ←
    recover_loop2_loop1 { start := 0#usize, «end» := active } n
      lane_id lane_step a3
  let a4 := Array.repeat machine.width 31#u64
  let state5 ← Array.update state4 pad a4
  let i5 ← pad + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state5 { start := i5, «end» := 25#usize }
  let (iter, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ← recover_loop2_loop2 iter (fun im1 => im1)
  let i6 ← 1#u64 <<< 63#i32
  let im1 := back im
  let s1 := into_iter_back im1
  let state6 := index_mut_back s1
  let a5 := Array.repeat machine.width i6
  let state7 ← Array.update state6 16#usize a5
  let state8 ← Dispatch.permute state7 active
  after state8

theorem body_round {N : Usize} (sig : Slice U8) (digits : Slice U32) (n offset : Usize)
    (sw aw : Array U64 4#usize) (order : Array Usize 67#usize) (total pad : Usize)
    (tips : Array (Array U8 N) 67#usize) (next active : Usize)
    (ids : Array Usize machine.width) (steps : Array U32 machine.width) (values : LaneValues machine.width)
    (s : Matrix machine.width) : recover_loop2.body sig digits n offset sw aw order total pad tips next active ids steps values s =
      (do if active>0#usize then
            round n offset sw aw pad active ids steps values s fun st => do
              let (tips',next',active',ids',steps',values',st') ← recover_loop2_loop3 sig digits n tips order total next active ids steps values st 0#usize
              ok (cont (tips',next',active',ids',steps',values',st'))
          else ok (done tips)) := by rfl

def RoundLayout (n offset pad active : Usize) (sw aw : Array U64 4#usize)
    (ids : Array Usize machine.width) (steps : Array U32 machine.width)
    (values : LaneValues machine.width) (out : Matrix machine.width) : Prop :=
  ∃ before : Matrix machine.width,
      (∀ l < active.val, ShakeBatch.lane out l=Spec.Keccak.permute (ShakeBatch.lane before l)) ∧
      ∀ k < 25, ∀ l < active.val, cell before k l =
        if k=16 then 0x8000000000000000 else if pad.val<k then 0 else if k=pad.val then 31
        else if k=n.val+3 then addressLow (UScalar.cast .U32 ids.val[l]!) ||| wordTag steps.val[l]!
        else if k< n.val then sw.val[k]!.bv else if k<offset.val then aw.val[k-n.val]!.bv
        else laneWord values l (k-offset.val)

theorem round_layout {α : Type} (n offset pad active : Usize) (sw aw : Array U64 4#usize)
    (ids : Array Usize machine.width) (steps : Array U32 machine.width) (values : LaneValues machine.width)
    (s : Matrix machine.width) (cap : n.val≤4) (off : offset.val=n.val+4) (padding : pad.val=offset.val+n.val)
    (valid : active.val≤machine.width.val) (permutes : ActiveCorrect machine accel.permute)
    (after : Matrix machine.width → Result α) (post : α → Prop)
    (k : ∀ out, RoundLayout n offset pad active sw aw ids steps values out → after out ⦃ v => post v ⦄) :
    round n offset sw aw pad active ids steps values s after ⦃ v => post v ⦄ := by
  unfold round
  step with pack_seed_payload s offset n active values sw valid cap (by omega) (by omega) as ⟨s1,packed⟩
  step as ⟨w0,r0⟩
  step as ⟨s2,u0⟩
  step as ⟨w1,r1⟩
  step as ⟨n1,v1⟩
  step as ⟨s3,u1⟩
  step as ⟨w2,r2⟩
  step as ⟨n2,v2⟩
  step as ⟨s4,u2⟩
  step with pack_tags s4 n active ids steps valid (by omega) as ⟨s5,tags⟩
  step as ⟨s6,marker⟩
  step as ⟨first,fv⟩
  step as ⟨part,back,partVal,partLen,write⟩
  simp only [core.slice.Slice.iter_mut,bind_ok]
  have zeros : recover_loop2_loop2 ⟨part,0⟩ id ⦃ it restore => (restore it).slice.length=part.length ∧
      ∀ j < part.length, (restore it).slice.val[j]! = Array.repeat machine.width 0#u64 ⦄ := Fors.zero_leaf_tail part
  obtain ⟨⟨it,restore⟩,hz,length,zero⟩ := spec_imp_exists zeros
  change recover_loop2_loop2 ⟨part,0⟩ (fun x=>x) = ok (it,restore) at hz
  change (do
    let (im,b) ← recover_loop2_loop2 ⟨part,0⟩ (fun x=>x)
    let hi ← 1#u64 <<< 63#i32
    let bef ← Array.update (back (b im).slice) 16#usize (Array.repeat machine.width hi)
    let out ← accel.permute bef active
    after out) ⦃ _ => _ ⦄
  rw [hz]
  simp only [bind_ok]
  try dsimp only
  step as ⟨last,_,high⟩
  step as ⟨before,finish⟩
  step with permutes before active valid as ⟨out,hash⟩
  apply k out
  refine ⟨before,hash,?_⟩
  intro k hk l hl
  have within := hl.trans_le valid
  rw [finish,broadcast _ _ _ _ _ (by decide) within]
  by_cases endWord : k=16
  · simp only [show (16#usize).val=16 by rfl,endWord,ite_true]
    exact high
  · simp only [show (16#usize).val=16 by rfl,endWord,ite_false]
    have cell6 : cell (back (restore it).slice) k l = if pad.val<k then 0 else cell s6 k l := by
      unfold cell
      rw [write]
      by_cases tail : pad.val<k
      · rw [ite_eq_left tail,List.getElem!_setSlice!_middle _ _ _ _ (by simp; change _ ∧ _ < (restore it).slice.length ∧ _ < 25;omega),
          zero _ (by omega),Array.repeat_val]
        simp [within]
      · rw [ite_eq_right tail,List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
    rw [cell6,marker,broadcast _ _ _ _ _ (by omega) within,tags,u2,broadcast _ _ _ _ _ (by omega) within,
      u1,broadcast _ _ _ _ _ (by omega) within,u0,broadcast _ _ _ _ _ (by omega) within,packed k l within]
    rw [r0,r1,r2,← getElem!_pos,← getElem!_pos,← getElem!_pos]
    simp only [v1,v2,hl,true_and,and_true]
    split_ifs <;> first | rfl | omega | (congr 3 <;> omega) | (congr 1 <;> omega) | (subst_vars; rfl) | rw [show k-n.val=2 by omega] | rw [show k-n.val=1 by omega] | rw [show k-n.val=0 by omega]

end slhdsa.NativeVerify.Wots
