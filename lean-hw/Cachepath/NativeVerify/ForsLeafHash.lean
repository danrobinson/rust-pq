import Cachepath.NativeVerify.ForsLeaf
import Cachepath.NativeVerify.ForsPadding
import Cachepath.WotsFusedChain

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1500000
variable [machine : Machine] [accelerator : ActiveKernel machine]

def hashLeaves (N : Usize) (sig : Slice U8) (n offset pad_short stride : Usize)
    (sw aw : Array U64 4#usize) (first active : Usize) (indices : Array U32 machine.width)
    (state : Matrix machine.width) : Result (Matrix machine.width) := do
  let state1 ←
    recover_loop0_loop1 { start := 0#usize, «end» := n }
      sw state
  let i3 ← Array.index_usize aw 0#usize
  let a := Array.repeat machine.width i3
  let state2 ← Array.update state1 n a
  let i4 ← Array.index_usize aw 1#usize
  let i5 ← n + 1#usize
  let a1 := Array.repeat machine.width i4
  let state3 ← Array.update state2 i5 a1
  let i6 ← Array.index_usize aw 2#usize
  let i7 ← n + 2#usize
  let a2 := Array.repeat machine.width i6
  let a3 ← Array.update state3 i7 a2
  let state4 ←
    recover_loop0_loop2 N
      { start := 0#usize, «end» := active } sig n offset stride a3 first
      indices
  let a4 := Array.repeat machine.width 31#u64
  let state5 ← Array.update state4 pad_short a4
  let i8 ← pad_short + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state5 { start := i8, «end» := 25#usize }
  let (iter2, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ←
    recover_loop0_loop3 iter2 (fun im1 => im1)
  let i9 ← 1#u64 <<< 63#i32
  let im1 := back im
  let s1 := into_iter_back im1
  let state6 := index_mut_back s1
  let a5 := Array.repeat machine.width i9
  let state7 ← Array.update state6 16#usize a5
  let state8 ← accelerator.run state7 active
  ok state8

theorem leaf_layout (N : Usize) (sig : Slice U8) (n offset pad stride : Usize)
    (sw aw : Array U64 4#usize) (first active : Usize) (indices : Array U32 machine.width)
    (s : Matrix machine.width) (cap : n.val≤4) (off : offset.val=n.val+4) (padding : pad.val=offset.val+n.val)
    (size : n.val*8=N.val) (valid : active.val≤machine.width.val) (stridePos : 0<stride.val)
    (fits : (first.val+active.val)*stride.val*N.val≤sig.length) (npos : 0<N.val)
    (permutes : ActiveCorrect machine accelerator.run) :
    hashLeaves N sig n offset pad stride sw aw first active indices s ⦃ out => ∃ before : Matrix machine.width,
      (∀ l < active.val, ShakeBatch.lane out l=Spec.Keccak.permute (ShakeBatch.lane before l)) ∧
      ∀ k < 25, ∀ l < active.val, cell before k l =
        if k=16 then 0x8000000000000000 else if pad.val<k then 0 else if k=pad.val then 31
        else if k=n.val+3 then wordTag indices.val[l]!
        else if k<n.val then sw.val[k]!.bv else if k<offset.val then aw.val[k-n.val]!.bv
        else blockWords sig N.val ((first.val+l)*stride.val) (k-offset.val) ⦄ := by
  unfold hashLeaves
  step with seed_rows s n sw cap as ⟨s1,packed⟩
  step as ⟨w0,r0⟩
  step as ⟨s2,u0⟩
  step as ⟨w1,r1⟩
  step as ⟨n1,v1⟩
  step as ⟨s3,u1⟩
  step as ⟨w2,r2⟩
  step as ⟨n2,v2⟩
  step as ⟨s4,u2⟩
  step with leaf_lanes N sig n offset stride first active s4 indices size off cap valid stridePos fits npos as ⟨s5,tags⟩
  step as ⟨s6,marker⟩
  step as ⟨first,fv⟩
  step as ⟨part,back,partVal,partLen,write⟩
  simp only [core.slice.Slice.iter_mut,bind_ok]
  have zeros : recover_loop0_loop3 ⟨part,0⟩ id ⦃ it restore => (restore it).slice.length=part.length ∧
      ∀ j < part.length, (restore it).slice.val[j]! = Array.repeat machine.width 0#u64 ⦄ := Fors.zero_leaf_tail part
  obtain ⟨⟨it,restore⟩,hz,length,zero⟩ := spec_imp_exists zeros
  change recover_loop0_loop3 ⟨part,0⟩ (fun x=>x) = ok (it,restore) at hz
  change (do
    let (im,b) ← recover_loop0_loop3 ⟨part,0⟩ (fun x=>x)
    let hi ← 1#u64 <<< 63#i32
    let bef ← Array.update (back (b im).slice) 16#usize (Array.repeat machine.width hi)
    let out ← accelerator.run bef active
    ok out) ⦃ _ => _ ⦄
  rw [hz]
  simp only [bind_ok]
  step as ⟨last,_,high⟩
  step as ⟨before,finish⟩
  step with permutes before active valid as ⟨out,hash⟩
  refine ⟨before,hash,?_⟩
  intro k hk l hl
  have within := hl.trans_le valid
  rw [finish,write_tag _ _ _ (by decide) k l within]
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
    rw [cell6,marker,write_tag _ _ _ (by omega) k l within,tags k hk l within,ite_eq_left hl,u2,write_tag _ _ _ (by omega) k l within,
      u1,write_tag _ _ _ (by omega) k l within,u0,write_tag _ _ _ (by omega) k l within,packed k hk l within]
    rw [r0,r1,r2,← getElem!_pos,← getElem!_pos,← getElem!_pos]
    simp only [v1,v2]
    split_ifs <;> first | rfl | omega | (congr 3 <;> omega) | (congr 1 <;> omega) | (subst_vars; simp)


theorem leaf_fips {N : Usize} (seed : Array U8 N) (a : address.Adrs) (sig : Slice U8)
    (n offset pad stride : Usize) (sw aw : Array U64 4#usize) (first active : Usize)
    (indices : Array U32 machine.width) (s : Matrix machine.width)
    (cap : n.val≤4) (off : offset.val=n.val+4) (padding : pad.val=offset.val+n.val)
    (size : n.val*8=N.val) (valid : active.val≤machine.width.val) (stridePos : 0<stride.val)
    (fits : (first.val+active.val)*stride.val*N.val≤sig.length) (npos : 0<N.val)
    (seeds : ∀ k < n.val, sw.val[k]!.bv=inputWord seed.val k)
    (address : ∀ k < 4, aw.val[k]!.bv=addressWord a k)
    (permutes : ActiveCorrect machine accelerator.run) :
    hashLeaves N sig n offset pad stride sw aw first active indices s ⦃ out => ∀ l < active.val,
      Spec.Keccak.squeeze (ShakeBatch.lane out l) 0 N.val = Spec.shake256
        (bytes seed.val ++ ((adrsS {a with word2:=0#u32,word3:=indices.val[l]!}).bytes ++
          bytes ((sig.val.drop (((first.val+l)*stride.val)*N.val)).take N.val))) N.val ⦄ := by
  apply WP.spec_mono (leaf_layout N sig n offset pad stride sw aw first active indices s cap off padding
    size valid stridePos fits npos permutes)
  rintro out ⟨before,hash,layout⟩ l hl
  let start := ((first.val+l)*stride.val)*N.val
  have slotFit : start+N.val≤sig.length := by
    have h := Nat.mul_le_mul_right stride.val (show first.val+l+1≤first.val+active.val by omega)
    rw [Nat.add_mul,one_mul] at h
    have next := Nat.mul_le_mul_right N.val (show (first.val+l)*stride.val+1≤(first.val+active.val)*stride.val by omega)
    rw [Nat.add_mul,one_mul] at next
    exact next.trans fits
  let payload : Array U8 N := Array.from ((sig.val.drop start).take N.val) (by simp [Slice.length] at slotFit; simp;omega)
  have pay : payload.val=(sig.val.drop start).take N.val := Array.from_val _ _
  change _ = Spec.shake256 (bytes seed.val ++ (_ ++ bytes ((sig.val.drop start).take N.val))) _
  rw [← pay]
  apply hashed_short seed payload a 0#u32 _ before out l (by omega) (by omega) (hash l hl)
  intro k hk
  rw [layout k hk l hl]
  unfold baseWord initialWord
  have low : addressLow 0#u32=0 := rfl
  have slot : blockWords sig N.val ((first.val+l)*stride.val) (k-offset.val) = inputWord payload.val (k-offset.val) := by rw [pay];rfl
  have zeroOr (v : BitVec 64) : (0 : BitVec 64) ||| v = v := by bv_decide
  rw [slot,low,zeroOr,show (2*N.val+32)/8=pad.val by omega,show N.val/8=n.val by omega,← off]
  by_cases region : offset.val≤k ∧ k<offset.val+n.val
  · rw [ite_eq_left region]
    simp only [ite_eq_right (by omega : k≠16),ite_eq_right (by omega : ¬pad.val<k),
      ite_eq_right (by omega : k≠pad.val),ite_eq_right (by omega : k≠n.val+3),
      ite_eq_right (by omega : ¬k<n.val),ite_eq_right (by omega : ¬k<offset.val)]
  · rw [ite_eq_right region]
    by_cases tag : k=n.val+3
    · have last : k=offset.val-1 := by omega
      simp only [ite_eq_left last,ite_eq_right (by omega : k≠16),ite_eq_right (by omega : ¬pad.val<k),
        ite_eq_right (by omega : k≠pad.val),ite_eq_left tag]
    · rw [ite_eq_right (by omega : k≠offset.val-1)]
      split_ifs <;> first | rfl | omega | exact seeds _ (by omega) | exact address _ (by omega) | decide

theorem split_batch [stream : Stream] (N : Usize) (height : U32) (selections : Slice U32)
    (sig : Slice U8) (n offset short pair stride : Usize) (sw aw : Array U64 4#usize)
    (it : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize))
    (pk : stream.State) (state : Matrix machine.width) :
    recover_loop0.body N height selections sig n offset short pair stride sw aw it pk state = (do
      let (o,next) ← core.iter.adapters.step_by.IteratorStepBy.next
        (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) it
      match o with
      | none => ok (done pk)
      | some first =>
        let rest ← selections.len-first
        let active ← lift (core.cmp.impls.OrdUsize.min rest machine.width)
        let ix ← recover_loop0_loop0 ⟨0#usize,active⟩ height selections first (Array.repeat machine.width 0#u32)
        let leaves ← hashLeaves N sig n offset short stride sw aw first active ix state
        let roots ← recover_loop0_loop4 N 0x8000000000000000#u64 ⟨0#u32,height⟩ sig n offset pair stride sw aw leaves first active ix
        let pk' ← recover_loop0_loop5 N ⟨0#usize,active⟩ n pk roots
        ok (cont (next,pk',roots))) := by
  unfold recover_loop0.body hashLeaves
  congr 1
  funext ⟨o,next⟩
  have high : (1#u64 <<< 63#i32 : Result U64)=ok 0x8000000000000000#u64 := rfl
  cases o <;> simp [high,Std.bind_assoc]
  simp only [uncurry,bind_tc_eq,Std.bind_assoc,bind_ok,high]
  repeat' congr 1

end slhdsa.NativeVerify.Fors
