import Cachepath.NativeVerify.ForsPadding
import Cachepath.WotsFusedLayout

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

def pairPad (state4 : Matrix machine.width) (pad_pair : Usize) (i : U64) : Result (Matrix machine.width) := do
  let i8 ← pad_pair + 1#usize
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice (Array Std.U64 machine.width)))
      state4 { start := i8, «end» := 25#usize }
  let (iter2, into_iter_back) ←
    core.slice.Slice.iter_mut s
  let (im, back) ←
    recover_loop0_loop4_loop2 iter2 (fun im1 => im1)
  let im1 := back im
  let s1 := into_iter_back im1
  let state5 := index_mut_back s1
  let a5 := Array.repeat machine.width 31#u64
  let state6 ← Array.update state5 pad_pair a5
  let (a6, index_mut_back1) ← Array.index_mut_usize state6 16#usize
  let (iter3, into_iter_back1) ←
    MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
      a6
  let (im2, back1) ←
    recover_loop0_loop4_loop3 i iter3 (fun im3 => im3)
  let im3 := back1 im2
  let a7 := into_iter_back1 im3
  let state7 := index_mut_back1 a7
  ok state7

theorem pair_pad (state : Matrix machine.width) (pad : Usize) (marker : U64) (ends : pad.val≤16) :
    pairPad state pad marker ⦃ out => ∀ k<25, ∀ l<machine.width.val, cell out k l =
      let v := if k=pad.val then (31 : BitVec 64) else if pad.val<k then 0 else cell state k l
      if k=16 then v ||| marker.bv else v ⦄ := by
  unfold pairPad
  step as ⟨start,startv⟩
  step as ⟨slice,restore,sv,slen,write⟩
  simp only [core.slice.Slice.iter_mut,bind_ok]
  have clear := zero_pair_tail slice
  apply WP.spec_bind clear
  rintro ⟨it,back⟩ ⟨length,zeros⟩
  simp only [uncurry]
  step as ⟨st,put⟩
  step as ⟨row,putRow,read,rb⟩
  simp only [MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,Array.to_slice_mut,
    core.slice.Slice.iter_mut,bind_ok]
  apply WP.spec_bind (pad_pair_word marker row.to_slice)
  rintro ⟨im,rev⟩ ⟨len2,marks⟩
  simp only [uncurry,bind_ok,WP.spec_ok]
  intro k hk l hl
  have stCell : cell st k l = if k=pad.val then 31 else if pad.val<k then 0 else cell state k l := by
    rw [put,write_tag _ _ _ (by omega) k l hl]
    by_cases same : k=pad.val
    · simp [same]
    · rw [ite_eq_right same,ite_eq_right same]
      unfold cell
      rw [write]
      by_cases tail : pad.val<k
      · rw [ite_eq_left tail,List.getElem!_setSlice!_middle _ _ _ _ (by simp; change _ ∧ _ < (back it).slice.length ∧ _ < 25;omega),
          zeros _ (by omega),Array.repeat_val]
        simp [hl]
      · rw [ite_eq_right tail,List.getElem!_setSlice!_prefix _ _ _ _ (by omega)]
  rw [← stCell,rb]
  by_cases middle : k=16
  · subst k
    simp only [ite_true]
    rw [cell,Array.set_val_eq,show (16#usize).val=16 by rfl,setSame st.val 16 _ (by simp)]
    rw [Array.from_slice_val _ _ (by simpa using len2),marks _ (by simpa),read,← getElem!_pos]
    simp only [Array.val_to_slice,cell];rfl
  · rw [ite_eq_right middle,cell,Array.set_val_eq,show (16#usize).val=16 by rfl,setOther st.val 16 k _ (Ne.symm middle)]
    rfl

end slhdsa.NativeVerify.Fors
