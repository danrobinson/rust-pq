import Kbulk.Word
import Slhdsa.Proofs.Basic
open Aeneas Aeneas.Std Result ControlFlow
open Spec.Keccak
namespace slhdsa.Oriented.Bulk
open KbulkRust.shake256
set_option maxHeartbeats 3000000

private def remaining (block : Slice U8) (a : Array U64 25#usize) (i : Nat) :=
  let state := if i = 17 then (permute (decode a),0) else (decode a,8*i)
  ((bytes block.val).drop (8*i)).foldl feed state

theorem blockWords (block : Slice U8) (a : Array U64 25#usize) (size : block.length=136) :
    oriented.blocks_loop0_loop0 ⟨0#usize,17#usize⟩ a block ⦃ out =>
      (permute (decode out),0) = (bytes block.val).foldl feed (decode a,0) ⦄ := by
  unfold oriented.blocks_loop0_loop0
  apply loop.spec_decr_nat
    (measure := fun (p : core.ops.range.Range Usize × Array U64 25#usize) => 17 - p.1.start.val)
    (inv := fun p => p.1.end=17#usize ∧ p.1.start.val≤17 ∧
      remaining block p.2 p.1.start.val = (bytes block.val).foldl feed (decode a,0))
  · rintro ⟨it,state⟩ ⟨he,hb,prior⟩
    simp only at he hb prior ⊢
    unfold oriented.blocks_loop0_loop0.body
    by_cases more : it.start.val<17
    · obtain ⟨⟨o,next⟩,get,ho,hn,he'⟩ := spec_imp_exists
        (core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact more))
      subst o
      rw [get]
      simp only [bind_ok]
      step as ⟨l,lo⟩
      step as ⟨e,hi⟩
      step as ⟨s,slice,len⟩
      have eight : s.length=8 := by scalar_tac
      simp only [core.array.TryFromArrayCopySlice.try_from,show s.length=(8#usize).val by exact eight,
        _root_.dite_true,core.result.Result.unwrap,bind_ok,lift]
      step as ⟨off,offEq⟩
      step as ⟨old,oldEq⟩
      step as ⟨out,write⟩
      refine ⟨he'.trans he,by omega,?_,by omega⟩
      let input := Array.from s.val (show s.val.length=(8#usize).val by exact eight)
      have lane : it.start.val < 25 := by omega
      have update := updateWord state it.start (core.num.U64.from_le_bytes input) lane
      simp only [getElem!_pos state.val it.start.val (by simpa using lane),
        getElem!_pos oriented.OFF.val it.start.val (by simpa using lane), ← oldEq, ← offEq] at update
      have data : (bytes block.val).drop (8*it.start.val) = bytes s.val ++ (bytes block.val).drop (8*(it.start.val+1)) := by
        rw [slice,List.slice,bytes_take,bytes_drop,hi,Nat.add_sub_cancel_left,lo,
          show 8*(it.start.val+1)=8*it.start.val+8 by omega, ← List.drop_drop]
        exact (List.take_append_drop _ _).symm
      have fed := feedWord (decode state) it.start.val (bytes s.val) (by simpa using eight)
        (by simpa [decode] using lane) more
      dsimp only at fed update
      rw [PlatformShake.loaded] at update
      simp only [input,Array.from_val] at update
      rw [write]
      unfold remaining at prior ⊢
      rw [if_neg (by omega),data,List.foldl_append,fed,← update] at prior
      rw [hn]
      by_cases last : it.start.val = 16
      · simpa [last] using prior
      · simpa [last,show it.start.val+1≠17 by omega,Nat.mul_succ] using prior
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.not_lt.mp more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      simpa [remaining,show it.start.val=17 by omega,List.drop_eq_nil_of_le (by simpa using size.le :
        (bytes block.val).length ≤ 136)] using prior
  · exact ⟨rfl,Nat.zero_le _,by simp [remaining]⟩
end slhdsa.Oriented.Bulk
