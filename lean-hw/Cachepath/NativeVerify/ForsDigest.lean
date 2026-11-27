import Cachepath.NativeVerify.ForsExtract
import Shakebatch.Digest
import Shakebatch.Range

open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Fors
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem extract_bytes {N : Usize} (s : Matrix machine.width) (lane n : Usize)
    (start : Array U8 N) (count : n.val=N.val/8) (alignment : N.val%8=0)
    (small : N.val ≤ 32) (valid : lane.val<machine.width.val) :
    recover_loop0_loop5_loop0 ⟨0#usize,n⟩ s lane start ⦃ out => bytes out.val =
      Spec.Keccak.squeeze (ShakeBatch.lane s lane.val) 0 N.val ⦄ := by
  apply WP.spec_mono (extract_range s lane n start count alignment (by omega) valid)
  intro out cells
  rw [Spec.Keccak.squeeze_short _ _ _ (by omega)]
  apply List.ext_getElem
  · simp [bytes]
  · intro b hl hr
    have bn : b < N.val := by simpa using hl
    simp only [bytes,List.getElem_map,List.getElem_range,Nat.zero_add]
    rw [← getElem!_pos,cells b bn,stateByte,le_byte _ _ (by omega)]
    simp only [Spec.Keccak.extractByte,ShakeBatch.lane,Spec.Keccak.ofFnAt _ _ (by omega : b/8 < 25),cell]

theorem append_batch [stream : Stream] [ok : StreamCorrect] {N : Usize} (s : Matrix machine.width)
    (n active : Usize) (pk : stream.State) (previous : Spec.Bytes)
    (prior : ok.Absorbed pk previous) (count : n.val=N.val/8) (align : N.val%8=0)
    (small : N.val≤32) (width : active.val≤machine.width.val) :
    recover_loop0_loop5 N ⟨0#usize,active⟩ n pk s ⦃ out => ok.Absorbed out
      (previous ++ (List.range active.val).flatMap (fun l => Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val)) ⦄ := by
  unfold recover_loop0_loop5
  apply range_fold (recover_loop0_loop5.body N n s) active pk (fun i v => ok.Absorbed v
      (previous ++ (List.range i).flatMap (fun l => Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val)))
  · simpa using prior
  · intro it v stop live prev
    unfold recover_loop0_loop5.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,inc,ends⟩
    simp only [tag]
    step with extract_bytes s it.start n (Array.repeat N 0#u8) count align small (live.trans_le width) as ⟨node,ex⟩
    simp only [lift,bind_ok]
    step with ok.append v _ prev node.to_slice as ⟨out,absorbed⟩
    refine ⟨next,out,rfl,ends.trans stop,inc,?_⟩
    rw [inc,List.range_succ,List.flatMap_append]
    simpa only [Array.val_to_slice,ex,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using absorbed
  · intro it v last stop
    unfold recover_loop0_loop5.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

end slhdsa.NativeVerify.Fors
