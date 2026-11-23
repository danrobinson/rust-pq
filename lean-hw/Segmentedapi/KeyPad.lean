import Segmentedapi.Funs
import Slhdsa.Proofs.HashMsg
open Aeneas Aeneas.Std Result
namespace slhdsa.SegmentedApi
abbrev Range := core.ops.range.Range Usize

/-- One recurrence handles both HMAC pad constants and the two block widths. -/
def keyPad {N B : Usize} (key : Array U8 N) (it : Range) (pad : Array U8 B) : Result (Array U8 B) := do
  loop (fun (q : Range × Array U8 B) => do
    let (range,row) := q
    let (index, nextRange) ← core.iter.range.IteratorRange.next core.iter.range.StepUsize range
    match index with
    | none => ok (ControlFlow.done row)
    | some i =>
      let k ← Array.index_usize key i
      let v ← Array.index_usize row i
      let updated ← Array.update row i (v ^^^ k)
      ok (ControlFlow.cont (nextRange, updated))) (it,pad)

theorem keyPad_spec {N B : Usize} (key : Array U8 N) (c : U8) (pad : Array U8 B)
    (fits : N.val ≤ B.val) (fresh : pad.val = List.replicate B.val c) :
    keyPad key ⟨0#usize,N⟩ pad ⦃ out =>
      out.val = (key.val.map (· ^^^ c)) ++ List.replicate (B.val-N.val) c ⦄ := by
  unfold keyPad
  apply loop.spec_decr_nat (measure := fun q : Range × Array U8 B => N.val-q.1.start.val)
    (inv := fun q => q.1.end=N ∧ q.1.start.val≤N.val ∧
      q.2.val=(key.val.map (· ^^^ c)).take q.1.start.val ++ List.replicate (B.val-q.1.start.val) c)
  · rintro ⟨it,row⟩ ⟨last,bounded,contents⟩
    simp only at last bounded contents
    by_cases more : it.start.val<N.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [last]; exact more) as ⟨opt,next,item,inc,stop⟩
      simp only [item]
      step as ⟨k,kEq⟩
      step as ⟨v,vEq⟩
      have filled : v=c := by
        rw [vEq,← getElem!_eq _ _ (by simp; omega),contents]
        have len : ((key.val.map (· ^^^ c)).take it.start.val).length=it.start.val := by simp; omega
        rw [List.getElem!_eq_getElem?_getD,List.getElem?_append_right (by omega),len,Nat.sub_self]
        simp [show 0 < B.val-it.start.val by omega]
      step as ⟨out,wrote⟩
      refine ⟨stop.trans last,by omega,?_,by omega⟩
      rw [wrote,Array.set_val_eq,contents,inc,filled,kEq]
      have len : ((key.val.map (· ^^^ c)).take it.start.val).length=it.start.val := by simp; omega
      rw [show B.val-it.start.val=(B.val-(it.start.val+1))+1 by omega,List.replicate_succ,
        set_mid _ _ _ _ _ len.symm,List.take_succ_eq_append_getElem (by simp; omega)]
      simp only [List.getElem_map,List.append_assoc,List.singleton_append]
      have comm (v : U8) : c ^^^ v = v ^^^ c := (UScalar.eq_equiv_bv_eq ..).2 (BitVec.xor_comm ..)
      rw [comm]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last]; omega) as ⟨opt,next,none,_⟩
      simp only [none,step_simps]
      simpa [show it.start.val=N.val by omega,List.take_of_length_le (by simp : (key.val.map (· ^^^ c)).length ≤ N.val)] using contents
  · simpa using fresh

@[step] theorem pad0 {N : Usize} (key : Array U8 N) (pad : Array U8 64#usize)
    (fits : N.val≤64) (fresh : pad.val=List.replicate 64 54#u8) :
    SegmentedApiRust.slh.message.randomizer_loop0 ⟨0#usize,N⟩ key pad ⦃ out =>
      bytes out.val = (bytes key.val ++ List.replicate (64-N.val) 0#8).map (· ^^^ 54#8) ⦄ := by
  have eq : SegmentedApiRust.slh.message.randomizer_loop0 ⟨0#usize,N⟩ key pad =
      keyPad key ⟨0#usize,N⟩ pad := by
    unfold SegmentedApiRust.slh.message.randomizer_loop0 keyPad
    congr 1
    funext q
    rcases q with ⟨range,row⟩
    unfold SegmentedApiRust.slh.message.randomizer_loop0.body
    simp only [lift,bind_tc_eq,bind_ok]
    rfl
  rw [eq]
  apply WP.spec_mono (keyPad_spec key 54#u8 pad fits fresh)
  intro out result
  rw [result,bytes_append,bytes_map_xor,bytes_replicate]
  simp

@[step] theorem pad1 {N : Usize} (key : Array U8 N) (pad : Array U8 64#usize)
    (fits : N.val≤64) (fresh : pad.val=List.replicate 64 92#u8) :
    SegmentedApiRust.slh.message.randomizer_loop1 ⟨0#usize,N⟩ key pad ⦃ out =>
      bytes out.val = (bytes key.val ++ List.replicate (64-N.val) 0#8).map (· ^^^ 92#8) ⦄ := by
  have eq : SegmentedApiRust.slh.message.randomizer_loop1 ⟨0#usize,N⟩ key pad =
      keyPad key ⟨0#usize,N⟩ pad := by
    unfold SegmentedApiRust.slh.message.randomizer_loop1 keyPad
    congr 1
    funext q
    rcases q with ⟨range,row⟩
    unfold SegmentedApiRust.slh.message.randomizer_loop1.body
    simp only [lift,bind_tc_eq,bind_ok]
    rfl
  rw [eq]
  apply WP.spec_mono (keyPad_spec key 92#u8 pad fits fresh)
  intro out result
  rw [result,bytes_append,bytes_map_xor,bytes_replicate]
  simp

@[step] theorem pad2 {N : Usize} (key : Array U8 N) (pad : Array U8 128#usize)
    (fits : N.val≤128) (fresh : pad.val=List.replicate 128 54#u8) :
    SegmentedApiRust.slh.message.randomizer_loop2 ⟨0#usize,N⟩ key pad ⦃ out =>
      bytes out.val = (bytes key.val ++ List.replicate (128-N.val) 0#8).map (· ^^^ 54#8) ⦄ := by
  have eq : SegmentedApiRust.slh.message.randomizer_loop2 ⟨0#usize,N⟩ key pad =
      keyPad key ⟨0#usize,N⟩ pad := by
    unfold SegmentedApiRust.slh.message.randomizer_loop2 keyPad
    congr 1
    funext q
    rcases q with ⟨range,row⟩
    unfold SegmentedApiRust.slh.message.randomizer_loop2.body
    simp only [lift,bind_tc_eq,bind_ok]
    rfl
  rw [eq]
  apply WP.spec_mono (keyPad_spec key 54#u8 pad fits fresh)
  intro out result
  rw [result,bytes_append,bytes_map_xor,bytes_replicate]
  simp

@[step] theorem pad3 {N : Usize} (key : Array U8 N) (pad : Array U8 128#usize)
    (fits : N.val≤128) (fresh : pad.val=List.replicate 128 92#u8) :
    SegmentedApiRust.slh.message.randomizer_loop3 ⟨0#usize,N⟩ key pad ⦃ out =>
      bytes out.val = (bytes key.val ++ List.replicate (128-N.val) 0#8).map (· ^^^ 92#8) ⦄ := by
  have eq : SegmentedApiRust.slh.message.randomizer_loop3 ⟨0#usize,N⟩ key pad =
      keyPad key ⟨0#usize,N⟩ pad := by
    unfold SegmentedApiRust.slh.message.randomizer_loop3 keyPad
    congr 1
    funext q
    rcases q with ⟨range,row⟩
    unfold SegmentedApiRust.slh.message.randomizer_loop3.body
    simp only [lift,bind_tc_eq,bind_ok]
    rfl
  rw [eq]
  apply WP.spec_mono (keyPad_spec key 92#u8 pad fits fresh)
  intro out result
  rw [result,bytes_append,bytes_map_xor,bytes_replicate]
  simp
end slhdsa.SegmentedApi
