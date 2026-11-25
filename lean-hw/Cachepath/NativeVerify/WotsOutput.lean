import Cachepath.NativeVerify.WotsProgram
import Shakebatch.WotsKeys
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.Wots
open ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]

theorem extract_range {N : Usize} (s : Matrix machine.width) (off lane n : Usize)
    (start : Array U8 N) (count : n.val=N.val/8) (alignment : N.val%8=0)
    (window : off.val+N.val/8 ≤ 25) (valid : lane.val<machine.width.val) :
    extract_lane_loop ⟨0#usize,n⟩ s off lane start ⦃ out => ∀ b < N.val,
      out.val[b]! = stateByte s lane.val (off.val+b/8) (b%8) ⦄ := by
  unfold extract_lane_loop
  apply WP.spec_mono (range_fold (extract_lane_loop.body s off lane) n _ (fun i out =>
    ∀ b < 8*i, out.val[b]! = stateByte s lane.val (off.val+b/8) (b%8)) ?_ ?_ ?_)
  · intro out h b hb; exact h b (by omega)
  · simp
  · intro it out stop live prior
    unfold extract_lane_loop.body
    step with core.iter.range.IteratorRange.next_Usize_some_spec it (by simpa [stop] using live) as ⟨_,next,tag,idx,ends⟩
    simp only [tag]
    step as ⟨pos,pv⟩
    step as ⟨limit,lv⟩
    step as ⟨part,back,_,plen,write⟩
    step as ⟨k,kv⟩
    step as ⟨row,atRow⟩
    step as ⟨word,atWord⟩
    simp only [lift,bind_ok]
    step as ⟨copy,cp⟩
    refine ⟨next,back copy,rfl,ends.trans stop,idx,?_⟩
    intro b hb
    rw [write copy,cp,Array.val_to_slice,word_bytes_write _ _ _ _ (by simp [pv];omega)]
    by_cases fresh : pos.val ≤ b
    · have lt : b < pos.val+8 := by omega
      rw [ite_eq_left ⟨fresh,lt⟩,atWord,← getElem!_pos,atRow,← getElem!_pos]
      have div : b/8=it.start.val := by omega
      have mod : b%8=b-pos.val := by omega
      simp only [stateByte,kv,div,mod]
    · rw [ite_eq_right (by omega)]
      exact prior b (by omega)
  · intro it out last stop
    unfold extract_lane_loop.body
    obtain ⟨⟨_,_⟩,no,tag,_⟩ := spec_imp_exists (core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop,last]))
    simp [no,tag]

theorem extract_lane_spec (N : Usize) (s : Matrix machine.width) (off lane : Usize)
    (alignment : N.val%8=0) (window : off.val+N.val/8 ≤ 25) (valid : lane.val<machine.width.val) :
    extract_lane N s off lane ⦃ out => ∀ b < N.val,
      out.val[b]! = stateByte s lane.val (off.val+b/8) (b%8) ⦄ := by
  unfold extract_lane
  step as ⟨n,count⟩
  exact extract_range s off lane n _ count alignment window valid

variable [stream : Stream] [correct : StreamCorrect]

theorem compress_endpoints {N : Usize} (slice : Slice (Array U8 N)) (pk : stream.State)
    (domain : Spec.Bytes) (tip : Nat → Spec.Bytes) (prior : correct.Absorbed pk domain)
    (values : ∀ j < slice.length, bytes slice.val[j]!.val=tip j) :
    recover_loop3 ⟨slice,0⟩ pk ⦃ out =>
      correct.Absorbed out (domain ++ (List.range slice.length).flatMap tip) ⦄ := by
  change shake.batch.keygen_loop0_loop0 ⟨slice,0⟩ pk ⦃ out => _ ⦄
  simpa using key_absorb slice pk domain 0 tip (by simpa using prior) (by simpa using values)

end slhdsa.NativeVerify.Wots
