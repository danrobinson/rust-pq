import Kgridbulk.Pack
import Kdiag.Odd
import Slhdsa.Proofs.Keccak
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kgridbulk
open KgridbulkRust KgridbulkRust.shake256.stream_x86
private def roundPrefix (a : State) (k : Nat) := ((KgridbulkRust.shake256.RC.val.take k).map (·.bv)).foldl round a

private theorem next (a : State) (k : Nat) (hk : k < 24) :
    roundPrefix a (k+1) = round (roundPrefix a k) KgridbulkRust.shake256.RC.val[k]!.bv := by
  have valid : k < KgridbulkRust.shake256.RC.val.length := by simpa using hk
  unfold roundPrefix
  rw [List.take_succ_eq_append_getElem valid,List.map_append,List.foldl_append,
    getElem!_pos KgridbulkRust.shake256.RC.val k valid]
  rfl

theorem rounds (view : Bool → Kdiag.Grid → State)
    (evenRound : ∀ (s : Kdiag.Grid) (c : U64), even s c ⦃ t => view true t = round (view false s) c.bv ⦄)
    (oddRound : ∀ (s : Kdiag.Grid) (c : U64), odd s c ⦃ t => view false t = round (view true s) c.bv ⦄)
    (a : Kdiag.Grid) :
    absorb_loop0_loop1 ⟨⟨0#usize,24#usize⟩,2#usize⟩ a ⦃ t => view false t = permute (view false a) ⦄ := by
  unfold absorb_loop0_loop1
  apply loop.spec_decr_nat
    (measure := fun (p : core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize) × Kdiag.Grid) =>
      24-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end=24#usize ∧ p.1.step_by=2#usize ∧ p.1.iter.start.val≤24 ∧
      p.1.iter.start.val%2=0 ∧ view false p.2 = roundPrefix (view false a) p.1.iter.start.val)
  · rintro ⟨it,st⟩ ⟨he,hs,hb,hd,prev⟩
    simp only at he hs hb hd prev
    unfold absorb_loop0_loop1.body
    have limit : (24#usize).val = 24 := rfl
    by_cases more : it.iter.start.val < it.iter.end.val
    · have bound : it.iter.start.val+2 ≤ 24 := by rw [he] at more; omega
      step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_some_spec it more
        (by rw [hs];decide) (by rw [he,hs];exact bound) as ⟨o,nxt,ho,hn,he',hs'⟩
      simp only [ho]
      step as ⟨c,hc⟩
      step with evenRound st c as ⟨u,hu⟩
      step as ⟨idx,hi⟩
      step as ⟨c',hc'⟩
      step with oddRound u c' as ⟨v,hv⟩
      have inc : nxt.iter.start.val = it.iter.start.val+2 := by rw [hn,hs]; rfl
      refine ⟨he'.trans he,hs'.trans hs,by omega,by omega,?_,by omega⟩
      rw [hv,hu,prev,inc,next _ (it.iter.start.val+1) (by omega),next _ it.iter.start.val (by omega)]
      have h0 : it.iter.start.val < KgridbulkRust.shake256.RC.val.length := by simp; omega
      have h1 : it.iter.start.val+1 < KgridbulkRust.shake256.RC.val.length := by simp; omega
      rw [getElem!_pos KgridbulkRust.shake256.RC.val it.iter.start.val h0, getElem!_pos KgridbulkRust.shake256.RC.val (it.iter.start.val+1) h1, hc,hc']
      congr 2
      simp only [hi]
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have last : it.iter.start.val=24 := by rw [he] at more; omega
      rw [prev,last]
      unfold roundPrefix
      rw [List.take_of_length_le (by simp)]
      have constants : KgridbulkRust.shake256.RC.val.map (·.bv)=rc.toList := by unfold KgridbulkRust.shake256.RC rc; rfl
      rw [constants]
      rfl
  · simp [roundPrefix]
end slhdsa.Kgridbulk
