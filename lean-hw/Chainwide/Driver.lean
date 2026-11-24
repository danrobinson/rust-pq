import Chainwide.Dispatch
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Chain
open ChainWideRust.sha256.x86.avx512

private theorem bind_if {A B : Type} (p : Prop) [Decidable p] (a b : Result A) (f : A → Result B) :
    Std.bind (if p then a else b) f = if p then Std.bind a f else Std.bind b f := by split <;> rfl

private theorem same_loop : @chains_loop0_loop3 = @chains_loop0_loop1 := rfl
private theorem same_pref : @chains_loop0_loop2 = @chains_loop0_loop0 := rfl

theorem driver_spec (N : Usize) (state : Array U32 8#usize) (blocks : Rows) (starts ends : Slice U32)
    (iv : Hash) (stride : Reg) (it : Iter) (hn : N.val=16 ∨ N.val=24 ∨ N.val=32)
    (hs : blocks.length ≤ starts.length) (he : blocks.length ≤ ends.length) (strideOK : Digest.Stride stride 64)
    (init : ∀ j, stateWords (laneState iv j) = wv state.val)
    (hi : it.iter.start = 0#usize) (hend : it.iter.end.val = blocks.length) (hstep : it.step_by = 16#usize) :
    chains_loop0 N it state blocks starts ends iv stride Store.control
      ⦃ out => Intel.Chain.Ended N state blocks out starts ends ⦄ := by
  let expected := Intel.Chain.expected N state blocks starts ends
  unfold chains_loop0
  apply loop.spec_decr_nat (measure := fun p : Iter × Rows => blocks.length-p.1.iter.start.val)
    (inv := fun p => p.1.iter.end.val = blocks.length ∧ p.1.step_by = 16#usize ∧
      p.1.iter.start.val ≤ blocks.length ∧ InPlace.Processed expected blocks p.2 p.1.iter.start.val)
  · rintro ⟨i,buf⟩ ⟨ie,step16,bound,processed⟩
    simp only at ie step16 bound processed
    have len := processed.1
    unfold chains_loop0.body
    by_cases lt : i.iter.start.val < i.iter.end.val
    · step with Store.next i lt step16 as ⟨o,nxt,opt,nx,ne,ns⟩
      simp only [opt]
      step as ⟨diff,hd⟩
      simp only [lift,bind_ok]
      step as ⟨stop,hstop⟩
      step as ⟨b,back,hb,lb,hback⟩
      have wid : (core.cmp.impls.OrdUsize.min diff 16#usize).val = min diff.val 16 := by simp
      have oldLength : (Slice.len buf).val = blocks.length := len
      have nb : nxt.iter.start.val = i.iter.start.val+b.length := by omega
      conv => lhs; equals (dispatch N i.iter.start state b starts ends iv stride Store.control >>= fun r => ok (cont (nxt,back r))) =>
        unfold dispatch vectorBatch loadRanges loadCounters
        simp only [bind_tc_eq,Std.bind_assoc,bind_ok,bind_if,lift,same_loop,same_pref]
        rfl
      step with dispatch_spec N i.iter.start state b starts ends iv stride hn (by omega) (by omega)
        (by omega) (by omega) strideOK init as ⟨r,lr,rows⟩
      refine ⟨by rw [ne,ie],ns.trans step16,by omega,?_,by omega⟩
      rw [nb,← lr]
      apply InPlace.advance _ _ _ _ _ _ processed (by omega)
      · simp only [hback,Slice.setSlice!_val]
      · intro k hk
        have actual := rows k (by omega)
        have before := processed.2 (i.iter.start.val+k) (by omega)
        rw [if_neg (by omega)] at before
        rw [hb,List.getElem!_slice _ _ _ buf.val (by change stop.val ≤ buf.length ∧ _; omega),before] at actual
        exact actual
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec i (by omega) as ⟨o,next,opt,_⟩
      simp only [opt,step_simps]
      refine ⟨len,fun j hj => ?_⟩
      have before := processed.2 j hj
      simpa only [if_pos (by omega : j < i.iter.start.val),expected,Intel.Chain.expected] using before
  · simp [hi,hend,hstep,InPlace.Processed]

end slhdsa.X86.Chain
