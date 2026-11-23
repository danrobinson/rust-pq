import Rcavx.Paired
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

private theorem count16 : SHA512_BLOCK_WORDS_NUM = ok 16#usize := by unfold SHA512_BLOCK_WORDS_NUM SHA512_BLOCK_BYTE_LEN core.mem.size_of; simp only [bind_ok]; rfl

private theorem signedNext (it : core.ops.range.Range I32) (he : it.end=4#i32)
    (lo : 0 ≤ it.start.val) (hi : it.start.val<4) :
    core.iter.range.IteratorRange.next core.iter.range.StepI32 it ⦃ o it' =>
      o=some it.start ∧ it'.start.val=it.start.val+1 ∧ it'.end=it.end ⦄ := by
  have cmp (a b : I32) : core.iter.range.StepI32.partialOrdInst.lt a b = ok (decide (a.val<b.val)) := by rfl
  have clone (a : I32) : core.iter.range.StepI32.cloneInst.clone a = ok a := by rfl
  have inside : it.start.val < it.end.val := by rw [he]; exact hi
  simp only [core.iter.range.IteratorRange.next,cmp,inside,decide_true,bind_ok,ite_true,clone]
  have room : it.start.val+(1#usize).val ≤ IScalar.max .I32 := by scalar_tac
  simp only [core.iter.range.StepI32,core.iter.range.IScalarStep,core.iter.range.IScalarStep.forward_checked,
    room,dif_pos,bind_ok,step_simps]
  simp

theorem single_0_63 (W : Words) (iv : Spec.SHA512.State) (s : St) (x ms : Ms) (rec : Rec W)
    (pre : Good W iv 0 s x ms 16#usize) :
    rounds_0_63_avx s x ms ⦃ out _ cache => state512 out = after W iv 64 ∧ Cache W 32 cache ⦄ := by
  unfold rounds_0_63_avx
  simp only [count16,bind_ok]
  unfold rounds_0_63_avx_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range I32 × St × Ms × Ms × Usize => 4-q.1.start.val.toNat)
    (inv := fun q => q.1.end=4#i32 ∧ 0 ≤ q.1.start.val ∧ q.1.start.val ≤ 4 ∧ Good W iv (8*q.1.start.val.toNat) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
  · rintro ⟨it,s,x,ms,idx⟩ ⟨he,lo,hi,prior⟩
    simp only at he lo hi prior
    unfold rounds_0_63_avx_loop0.body
    by_cases inside : it.start.val<4
    · step with signedNext it he lo inside as ⟨o,next,ho,hn,he'⟩
      simp only [ho,bind_ok]
      step with single_inner W iv it.start.val.toNat (by omega) s x ms idx rec prior as ⟨s',x',ms',idx',post⟩
      refine ⟨he'.trans he,by omega,by omega,?_,by omega⟩
      simpa only [show 8*next.start.val.toNat=8*it.start.val.toNat+8 by omega] using post
    · have es : it.start=4#i32 := by scalar_tac
      have eq : it=⟨4#i32,4#i32⟩ := by cases it; simp_all
      subst it
      have cmp (a b : I32) : core.iter.range.StepI32.partialOrdInst.lt a b = ok (decide (a.val<b.val)) := by rfl
      simp only [core.iter.range.IteratorRange.next,cmp,lt_irrefl,decide_false,bind_ok,Bool.false_eq_true,ite_false,step_simps]
      exact ⟨prior.1,prior.2.2.1⟩
  · exact ⟨rfl,by change (0:Int) ≤ 0; omega,by change (0:Int) ≤ 4; omega,pre⟩

theorem paired_0_63 (W V : Words) (iv : Spec.SHA512.State) (s : St) (x : Array Wide 8#usize) (ms : Ms)
    (saved : Array Lane 40#usize) (rec : Rec W) (recV : Rec V)
    (pre : Good2 W V iv 0 s x ms saved 16#usize) :
    rounds_0_63_avx2 s x ms saved ⦃ out _ cache archive => state512 out = after W iv 64 ∧ Cache W 32 cache ∧ Archive V 40 archive ⦄ := by
  unfold rounds_0_63_avx2
  simp only [count16,bind_ok]
  unfold rounds_0_63_avx2_loop0
  apply loop.spec_decr_nat
    (measure := fun q : core.ops.range.Range Usize × St × Array Wide 8#usize × Ms × Array Lane 40#usize × Usize => 5-q.1.start.val)
    (inv := fun q => q.1.end=5#usize ∧ 1 ≤ q.1.start.val ∧ q.1.start.val ≤ 5 ∧ Good2 W V iv (8*(q.1.start.val-1)) q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)
  · rintro ⟨it,s,x,ms,saved,idx⟩ ⟨he,lo,hi,prior⟩
    simp only at he lo hi prior
    unfold rounds_0_63_avx2_loop0.body
    by_cases inside : it.start.val<5
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [he]; exact inside) as ⟨o,next,ho,hn,he'⟩
      simp only [ho,bind_ok]
      step with paired_inner W V iv (it.start.val-1) (by omega) s x ms saved idx it.start (by omega) rec recV prior as ⟨s',x',ms',saved',idx',post⟩
      refine ⟨he'.trans he,by omega,by omega,?_,by omega⟩
      simpa only [show 8*(next.start.val-1)=8*(it.start.val-1)+8 by omega] using post
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [he]; exact Nat.le_of_not_gt inside) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      rw [show it.start.val=5 by omega] at prior
      exact ⟨prior.1,prior.2.2.1,prior.2.2.2.1⟩
  · exact ⟨rfl,by change 1 ≤ 1; omega,by change 1 ≤ 5; omega,pre⟩
end slhdsa.X86.RustCrypto512
