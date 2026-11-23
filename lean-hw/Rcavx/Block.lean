import Rcavx.Outer
import Rcavx.Finish
import Rcavx.Load
import Streamround.Blocks
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream

private theorem msg_rec (b : Block) : Rec (msgW b) := slhdsa.H512.schedule_rec (bytes b.val)

theorem single (st : St) (b : Block) :
    sha512_compress_x86_64_avx st b ⦃ out => slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv st.val) (bytes b.val) ⦄ := by
  unfold sha512_compress_x86_64_avx
  simp only [core.core_arch.x86.sse2._mm_setzero_si128,lift,bind_ok,core.slice.Slice.as_ptr,
    core.ptr.const_ptr.RawPtrConstT.cast,Array.val_to_slice]
  step with initial b as ⟨x,ms,words,cache⟩
  have start : Good (msgW b) (state512 st) 0 st x ms 16#usize := ⟨rfl,words,cache,rfl⟩
  step with single_0_63 (msgW b) (state512 st) st x ms (msg_rec b) start as ⟨s,_,ms',rounds,keys⟩
  step with last16 (msgW b) (state512 st) s ms' rounds keys as ⟨final,done⟩
  exact feed st final _ done

theorem pair_list (bs : Array Block 2#usize) : bs.val=[bs.val[0]!,bs.val[1]!] := by
  apply List.ext_getElem
  · simp
  · intro i hi _
    have bound : i<2 := by simpa using hi
    interval_cases i <;> simp

abbrev Group := Array Block 2#usize
abbrev ArchiveRegs := Array Lane 40#usize
abbrev Regs := Array Wide 8#usize

theorem paired_loop (groups : Slice Group) (st : St) (ms : Ms) (saved : ArchiveRegs) (x : Regs) :
    compress_loop ⟨groups,0⟩ st ms saved x ⦃ out => slhdsa.S512.wv out.val =
      groups.val.foldl (fun s g => fold512 s g.val) (slhdsa.S512.wv st.val) ⦄ := by
  let iv := slhdsa.S512.wv st.val
  unfold compress_loop
  apply loop.spec_decr_nat
    (measure := fun q : core.slice.iter.Iter Group × St × Ms × ArchiveRegs × Regs => groups.length-q.1.i)
    (inv := fun q => q.1.slice=groups ∧ q.1.i≤groups.length ∧ slhdsa.S512.wv q.2.1.val=
      (groups.val.take q.1.i).foldl (fun s g => fold512 s g.val) iv)
  · rintro ⟨it,s,ms,saved,x⟩ ⟨slice,bound,prior⟩
    simp only at slice bound prior
    simp only
    unfold compress_loop.body
    by_cases more : it.i<groups.val.length
    · let grp := groups.val[it.i]
      let next := {it with i := it.i+1}
      have read : core.slice.iter.IteratorSliceIter.next it = ok (some grp,next) := by
        simp [core.slice.iter.IteratorSliceIter.next,next,grp,slice,more,Slice.length]
      rw [read]; simp only [bind_ok]
      let a := grp.val[0]!
      let b := grp.val[1]!
      step with initial2 grp x ms saved as ⟨x',ms',saved',words,cache,arch⟩
      have start : Good2 (msgW a) (msgW b) (state512 s) 0 s x' ms' saved' 16#usize := ⟨rfl,words,cache,arch,rfl⟩
      step with paired_0_63 (msgW a) (msgW b) (state512 s) s x' ms' saved' (msg_rec a) (msg_rec b) start as ⟨s1,x1,ms1,saved1,rounds,keys,archive⟩
      step with last16 (msgW a) (state512 s) s1 ms1 rounds keys as ⟨s2,done⟩
      step with feed s s2 (bytes a.val) done as ⟨s3,first⟩
      step with second80 (msgW b) s3 saved1 archive as ⟨s4,done2⟩
      step with feed s3 s4 (bytes b.val) done2 as ⟨out,second⟩
      refine ⟨slice,by change it.i+1 ≤ groups.val.length; omega,?_,by change groups.val.length-(it.i+1)<groups.val.length-it.i; omega⟩
      rw [second,first,prior]
      change _ = (groups.val.take (it.i+1)).foldl _ _
      rw [List.take_succ_eq_append_getElem more,List.foldl_append]
      simp only [List.foldl_cons,List.foldl_nil]
      change _ = fold512 _ grp.val
      conv_rhs => rw [pair_list grp]
      simp only [fold512,List.foldl_cons,List.foldl_nil,a,b,grp]
    · have read : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more,Slice.length]
      simp only [read,bind_ok,step_simps]
      simpa only [List.take_of_length_le (Nat.le_of_not_gt more)] using prior
  · exact ⟨rfl,Nat.zero_le _,rfl⟩
end slhdsa.X86.RustCrypto512
