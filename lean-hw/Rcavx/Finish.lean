import Rcavx.Inner
import Streamscalar.Fips
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.RustCrypto512
open RcAvxRust RcAvxRust.sha512.x86_avx2 Stream
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

private theorem add_word (W : Words) (t pos : Nat) (xs : List U64)
    (eq : (xs[2*pos]!.bv,xs[2*pos+1]!.bv) = weighted W (t/2)) :
    xs[2*pos+t%2]!.bv = Spec.SHA512.K[t]!+W[t]! := by
  by_cases even : t%2=0
  · simpa only [even,Nat.add_zero,show 2*(t/2)=t by omega] using (congrArg Prod.fst eq).trans (weight0 W (t/2))
  · simpa only [show t%2=1 by omega,show 2*(t/2)+1=t by omega] using (congrArg Prod.snd eq).trans (weight1 W (t/2))

theorem last16 (W : Words) (iv : Spec.SHA512.State) (s : St) (ms : Ms)
    (start : state512 s=after W iv 64) (cache : Cache W 32 ms) :
    rounds_64_79 s ms ⦃ out => state512 out=after W iv 80 ⦄ := by
  unfold rounds_64_79 cast_ms
  step with cast_spec (len:=16#usize) ms (by rfl) as ⟨ws,reads⟩
  unfold rounds_64_79_loop
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × St => 80-q.1.start.val)
    (inv := fun q => q.1.end=80#usize ∧ 64 ≤ q.1.start.val ∧ q.1.start.val ≤ 80 ∧ state512 q.2=after W iv q.1.start.val)
  · rintro ⟨it,s⟩ ⟨stop,lo,hi,prior⟩
    simp only at stop lo hi prior
    unfold rounds_64_79_loop.body
    by_cases more : it.start.val<80
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [stop]; exact more) as ⟨o,next,ho,hn,he⟩
      simp only [ho,lift,bind_ok]
      have mask : (it.start &&& 15#usize).val = it.start.val%16 := by
        calc
          (it.start &&& 15#usize).val = it.start.val &&& (15#usize).val := BitVec.toNat_and _ _
          _ = it.start.val%16 := Nat.and_two_pow_sub_one_eq_mod _ 4
      step as ⟨wk,hr⟩
      have row := (reads ((it.start.val/2)%8) (by omega)).trans (cache (it.start.val/2) (by omega) (by omega))
      have v := add_word W it.start.val ((it.start.val/2)%8) ws.val row
      rw [show 2*((it.start.val/2)%8)+it.start.val%2=it.start.val%16 by omega] at v
      have word : wk.bv = Spec.SHA512.K[it.start.val]!+W[it.start.val]! := by rw [hr,← getElem!_eq ws.val _ (by scalar_tac),mask]; exact v
      step with next_round s wk W iv it.start.val prior word as ⟨out,last⟩
      exact ⟨he.trans stop,by omega,by omega,hn ▸ last,by omega⟩
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [stop]; exact Nat.le_of_not_gt more) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      simpa only [show it.start.val=80 by omega] using prior
  · exact ⟨rfl,by change 64 ≤ 64; omega,by change 64 ≤ 80; omega,start⟩

theorem second80 (W : Words) (s : St) (saved : Array Lane 40#usize) (archive : Archive W 40 saved) :
    process_second_block s saved ⦃ out => state512 out=after W (state512 s) 80 ⦄ := by
  unfold process_second_block cast_rs
  step with cast_spec (len:=80#usize) saved (by rfl) as ⟨ws,reads⟩
  simp only [lift,bind_ok,core.slice.Slice.iter]
  unfold process_second_block_loop
  apply loop.spec_decr_nat (measure := fun q : core.slice.iter.Iter U64 × St => 80-q.1.i)
    (inv := fun q => q.1.slice=ws.to_slice ∧ q.1.i ≤ 80 ∧ state512 q.2=after W (state512 s) q.1.i)
  · rintro ⟨it,v⟩ ⟨slice,hi,prior⟩
    simp only at slice hi prior
    simp only
    unfold process_second_block_loop.body
    by_cases more : it.i<80
    · have bound : it.i<ws.val.length := by simpa using more
      let next := {it with i:=it.i+1}
      have read : core.slice.iter.IteratorSliceIter.next it = ok (some ws.val[it.i],next) := by
        simp [core.slice.iter.IteratorSliceIter.next,next,slice,more]
      rw [read]; simp only [bind_ok]
      have eq := (reads (it.i/2) (by omega)).trans (archive (it.i/2) (by omega))
      have value := add_word W it.i (it.i/2) ws.val eq
      rw [show 2*(it.i/2)+it.i%2=it.i by omega,getElem!_pos ws.val it.i bound] at value
      step with next_round v _ W (state512 s) it.i prior value as ⟨out,h⟩
      exact ⟨slice,by change it.i+1 ≤ 80; omega,h,by change 80-(it.i+1)<80-it.i; omega⟩
    · have read : core.slice.iter.IteratorSliceIter.next it = ok (none,it) := by
        simp [core.slice.iter.IteratorSliceIter.next,slice,more]
      simp only [read,bind_ok,step_simps]
      simpa only [show it.i=80 by omega] using prior
  · exact ⟨rfl,Nat.zero_le _,rfl⟩

theorem feed (s v : St) (block : Spec.Bytes)
    (h : state512 v=after (Spec.SHA512.schedule block) (state512 s) 80) :
    accumulate_state s v ⦃ out => slhdsa.S512.wv out.val = Spec.SHA512.compress (slhdsa.S512.wv s.val) block ⦄ := by
  have count : SHA512_HASH_WORDS_NUM = ok 8#usize := by unfold SHA512_HASH_WORDS_NUM SHA512_HASH_BYTE_LEN core.mem.size_of; simp only [bind_ok]; rfl
  unfold accumulate_state
  simp only [count,bind_ok]
  exact feed512_fips s v block h
end slhdsa.X86.RustCrypto512
