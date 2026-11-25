import Cachepath.NativeVerify.ActiveHashProgram
import Shakebatch.Digest
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeVerify.ActiveHash
open ShakeBatch
variable [machine : Machine]
theorem put_row {N : Usize} (s : Matrix machine.width) (offset i : Usize)
    (values : Array (Array U8 N) machine.width) (active : Usize) (boundActive : active.val ≤ machine.width.val)
    (row : offset.val+i.val < 25) (bytesFit : i.val*8+8 ≤ N.val) :
    put_active_loop0_loop0 ⟨0#usize,active⟩ s offset values i ⦃ out =>
      ∀ k < 25, ∀ j < active.val, cell out k j =
        if k=offset.val+i.val then inputWord values.val[j]!.val i.val else cell s k j ⦄ := by
  unfold put_active_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => active.val-q.1.start.val)
    (inv := fun q => q.1.end=active ∧ q.1.start.val ≤ active.val ∧
      ∀ k < 25, ∀ j < active.val, cell q.2 k j =
        if k=offset.val+i.val ∧ j < q.1.start.val then inputWord values.val[j]!.val i.val else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold put_active_loop0_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < active.val := he ▸ more
      have wide : it.start.val < machine.width.val := lt.trans_le boundActive
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho,bind_ok,lift]
      step as ⟨val,get⟩
      step with word_spec (Array.to_slice val) i (by simpa using bytesFit) as ⟨w,hw⟩
      step as ⟨r,index⟩
      step as ⟨a,back,read,write⟩
      step as ⟨a',update⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write,update,read,← getElem!_pos,cell_write _ _ _ _ (by omega) wide,index,h k hk j hj]
      by_cases pos : k=offset.val+i.val
      · subst k
        by_cases col : j=it.start.val
        · subst j
          simp only [true_and,ite_true,hn,Nat.lt_add_one,ite_false,lt_self_iff_false]
          rw [get,← getElem!_pos] at hw
          simpa only [Array.val_to_slice,inputWord] using hw
        · have equiv : j < nxt.start.val ↔ j < it.start.val := by omega
          simp [col,equiv]
      · simp [pos]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=active.val := by rw [he] at more; omega
      intro k hk j hj
      simpa [eq,hj] using h k hk j hj
  · simp

/-- Insert every payload word at its designated offset without disturbing other state words. -/
theorem put_spec {N : Usize} (s : Matrix machine.width) (offset : Usize)
    (values : Array (Array U8 N) machine.width) (active : Usize) (boundActive : active.val ≤ machine.width.val) (fits : offset.val+N.val/8 ≤ 25) :
    put_active s offset values active ⦃ out =>
      ∀ k < 25, ∀ j < active.val, cell out k j =
        if offset.val ≤ k ∧ k < offset.val+N.val/8 then inputWord values.val[j]!.val (k-offset.val) else cell s k j ⦄ := by
  unfold put_active
  step as ⟨last,count⟩
  unfold put_active_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Matrix machine.width => last.val-q.1.start.val)
    (inv := fun q => q.1.end=last ∧ q.1.start.val ≤ last.val ∧
      ∀ k < 25, ∀ j < active.val, cell q.2 k j =
        if offset.val ≤ k ∧ k < offset.val+q.1.start.val then inputWord values.val[j]!.val (k-offset.val) else cell s k j)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold put_active_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < last.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with put_row state offset it.start values active boundActive (by omega) (by omega) as ⟨st,write⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro k hk j hj
      rw [write k hk j hj,h k hk j hj]
      by_cases row : k=offset.val+it.start.val
      · subst k
        simp [hn]
      · have equiv : k < offset.val+nxt.start.val ↔ k < offset.val+it.start.val := by omega
        simp only [row,ite_false,equiv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = N.val/8 := by rw [he] at more; omega
      simpa only [eq] using h
  · simp

theorem read_row {N : Usize} (s : Matrix machine.width) (i : Usize)
    (values : Array (Array U8 N) machine.width) (active : Usize) (boundActive : active.val ≤ machine.width.val) (within : i.val < 25) (fits : i.val*8+8 ≤ N.val) :
    read_active_loop0_loop0 ⟨0#usize,active⟩ s values i ⦃ out =>
      ∀ j < active.val, ∀ b < N.val, outputByte out j b =
        if 8*i.val ≤ b ∧ b < 8*i.val+8 then stateByte s j i.val (b-8*i.val) else outputByte values j b ⦄ := by
  unfold read_active_loop0_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array (Array U8 N) machine.width => active.val-q.1.start.val)
    (inv := fun q => q.1.end=active ∧ q.1.start.val ≤ active.val ∧
      ∀ j < active.val, ∀ b < N.val, outputByte q.2 j b =
        if j < q.1.start.val ∧ 8*i.val ≤ b ∧ b < 8*i.val+8 then stateByte s j i.val (b-8*i.val) else outputByte values j b)
  · rintro ⟨it,state⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold read_active_loop0_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < active.val := he ▸ more
      have wide : it.start.val < machine.width.val := lt.trans_le boundActive
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step as ⟨a,restore,get,save⟩
      step as ⟨pos,pv⟩
      step as ⟨stop,sv⟩
      step as ⟨part,back,pr,plen,write⟩
      step as ⟨row,rowAt⟩
      step as ⟨w,word⟩
      simp only [lift,bind_ok]
      step as ⟨copied,cp⟩
      refine ⟨hen.trans he, by omega, ?_, by omega⟩
      intro j hj b hb
      by_cases same : j=it.start.val
      · subst j
        rw [outputByte,save,Array.set_val_eq,setSame _ _ _ (by simpa using wide)]
        rw [write copied,cp,Array.val_to_slice,word_bytes_write _ _ _ _ (by simp [pv];omega)]
        rw [get,← getElem!_pos,word,← getElem!_pos,rowAt,← getElem!_pos]
        change (if _ then _ else outputByte state it.start.val b) = _
        rw [h _ lt b hb]
        simp [hn,pv,stateByte]
      · rw [outputByte,save,Array.set_val_eq,setOther _ _ _ _ (Ne.symm same)]
        change outputByte state j b = _
        rw [h j hj b hb]
        have equiv : j < nxt.start.val ↔ j < it.start.val := by omega
        simp [equiv]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val=active.val := by rw [he] at more; omega
      intro j hj b hb
      simpa [eq,hj] using h j hj b hb
  · simp

theorem read_spec (N : Usize) (s : Matrix machine.width) (active : Usize) (boundActive : active.val ≤ machine.width.val) (bound : N.val ≤ 136) (align : N.val%8=0) :
    read_active N s active ⦃ out => ∀ j < active.val, ∀ b < N.val,
      outputByte out j b = stateByte s j (b/8) (b%8) ⦄ := by
  unfold read_active
  step as ⟨last,count⟩
  unfold read_active_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array (Array U8 N) machine.width => last.val-q.1.start.val)
    (inv := fun q => q.1.end=last ∧ q.1.start.val ≤ last.val ∧
      ∀ j < active.val, ∀ b < 8*q.1.start.val, outputByte q.2 j b = stateByte s j (b/8) (b%8))
  · rintro ⟨it,values⟩ ⟨he,hi,h⟩
    simp only at he hi h
    unfold read_active_loop0.body
    by_cases more : it.start.val < it.end.val
    · have lt : it.start.val < last.val := he ▸ more
      step with core.iter.range.IteratorRange.next_Usize_some_spec it more as ⟨o,nxt,ho,hn,hen⟩
      simp only [ho]
      step with read_row s it.start values active boundActive (by omega) (by omega) as ⟨st,write⟩
      refine ⟨hen.trans he,by omega,?_,by omega⟩
      intro j hj b hb
      rw [write j hj b (by omega)]
      by_cases new : 8*it.start.val ≤ b
      · have div : b/8=it.start.val := by omega
        have rem : b%8=b-8*it.start.val := by omega
        simp [new,show b < 8*it.start.val+8 by omega,div,rem]
      · simp only [new,false_and,ite_false]
        exact h j hj b (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.start.val = N.val/8 := by rw [he] at more; omega
      intro j hj b hb
      exact h j hj b (by omega)
  · simp

theorem read_digest (N : Usize) (s : Matrix machine.width) (active : Usize) (boundActive : active.val ≤ machine.width.val) (bound : N.val ≤ 136) (align : N.val%8=0) :
    read_active N s active ⦃ out => ∀ j < active.val,
      bytes out.val[j]!.val = Spec.Keccak.squeeze (ShakeBatch.lane s j) 0 N.val ⦄ := by
  apply WP.spec_mono (read_spec N s active boundActive bound align)
  intro out cells j hj
  rw [Spec.Keccak.squeeze_short _ _ _ (by omega)]
  apply List.ext_getElem
  · simp [bytes]
  · intro b hl hr
    have bn : b < N.val := by simpa [bytes] using hl
    have ks : b/8 < 25 := by omega
    simp only [bytes,List.getElem_map,List.getElem_range,Nat.zero_add]
    rw [← getElem!_pos]
    change (outputByte out j b).bv = _
    rw [cells j hj b bn,stateByte,le_byte _ _ (by omega)]
    simp only [Spec.Keccak.extractByte,ShakeBatch.lane,Spec.Keccak.ofFnAt _ _ ks,cell]
end slhdsa.NativeVerify.ActiveHash
