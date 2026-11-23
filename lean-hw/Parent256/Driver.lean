import Parent256.Destination
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.X86.Parent
open TreeRust.sha256.x86.avx512
open Spec.SHA256

def expected (p : Spec.Params) (pk : Spec.Bytes) (A : Spec.Adrs) (first : U32) (rows : Rows) (i : Nat) :=
  Spec.H p pk {A with word3 := first.val+i} (children rows i)

theorem batches_spec (p : Spec.Params) (pk : Spec.Bytes) (A : Spec.Adrs)
    (base : Array Reg 16#usize) (iv pre : Array Reg 8#usize) (stride : Reg)
    (first : U32) (rows : Rows) (count : Usize)
    (family : p.family = .sha2) (width : p.n = 16) (hpk : pk.length = 16)
    (hw : ∀ k, k < 16 → ∀ j, base.val[k]! j = word (template A) (4*k))
    (seed : ∀ j, stateWords (laneState iv j) = seedState 16 pk)
    (hp : Trace pre (fun _ => schedule (template A)) (laneState iv) 4)
    (hs : Digest.Stride stride 32) (bound : 2*count.val ≤ rows.length)
    (indices : first.val+count.val ≤ 2^32) (size : 32*count.val ≤ Usize.max) :
    fors_parents_loop1 ⟨⟨0#usize,count⟩,16#usize⟩ first rows count base iv pre
      (fun j => BitVec.ofNat 32 j.val) stride Store.control
      ⦃ r => Processed (expected p pk A first rows) rows r count.val ⦄ := by
  unfold fors_parents_loop1
  apply loop.spec_decr_nat (measure := fun q : Leaf.Iter × Rows => count.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end = count ∧ q.1.step_by = 16#usize ∧ q.1.iter.start.val ≤ count.val ∧
      Processed (expected p pk A first rows) rows q.2 q.1.iter.start.val)
  · rintro ⟨it,buf⟩ ⟨he,hstep,hle,hproc⟩
    simp only at he hstep hle hproc
    have hlen := hproc.1
    unfold fors_parents_loop1.body
    by_cases hlt : it.iter.start.val < it.iter.end.val
    · have lt : it.iter.start.val < count.val := he ▸ hlt
      step with Leaf.next it hlt hstep as ⟨o,next,ho,hnxt,hend,hs'⟩
      simp only [ho,lift,bind_ok,_root_.core.core_arch.x86.avx512f._mm512_set1_epi32,
        _root_.core.core_arch.x86.avx512f._mm512_add_epi32]
      step as ⟨diff,hdiff⟩
      step as ⟨shift,hshift⟩
      step as ⟨mask,hmask⟩
      step as ⟨pos,hpos⟩
      let idx : Reg := fun j => BitVec.ofNat 32 j.val + pos.bv
      conv => lhs; equals (finishBatch base iv pre idx buf stride it.iter.start count mask >>= fun r =>
        ok (cont (next,r))) =>
          unfold finishBatch prepare destination
          simp only [idx,bind_tc_eq,Std.bind_assoc,bind_ok,lift,UScalar.hcast_bv_eq,BitVec.setWidth_eq]
          rfl
      obtain ⟨⟨dst,back⟩,eq,hd,hb⟩ := spec_imp_exists (destination_spec buf it.iter.start count hle (by omega) (by omega))
      rw [finish_eq _ _ _ _ _ _ _ _ _ _ _ eq]
      simp only [bind_tc_eq,Std.bind_assoc,bind_ok]
      have advanceTo : next.iter.start.val = it.iter.start.val+dst.length := by rw [hnxt,he]; omega
      have dlen : dst.length ≤ 16 := by omega
      have maskOK : Digest.Mask mask dst.length := by
        intro j
        unfold Digest.active
        have hb : mask.bv = core.num.U16.MAX.bv >>> shift.val := by assumption
        rw [hb,hshift]
        have d : (core.cmp.impls.OrdUsize.min diff 16#usize).val = dst.length := by
          rw [show (core.cmp.impls.OrdUsize.min diff 16#usize).val = min diff.val 16 by simp,hdiff,hd]
        rw [d]
        exact Digest.mask_ok ⟨dst.length,by omega⟩ j
      step with hash_batch_spec p pk A base iv pre idx stride buf dst it.iter.start mask family width hpk hw seed hp
        maskOK hs (by omega) dlen (by omega) (by omega) as ⟨r,lr,hash⟩
      refine ⟨hend.trans he,hs'.trans hstep,by omega,?_,by omega⟩
      rw [advanceTo,← lr]
      apply advance _ _ _ _ _ _ hproc (by omega) (hb r)
      intro k hk
      let j : Fin 16 := ⟨k,by omega⟩
      have h := hash j (by change k < dst.length; omega)
      have posval : pos.val = first.val+it.iter.start.val := by
        rw [hpos,UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change it.iter.start.val < 2^32; omega)]
      have ix : (idx j).toNat = first.val+(it.iter.start.val+k) := by
        change (BitVec.ofNat 32 k + pos.bv).toNat = _
        rw [show pos.bv = BitVec.ofNat 32 pos.val by simp,← BitVec.ofNat_add,BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega),posval]; omega
      rw [ix,children_intact _ _ _ _ _ hproc (by omega) (by change 2*(it.iter.start.val+k)+1 < rows.length; omega)] at h
      exact h
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,next,ho,_⟩
      simp only [ho,step_simps]
      have eq : it.iter.start.val = count.val := by rw [he] at hlt; omega
      exact eq ▸ hproc
  · simp [Processed]

end slhdsa.X86.Parent
