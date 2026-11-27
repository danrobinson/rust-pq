import Cachepath.NativeShakeWots.SignInitWords
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots.Signer
open ShakeBatch NativeVerify NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option maxHeartbeats 1500000
set_option linter.concreteInstances false
variable [machine : Machine] [accel : Dispatch machine]

def secretAt {N : Usize} (p : params.Params) (sk seed : Array U8 N) (prf : address.Adrs) (id : Nat) :=
  Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val) {adrsS prf with word2:=id,word3:=0}

theorem prepare_secrets {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (digits : Slice U32) (prf : address.Adrs) (len n : Usize) (eqLen : digits.length=len.val)
    (size : len.val≤67) (count : n.val=N.val/8) (sw skw ap : Array U64 4#usize)
    (w2p : Array U64 machine.width) (s : Matrix machine.width) (sig : Signature) (table : Secrets)
    (sigLen : sig.length=digits.length*N.val) (positive : 0<machine.width.val)
    (swOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k) (skOk : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k)
    (prfOk : ∀ k<4, ap.val[k]!.bv=addressWord prf k)
    (tagP : ∀ l<machine.width.val, w2p.val[l]!.bv=addressWord prf 2)
    (permutes : ActiveCorrect machine accel.permute) :
    sign_loop0 N machine.width ⟨⟨0#usize,len⟩,machine.width⟩ digits len n sw skw ap w2p sig table s ⦃ out =>
      Prepared N digits (secretAt p sk seed prf) len.val out.1 out.2.1 ⦄ := by
  unfold sign_loop0
  apply loop.spec_decr_nat
    (measure := fun q : (core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)) × Signature × Secrets × Matrix machine.width =>
      len.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end=len ∧ q.1.step_by=machine.width ∧
      Prepared N digits (secretAt p sk seed prf) (min q.1.iter.start.val len.val) q.2.1 q.2.2.1)
  · rintro ⟨it,signature,tab,st⟩ ⟨stop,stride,old⟩
    simp only at stop stride old
    unfold sign_loop0.body
    by_cases live : it.iter.start.val < it.iter.end.val
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_spec it (by scalar_tac) as ⟨o,nxt,info,he,hw⟩
      simp only [live,ite_true] at info
      obtain ⟨ho,hn⟩ := info
      simp only [ho,bind_ok]
      let pos := it.iter.start
      have valid : pos.val<len.val := by rw [stop] at live; exact live
      step as ⟨left,sub⟩
      simp only [lift,bind_ok]
      let active := core.cmp.impls.OrdUsize.min left machine.width
      have cnt : active.val = min (len.val-pos.val) machine.width.val := by
        change (if machine.width < left then machine.width else left).val=_
        change (if machine.width < left then machine.width else left).val = min (len.val-it.iter.start.val) machine.width.val
        rw [← sub]
        split <;> rename_i h
        · exact (min_eq_right (Nat.le_of_lt h)).symm
        · exact (min_eq_left (Nat.le_of_not_gt h)).symm
      have good : 0<active.val := by omega
      have fits : pos.val+active.val≤67 := by omega
      let ident := fun l : Nat => U32.ofNatCore ((pos.val+l) % (2^32)) (by apply Nat.mod_lt; decide)
      have identVal (l : Nat) (hl : l<active.val) : (ident l).val=pos.val+l := by
        simp only [ident,U32.ofNatCore_val_eq,Nat.mod_eq_of_lt (show pos.val+l < 2^32 by omega)]
      have idGen := chunk_ids N pos active good fits
      change core.array.from_fn machine.width (sign.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64 N)
        (pos,active) ⦃ _ ⦄ at idGen
      step with idGen as ⟨ids,indices⟩
      have idsOk : ∀ l<active.val, ids.val[l]!.bv=addressLow (ident l) := by
        intro l hl
        rw [indices l hl (by omega)]
        congr 1
        apply UScalar.eq_of_val_eq
        simp only [U32.ofNatCore_val_eq,identVal l hl];rfl
      step as ⟨w0,v0⟩
      step as ⟨w1,v1⟩
      have prfHash := prf_lanes p hp sk seed prf sw skw w0 w1 w2p ids st active ident (by omega) swOk skOk
        (by rw [v0,← getElem!_pos];exact prfOk 0 (by decide)) (by rw [v1,← getElem!_pos];exact prfOk 1 (by decide))
        (fun l hl=>tagP l (by omega)) idsOk permutes
      obtain ⟨packed,packEq,_⟩ := spec_imp_exists (fill_layout N st sw skw w0 w1 w2p ids hp.le32)
      obtain ⟨hashed,hashEq,hashedRows⟩ := spec_imp_exists prfHash
      simp only [packEq,bind_ok] at hashEq
      rw [packEq,bind_ok,hashEq]
      simp only [bind_ok]
      have rows (l : Nat) (hl : l<active.val) : digest N hashed l=secretAt p sk seed prf (pos.val+l) := by
        simpa only [secretAt,identVal l hl] using hashedRows l hl
      let* ⟨outSig,outTable,scattered⟩ ← scatter_chunk N digits (secretAt p sk seed prf) n active pos hashed signature tab
        count (aligned_hash hp) hp.le32 (by omega) (by omega) (by omega) rows
        (by simpa only [min_eq_left (le_of_lt valid),pos] using old)
      have advance : nxt.iter.start.val=min (pos.val+machine.width.val) len.val := by rw [hn,stride,stop]
      refine ⟨he.trans stop,hw.trans stride,?_,by dsimp [pos] at advance valid;omega⟩
      simpa only [show min nxt.iter.start.val len.val=pos.val+active.val by omega] using scattered
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      simpa only [min_eq_right (show len.val ≤ it.iter.start.val by rw [stop] at live;omega)] using old
  · exact ⟨rfl,rfl,sigLen,by simp⟩

end slhdsa.NativeShakeWots.Signer
