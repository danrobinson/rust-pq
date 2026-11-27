import Cachepath.NativeShakeWots.Chains
import Cachepath.WotsFusedPrf
import Cachepath.NativeShakeWots.KeyUtils
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.NativeShakeWots
open ShakeBatch NativeVerify NativeVerify.Wots cache.builder.nativeShake.Vector.Fused
set_option maxHeartbeats 1500000
set_option linter.concreteInstances false
variable [machine : Machine] [accel : Dispatch machine] [stream : Stream] [ok : StreamCorrect]

theorem key_chunks {N : Usize} (p : params.Params) (hp : PN p N) (sk seed : Array U8 N)
    (prf hash : address.Adrs) (len : Usize) (size : len.val≤67) (sw skw ap ah : Array U64 4#usize)
    (w2p w2h : Array U64 machine.width) (s : Matrix machine.width) (pk : stream.State) (domain : Spec.Bytes)
    (prior : ok.Absorbed pk domain) (positive : 0<machine.width.val)
    (swOk : ∀ k<N.val/8, sw.val[k]!.bv=inputWord seed.val k) (skOk : ∀ k<N.val/8, skw.val[k]!.bv=inputWord sk.val k)
    (prfOk : ∀ k<4, ap.val[k]!.bv=addressWord prf k) (hashOk : ∀ k<4, ah.val[k]!.bv=addressWord hash k)
    (tagP : ∀ l<machine.width.val, w2p.val[l]!.bv=addressWord prf 2)
    (tagH : ∀ l<machine.width.val, w2h.val[l]!.bv=addressWord hash 2)
    (permutes : ActiveCorrect machine accel.permute) :
    keygen_loop0 N machine.width ⟨⟨0#usize,len⟩,machine.width⟩ len sw skw ap ah w2p w2h s pk
      ⦃ out => ok.Absorbed out (domain ++ (List.range len.val).flatMap (tip p sk seed prf hash)) ⦄ := by
  let root := tip p sk seed prf hash
  unfold keygen_loop0
  apply loop.spec_decr_nat
    (measure := fun q : (core.iter.adapters.step_by.StepBy (core.ops.range.Range Usize)) × Matrix machine.width × stream.State =>
      len.val-q.1.iter.start.val)
    (inv := fun q => q.1.iter.end=len ∧ q.1.step_by=machine.width ∧
      ok.Absorbed q.2.2 (domain ++ (List.range (min q.1.iter.start.val len.val)).flatMap root))
  · rintro ⟨it,st,streamState⟩ ⟨stop,stride,old⟩
    simp only at stop stride old
    unfold keygen_loop0.body
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
      step with chunk_ids N pos active good fits as ⟨ids,indices⟩
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
      simp only [bind_ok,W_eq]
      step as ⟨last,bound⟩
      have finalStep : last=15#u32 := by scalar_tac
      rw [finalStep]
      let initial := fun l => Spec.PRF (Shake.params p) (bytes seed.val) (bytes sk.val) {adrsS prf with word2:=(ident l).val,word3:=0}
      step with chain_rounds p hp seed hash sw ah w2h ids active ident initial hashed (by omega) swOk hashOk
        (fun l hl => tagH l (by omega)) idsOk (by intro l hl;exact hashedRows l hl) permutes as ⟨ends,endRows⟩
      have rows (l : Nat) (hl : l<active.val) : digest N ends l=root (pos.val+l) := by
        rw [endRows l hl]
        have mod : (it.iter.start.val+l)%4294967296=pos.val+l := by
          change (pos.val+l)%4294967296=pos.val+l
          apply Nat.mod_eq_of_lt; omega
        simp [initial,root,tip,adrsS,identVal l hl,mod]
      step with absorb_chunk ends active streamState pos.val domain root (by simpa [min_eq_left (le_of_lt valid),pos] using old)
        rows hp.le32 (aligned_hash hp) (by omega) as ⟨out,added⟩
      have advance : nxt.iter.start.val=min (pos.val+machine.width.val) len.val := by rw [hn,stride,stop]
      refine ⟨he.trans stop,hw.trans stride,?_,by dsimp [pos] at advance valid;omega⟩
      simpa only [show min nxt.iter.start.val len.val=pos.val+active.val by omega] using added
    · step with core.iter.adapters.step_by.IteratorStepBy.next_Range_Usize_none_spec it (by omega) as ⟨o,_,ho,_⟩
      simp only [ho,step_simps]
      simpa [min_eq_right (show len.val ≤ it.iter.start.val by rw [stop] at live;omega),root] using old
  · simpa using prior

end slhdsa.NativeShakeWots
