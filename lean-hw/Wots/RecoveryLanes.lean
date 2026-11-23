import Wots.RecoveryAddress
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Wots
open Spec.SHA256

def chainIndex (ix : LaneArray) (j : Fin 16) := ix.val[j.val]!.bv.toNat

def laneStateOK (P : Spec.Params) (N : Usize) (pk : Spec.Bytes) (a : Spec.Adrs)
    (sig : Slice U8) (digits : Slice U32) (ix : LaneArray) (mask : U16) (c : Reg) (h : Hash) (w : Words) :=
  ∀ j, let i := chainIndex ix j
    i < 67 ∧ addressReady w j N.val a i ∧ (enabled mask j = true →
      i < digits.length ∧ digits.val[i]!.val ≤ (c j).toNat ∧ (c j).toNat < 15 ∧
        laneValue h j N.val = chainAt P N pk a sig digits i (c j).toNat)

private theorem unchanged_lane {digits order ix st active pos ix' st' mask next assigned}
    (fill : mapped digits order ix st active pos (ix',st',mask,next,assigned))
    (j : Fin 16) (off : enabled assigned j = false) :
    chainIndex ix' j = chainIndex ix j ∧ enabled mask j = enabled active j := by
  obtain ⟨job,_,_,lanes⟩ := fill
  have hj := lanes j
  cases e : job j with
  | none => rw [e] at hj; exact ⟨congrArg (fun (v : I32) => v.bv.toNat) hj.2.2.1,hj.2.1⟩
  | some q => rw [e] at hj; have := hj.2.2.2.1; simp_all

theorem no_load_lanes {P N pk a sig digits ix st active pos ix' st' mask next c h w order}
    (fill : mapped digits order ix st active pos (ix',st',mask,next,0#u16))
    (before : laneStateOK P N pk a sig digits ix active c h w) :
    laneStateOK P N pk a sig digits ix' mask c h w := by
  intro j
  obtain ⟨key,on⟩ := unchanged_lane fill j (by simp [enabled])
  simpa only [key,on] using before j

theorem load_chains {P N pk a sig digits ix st active pos ix' st' mask next assigned order}
    (c src : Reg) (h : Hash) (w : Words)
    (fill : mapped digits order ix st active pos (ix',st',mask,next,assigned))
    (before : laneStateOK P N pk a sig digits ix active c h w)
    (key : a.keypair < 2^32) (shape : N.val = 16 ∨ N.val = 24 ∨ N.val = 32)
    (queued : ∀ q < next.val, order.val[q]!.val < digits.length ∧ digits.val[order.val[q]!.val]!.val < 15)
    (nonzero : assigned ≠ 0#u16) (small : digits.length ≤ 67) (available : N.val*digits.length ≤ sig.length) :
    loadAssigned N ix' st' c src assigned sig h w Store.control ⦃ _ loaded hash patched =>
      laneStateOK P N pk a sig digits ix' mask loaded hash patched ⦄ := by
  have index (j) (on : enabled assigned j = true) :=
    assigned_index fill small (fun q hq => (queued q hq).1) j on
  have valid (j) (on : enabled assigned j = true) := (index j on).choose_spec.2.2.2.1
  have nz : assigned.bv ≠ 0 := by
    intro eq; apply nonzero; apply UScalar.eq_of_val_eq; exact congrArg BitVec.toNat eq
  let first : Fin 16 := ⟨_,BitVec.ctz_lt_iff_ne_zero.mpr nz⟩
  have positive := valid first (BitVec.getLsbD_true_ctz_of_ne_zero nz)
  apply WP.spec_mono (load_assigned_spec N ix' st' c src assigned sig h w digits.length shape (by omega)
    small available valid)
  rintro ⟨idx,loaded,hash,patched⟩ ⟨indices,count,hashes,patch⟩ j
  obtain ⟨oldBound,oldAddr,oldValue⟩ := before j
  have bound : chainIndex ix' j < 67 := by
    cases e : enabled assigned j with
    | true => exact lt_of_lt_of_le (valid j e) small
    | false => rw [(unchanged_lane fill j e).1]; exact oldBound
  refine ⟨bound,address_after_refill w patched j N.val a _ _ shape key oldBound bound oldAddr ?_,?_⟩
  · intro k hk
    rw [patch k hk j,indices,chainIndex,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  · intro on
    cases e : enabled assigned j with
    | true =>
      obtain ⟨q,_,hq,idxq,ok,digit⟩ := index j e
      have counter : (loaded j).toNat = digits.val[chainIndex ix' j]!.val := by
        simp only [count j,e,ite_true,digit,chainIndex,idxq]; rfl
      rw [counter]
      refine ⟨ok,le_rfl,by change digits.val[ix'.val[j.val]!.bv.toNat]!.val < 15; rw [idxq]; exact (queued q hq).2,?_⟩
      apply loaded_chain P N pk a sig digits _ hash j shape available ok
      intro k hk
      rw [hashes k (by omega) j,if_pos ⟨hk,e⟩]
    | false =>
      obtain ⟨same,on'⟩ := unchanged_lane fill j e
      obtain ⟨ok,lo,hi,value⟩ := oldValue (on'.symm.trans on)
      have sameWords : stateWords (laneState hash j) = stateWords (laneState h j) := by
        simp (disch := decide) only [stateWords,laneState,hashes, e,Bool.false_eq_true,and_false,ite_false]
      simpa only [count j,e,Bool.false_eq_true,ite_false,same,laneValue,sameWords] using And.intro ok (And.intro lo (And.intro hi value))

end slhdsa.X86.Wots
