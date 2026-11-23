import Armplatform.Parents
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformFors
open PlatformParent.Driver
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

def path (target : Target) {N} (sig : Slice U8) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (adrs : address.Adrs) (a : U32) (k : Usize) (idx : Array U32 35#usize)
    (vals : Array (Array U8 N) 35#usize) (h : U32) (i : Usize) := do
  if i ≠ 0#usize then fors.fors_pk_from_sig_loop2_loop2 sig pk st st5 adrs a k idx vals h i
  else
    let height ← h+1#u32
    let adr ← address.Adrs.with_word2 adrs height
    let (s,back) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice (Array U8 N))) vals ⟨k⟩
    let (indices,restore) ← lift (Array.to_slice_mut idx)
    let (n,out,ix) ← pathParents target st5 adr s indices sig
      (UScalar.cast .Usize a) (UScalar.cast .Usize h)
    fors.fors_pk_from_sig_loop2_loop2 sig pk st st5 adrs a k (restore ix) (back out) h n

theorem path_spec (target : Target) {N : Usize} (p : params.Params) (hp : PN p N)
    (sig : Slice U8) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk ({ pk_seed := pk, state := st, state512 := st5 } : hash.Seed N))
    (adrs : address.Adrs) (k : Usize) (hk : k.val = p.k.val)
    (vals0 : Array (Array U8 N) 35#usize) (idx0 : Array U32 35#usize)
    (h : U32) (hh : h.val < p.a.val) (hsig : sig.length = p.k.val * (1 + p.a.val) * N.val)
    (idx : Array U32 35#usize) (vals : Array (Array U8 N) 35#usize) (i : Usize) (hi : i.val ≤ k.val)
    (hdone : ∀ t, t < i.val →
      bytes (vals.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
        { adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }
        (pairMsg (bytes (vals0.val[t]!).val)
          (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
      (idx.val[t]!).val = (idx0.val[t]!).val / 2)
    (hrest : ∀ t, i.val ≤ t → vals.val[t]! = vals0.val[t]! ∧ idx.val[t]! = idx0.val[t]!) :
    path target sig pk st st5 adrs p.a k idx vals h i ⦃ r =>
      ∀ t, t < k.val →
        bytes (r.2.val[t]!).val = Spec.H (paramsS p) (bytes pk.val)
          { adrsS adrs with word2 := h.val + 1, word3 := (idx0.val[t]!).val / 2 }
          (pairMsg (bytes (vals0.val[t]!).val)
            (Spec.block (paramsS p) (bytes sig.val) (t * (p.a.val + 1) + 1 + h.val)) (idx0.val[t]!).val) ∧
        (r.1.val[t]!).val = (idx0.val[t]!).val / 2 ⦄ := by
  unfold path
  split
  · exact fors_pk_from_sig_loop2_loop2_spec p hp sig pk st st5 hs adrs k hk vals0 idx0 h hh hsig
      idx vals i hi hdone hrest
  · rename_i start
    have zero : i=0#usize := by exact Classical.byContradiction start
    subst i
    have valsEq : vals=vals0 := by
      apply Aeneas.Std.Array.ext
      apply List.ext_getElem (by simp)
      intro t h h'
      rw [← getElem!_eq _ _ h,← getElem!_eq _ _ h']
      exact (hrest t (by simp)).1
    have idxEq : idx=idx0 := by
      apply Aeneas.Std.Array.ext
      apply List.ext_getElem (by simp)
      intro t h h'
      rw [← getElem!_eq _ _ h,← getElem!_eq _ _ h']
      exact (hrest t (by simp)).2
    subst vals0
    subst idx0
    have ha : p.a.val≤14 := hp.valid.a_le
    have hk35 : k.val≤35 := hk ▸ hp.valid.k_le
    have acast : (UScalar.cast .Usize p.a).val=p.a.val := by scalar_tac
    have hcast : (UScalar.cast .Usize h).val=h.val := by scalar_tac
    step as ⟨height,hval⟩
    simp only [address.Adrs.with_word2,bind_tc_eq,bind_ok]
    apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice vals ⟨k⟩ (by scalar_tac))
    rintro ⟨active,back⟩ ⟨sliced,len,restore⟩
    change active.length=k.val at len
    have bounds : SigBounds N.val (UScalar.cast .Usize p.a).val (UScalar.cast .Usize h).val active.length sig := by
      intro t ht
      rw [acast,hcast]
      have endPos := fors_sib_bound p.a.val p.k.val N.val t h.val sig.length (by omega) hh hsig
      unfold siblingStart
      simpa only [Nat.add_one_mul,Nat.mul_comm N.val] using endPos
    try simp only [lift,Array.to_slice_mut,bind_tc_eq,bind_ok]
    apply WP.spec_bind (path_prefix target p hp pk st st5 hs {adrs with word2 := height} active idx.to_slice sig _ _ (by rw [len]; simpa)
      (by scalar_tac) bounds)
    rintro ⟨n,out,ix⟩ ⟨used,post⟩
    obtain ⟨⟨ixlen,indexAt⟩,outlen,atNode⟩ := post
    have readIdx : (Array.from_slice idx ix).val=ix.val :=
      Array.from_slice_val _ _ (by simpa [Slice.length] using ixlen)
    have getActive (t) (ht : t<k.val) : active.val[t]! = vals.val[t]! := by
      rw [sliced]
      exact slice0_getElem! _ _ _ ht (by simp; omega)
    have getOut (t) (ht : t<k.val) : (back out).val[t]! = out.val[t]! := by
      rw [restore,List.getElem!_setSlice!_middle _ _ _ _ ⟨by omega,by change t-0<out.length; omega,by simp; omega⟩]
      rfl
    apply fors_pk_from_sig_loop2_loop2_spec p hp sig pk st st5 hs adrs k hk vals idx h hh hsig (Array.from_slice idx ix) (back out) n (by omega)
    · intro t ht
      have kt : t<k.val := by omega
      have pos := indexAt t (by simp; omega)
      simp only [Array.val_to_slice,Nat.zero_add,Nat.zero_le,true_and,if_pos ht] at pos
      have updated : (nextIndex idx.val[t]!).val=idx.val[t]!.val/2 := by
        change ((idx.val[t]!).bv >>> 1).toNat = (idx.val[t]!).bv.toNat/2
        rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      have row := atNode t (by omega)
      simp only [if_pos ht] at row
      refine ⟨?_,by rw [readIdx,pos,updated]⟩
      rw [getOut t kt]
      have msg : sibling sig N.val p.a.val h.val t = Spec.block (paramsS p) (bytes sig.val) (t*(p.a.val+1)+1+h.val) := by
        unfold Spec.block
        rw [hp.n]
        simp [sibling,siblingStart,bytes,List.slice,List.map_take,List.map_drop,Nat.mul_comm N.val]
      simpa only [nodeBytes,pathParent,pathAddress,treeAddress,adrsS,pathData,Array.val_to_slice,
        getActive t kt,hval,acast,hcast,msg,updated,pairMsg] using row
    · intro t ht
      by_cases valid : t<35
      · have pos := indexAt t (by simpa)
        simp only [Array.val_to_slice,Nat.zero_add,Nat.zero_le,true_and,if_neg (by omega : ¬ t<n.val)] at pos
        refine ⟨?_,by rw [readIdx,pos]⟩
        by_cases kt : t<k.val
        · have row := atNode t (by omega)
          rw [if_neg (by omega),getActive t kt] at row
          rw [getOut t kt,row]
        · rw [restore,List.getElem!_setSlice!_suffix _ _ _ _ (by change 0+out.length≤t; omega)]
      · constructor <;> rw [getElem!_neg _ _ (by simp; omega),getElem!_neg _ _ (by simp; omega)]
end slhdsa.PlatformFors
