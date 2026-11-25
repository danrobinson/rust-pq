import Buffered.SmallWotsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.Buffered.SmallWots
open ShakeBatch NativeVerify NativeVerify.Wots NativeShakeWots cache.builder.nativeShake.Vector.Fused
set_option maxHeartbeats 900000

def chainId (K idx : Usize) (l : Nat) : U32 := ⟨BitVec.ofNat 32 ((idx.val+l)/K.val)⟩

def keyAddr (a : address.Adrs) (typ first : U32) (K idx : Usize) (l : Nat) :=
  Fused.laneAddress a typ first.val ((idx.val+l)%K.val)

def Tagged (K idx : Usize) (first : U32) (a : address.Adrs) (n : Nat) (prf hash ids : Array U64 8#usize) :=
  ∀ l<n, prf.val[l]!.bv=addressWord (keyAddr a address.WOTS_PRF first K idx l) 2 ∧
    hash.val[l]!.bv=addressWord (keyAddr a address.WOTS_HASH first K idx l) 2 ∧
    ids.val[l]!.bv=addressLow (chainId K idx l)

private theorem natWord (u : U32) (x : Nat) (same : u.val=x) : (⟨BitVec.ofNat 32 x⟩ : U32)=u := by
  rw [←same];cases u;simp [UScalar.val,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem chain_tags (K idx active : Usize) (first : U32) (a : address.Adrs) (prf hash ids : Array U64 8#usize)
    (pos : 0<K.val) (keys : K.val≤8) (fit : first.val+K.val≤2^32) (cap : idx.val+active.val≤512)
    (live : active.val≤8) :
    leaves_loop2_loop0 K ⟨0#usize,active⟩ first idx prf hash ids ⦃ p h i => Tagged K idx first a active.val p h i ⦄ := by
  unfold leaves_loop2_loop0
  apply loop.spec_decr_nat (measure := fun q : core.ops.range.Range Usize × Array U64 8#usize × Array U64 8#usize × Array U64 8#usize => active.val-q.1.start.val)
    (inv := fun q => q.1.end=active ∧ q.1.start.val≤active.val ∧ Tagged K idx first a q.1.start.val q.2.1 q.2.2.1 q.2.2.2)
  · rintro ⟨it,p,h,i⟩ ⟨last,le,prior⟩
    simp only at last le prior ⊢
    unfold leaves_loop2_loop0.body
    by_cases more : it.start.val<active.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec it (by rw [last];exact more) as ⟨_,next,tag,inc,ends⟩
      simp only [tag]
      step as ⟨flat,fv⟩
      step as ⟨chain,cv⟩
      step as ⟨key,kv⟩
      simp only [lift,bind_ok]
      have rem : key.val<K.val := kv ▸ Nat.mod_lt _ pos
      have cast : (UScalar.cast .U32 key).val=key.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change _ < 2^32;omega)
      step as ⟨kp,kpv⟩
      simp only [ShakeBatch.core.num.U32.swap_bytes,lift,bind_ok]
      step as ⟨hi,_,w⟩
      step as ⟨newP,wp⟩
      step as ⟨hi2,_,w2⟩
      step as ⟨newH,wh⟩
      step as ⟨newI,wi⟩
      have eqK : (⟨BitVec.ofNat 32 (first.val+(idx.val+it.start.val)%K.val)⟩ : U32)=kp :=
        natWord _ _ (by rw [kpv,cast,kv,fv])
      have cq : chain.val≤flat.val := cv ▸ Nat.div_le_self _ _
      have eqC : chainId K idx it.start.val=UScalar.cast .U32 chain := natWord _ _
        (by rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by change _ < 2^32;omega),cv,fv])
      refine ⟨ends.trans last,by omega,?_ ,by omega⟩
      intro l ll
      rw [wp,wh,wi,Array.set_val_eq,Array.set_val_eq,Array.set_val_eq]
      by_cases same : l=it.start.val
      · subst l
        rw [setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega),setSame _ _ _ (by simp;omega)]
        simp only [keyAddr,Fused.address_tag,eqK,eqC]
        exact ⟨congrArg (fun z => addressLow address.WOTS_PRF ||| z) w,
          congrArg (fun z => addressLow address.WOTS_HASH ||| z) w2,rfl⟩
      · rw [setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same),setOther _ _ _ _ (Ne.symm same)]
        exact prior l (by omega)
    · step with core.iter.range.IteratorRange.next_Usize_none_spec it (by rw [last];omega) as ⟨_,_,tag,_⟩
      simp only [tag,step_simps]
      exact (show it.start.val=active.val by omega) ▸ prior
  · exact ⟨rfl,Nat.zero_le _,by intro l hl;change l<0 at hl;omega⟩
end slhdsa.Buffered.SmallWots
