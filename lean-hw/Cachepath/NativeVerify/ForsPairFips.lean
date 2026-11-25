import Cachepath.NativeVerify.ForsPairHash
import Shakebatch.Pair
import Shakebatch.WotsWords
import Shakebatch.ClimbStep

open Aeneas Aeneas.Std Result
namespace slhdsa.NativeVerify.Fors
open ShakeBatch cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
set_option maxHeartbeats 1600000
variable [machine : Machine]

private theorem padded_pair {N : Usize} (seed left right : Array U8 N) (a : address.Adrs)
    (n offset pad : Usize) (sw aw : Array U64 4#usize) (height parent : U32)
    (cap : n.val≤4) (size : n.val*8=N.val) (off : offset.val=n.val+4) (padEq : pad.val=offset.val+2*n.val)
    (seeds : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addr : ∀ k<4, aw.val[k]!.bv=addressWord a k) (k : Nat) :
    (let raw : BitVec 64 := if k=pad.val then 31 else if pad.val<k then 0 else
       if k=n.val+3 then addressLow height ||| wordTag parent else
       if k<n.val then sw.val[k]!.bv else if k<offset.val then aw.val[k-n.val]!.bv else
       if k<offset.val+n.val then inputWord left.val (k-offset.val) else inputWord right.val (k-(offset.val+n.val))
     if k=16 then raw ||| 0x8000000000000000 else raw) =
    Spec.Keccak.paddedWord (bytes seed.val ++ ((adrsS {a with word2:=height,word3:=parent}).bytes ++
      (bytes left.val ++ bytes right.val))) k := by
  rw [← pair_layout seed left right _ (by omega) (by omega)]
  unfold initialWord
  simp only [show 2*N.val/8+4=offset.val+n.val by omega,show N.val/8+4=offset.val by omega,
    show (3*N.val+32)/8=pad.val by omega,show N.val/8=n.val by omega]
  simp only [← off]
  by_cases within : n.val≤k ∧ k<offset.val
  · rw [packed_address a height parent (k-n.val) (by omega)]
    split_ifs <;> first | rfl | omega | exact addr _ (by omega)
  · split_ifs <;> first | rfl | omega | exact seeds _ (by omega) | decide

theorem parent_fips [accelerator : ActiveKernel machine] {N : Usize} (seed : Array U8 N)
    (a : address.Adrs) (sig : Slice U8) (n offset pad stride first active : Usize)
    (sw aw : Array U64 4#usize) (lvl : U32) (s : Matrix machine.width) (ix : Array U32 machine.width)
    (small : n.val≤4) (size : n.val*8=N.val) (off : offset.val=n.val+4) (padEq : pad.val=offset.val+2*n.val)
    (live : active.val≤machine.width.val) (depth : lvl.val+2≤stride.val) (heightBound : lvl.val<32)
    (fit : (first.val+active.val)*stride.val*N.val≤sig.length) (pos : 0<N.val)
    (seeds : ∀ k<n.val, sw.val[k]!.bv=inputWord seed.val k)
    (addr : ∀ k<4, aw.val[k]!.bv=addressWord a k)
    (permutes : ActiveCorrect machine accelerator.run) :
    hashParents N 0x8000000000000000#u64 sig n offset pad stride sw aw first active lvl s ix ⦃ out updated =>
      ∀ l<active.val, let idx := ix.val[l]!
        let block := (first.val+l)*stride.val+lvl.val+1
        updated.val[l]!.val=idx.val/2 ∧ Spec.Keccak.squeeze (ShakeBatch.lane out l) 0 N.val =
          Spec.shake256 (bytes seed.val ++ ({adrsS a with word2:=lvl.val+1,word3:=idx.val/2}.bytes ++
          pairMsg (Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val)
            (bytes ((sig.val.drop (block*N.val)).take N.val)) idx.val)) N.val ⦄ := by
  apply WP.spec_mono (parent_layout N sig n offset pad stride first active sw aw lvl s ix small size off padEq live depth heightBound fit pos permutes)
  rintro ⟨out,updated⟩ ⟨changed,before,height,heightEq,hash,layout⟩ l hl
  dsimp only
  let idx := ix.val[l]!
  let parent : U32 := ⟨idx.bv >>> 1⟩
  have par : parent.val=idx.val/2 := by
    change (idx.bv >>> 1).toNat=idx.val/2
    rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow];rfl
  refine ⟨by rw [changed l hl]; exact par,?_⟩
  let block := (first.val+l)*stride.val+lvl.val+1
  have bounds := Nat.mul_le_mul_right stride.val (show first.val+l+1≤first.val+active.val by omega)
  rw [Nat.add_mul,one_mul] at bounds
  have bfit := (Nat.mul_le_mul_right N.val (show block+1≤(first.val+active.val)*stride.val by dsimp [block];omega)).trans fit
  rw [Nat.add_mul,one_mul] at bfit
  let sibling : Array U8 N := Array.from ((sig.val.drop (block*N.val)).take N.val) (by simp [Slice.length] at bfit;simp;omega)
  have sib : sibling.val=(sig.val.drop (block*N.val)).take N.val := Array.from_val _ _
  obtain ⟨bytesOut,recovered,words⟩ := digest_words (N:=N) s (by omega) (by omega)
  let value := bytesOut.val[l]!
  have vbytes : bytes value.val=Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val := recovered l (by omega)
  let lhs := if idx.val%2=0 then value else sibling
  let rhs := if idx.val%2=0 then sibling else value
  have addressEq : adrsS {a with word2:=height,word3:=parent}={adrsS a with word2:=lvl.val+1,word3:=idx.val/2} := by
    simp only [adrsS,heightEq,par]
  have order : pairMsg (Spec.Keccak.squeeze (ShakeBatch.lane s l) 0 N.val)
      (bytes ((sig.val.drop (block*N.val)).take N.val)) idx.val = bytes lhs.val ++ bytes rhs.val := by
    rw [← vbytes,← sib]
    by_cases h : idx.val%2=0 <;> simp [lhs,rhs,pairMsg,h]
  change _ = Spec.shake256 (bytes seed.val ++ (_ ++ pairMsg _ (bytes ((sig.val.drop (block*N.val)).take N.val)) idx.val)) _
  rw [order,← addressEq,hash l hl,Spec.shake256,Spec.Keccak.padded_fips _ (by simp [address_length];omega) (by simp [address_length];omega)]
  apply congrArg (fun st => Spec.Keccak.squeeze (Spec.Keccak.permute st) 0 N.val)
  apply Spec.Keccak.ext25 _ _ (by simp [ShakeBatch.lane]) (by simp [Spec.Keccak.padded])
  intro k hk
  simp only [ShakeBatch.lane,Spec.Keccak.padded,Spec.Keccak.ofFnAt _ _ hk,layout k hk l hl]
  rw [← padded_pair seed lhs rhs a n offset pad sw aw height parent small size off padEq seeds addr k]
  have w (j : Nat) (hj : j<n.val) : cell s j l=inputWord value.val j := (words l (by omega) j (by omega)).symm
  have sibWords : blockWords sig N.val block = inputWord sibling.val := by rw [sib];rfl
  change parentInput sw aw s idx _ _ _ height sig _ block _ _ = _
  simp only [parentInput,sibWords]
  by_cases even : idx.val%2=0 <;> simp only [even,lhs,rhs,ite_true,ite_false]
  all_goals split_ifs <;> first | rfl | omega | apply w <;> omega | (congr 1; exact w _ (by omega))

end slhdsa.NativeVerify.Fors
