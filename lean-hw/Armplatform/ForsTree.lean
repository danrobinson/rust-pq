import Armplatform.Parents
open Aeneas Aeneas.Std Result
namespace slhdsa.PlatformFors
open PlatformParent.Driver
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

/-- The accelerated prefix followed by the scalar tail of a FORS reduction. The
original caller always starts at zero. Nonzero starts provide the scalar loop's
existing induction interface for proof specialization. -/
def tree (target : Target) {N} (i z : U32) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32) (vals : Array (Array U8 N) 128#usize)
    (lvl : U32) (cnt j : Usize) := do
  if j ≠ 0#usize then
    fors.fors_batch_loop3_loop2 i z pk st st5 i1 i2 i3 i4 i5 i6 vals lvl cnt j
  else
    let a ← address.Adrs.with_word2 ⟨i1,i2,i3,i4,i5,i6⟩ lvl
    let shift ← z-lvl
    let first ← i <<< shift
    let (s,back) ← lift (Array.to_slice_mut vals)
    let (offset,written) ← parents target st5 a first s cnt
    fors.fors_batch_loop3_loop2 i z pk st st5 i1 i2 i3 i4 i5 i6 (back written) lvl cnt offset

theorem tree_spec (target : Target) {N : Usize} (p : params.Params) (hp : PN p N)
    (i z : U32) (pk : Array U8 N) (st : Array U32 8#usize) (st5 : Array U64 8#usize)
    (hs : SeedOk ({ pk_seed := pk, state := st, state512 := st5 } : hash.Seed N))
    (i1 : U32) (i2 : U64) (i3 i4 i5 i6 : U32)
    (A0 : address.Adrs) (hA0 : A0 = ⟨i1, i2, i3, i4, i5, i6⟩)
    (vals0 : Array (Array U8 N) 128#usize) (lvl : U32) (cnt : Usize)
    (hlvl : 1 ≤ lvl.val) (hlz : lvl.val ≤ z.val) (hz : z.val ≤ 7)
    (hcnt : cnt.val = 2 ^ (z.val - lvl.val)) (hi : (i.val + 1) * 2 ^ z.val < 2 ^ 32)
    (vals : Array (Array U8 N) 128#usize) (j : Usize) (hj : j.val ≤ cnt.val)
    (hdone : ∀ k, k < j.val → bytes (vals.val[k]!).val =
      Spec.H (paramsS p) (bytes pk.val)
        { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }
        (bytes (vals0.val[2 * k]!).val ++ bytes (vals0.val[2 * k + 1]!).val))
    (hrest : ∀ k, j.val ≤ k → vals.val[k]! = vals0.val[k]!) :
    tree target i z pk st st5 i1 i2 i3 i4 i5 i6 vals lvl cnt j ⦃ r =>
      ∀ k, k < cnt.val → bytes (r.val[k]!).val =
        Spec.H (paramsS p) (bytes pk.val)
          { adrsS A0 with word2 := lvl.val, word3 := i.val * 2 ^ (z.val - lvl.val) + k }
          (bytes (vals0.val[2 * k]!).val ++ bytes (vals0.val[2 * k + 1]!).val) ⦄ := by
  unfold tree
  split
  · exact fors_batch_loop3_loop2_spec p hp i z pk st st5 hs i1 i2 i3 i4 i5 i6 A0 hA0 vals0 lvl cnt
      hlvl hlz hz hcnt hi vals j hj hdone hrest
  · rename_i start
    have zero : j=0#usize := by exact Classical.byContradiction start
    subst j
    have eql : vals=vals0 := by
      apply Aeneas.Std.Array.ext
      apply List.ext_getElem (by simp)
      intro k h h'
      rw [← getElem!_eq _ _ h,← getElem!_eq _ _ h']
      exact hrest k (by simp)
    subst vals0
    have lim : 2^(z.val-lvl.val)≤2^z.val := Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    have room : i.val*2^(z.val-lvl.val)+cnt.val≤2^32 := by
      rw [hcnt,←Nat.add_one_mul]
      exact le_trans (Nat.mul_le_mul_left _ lim) (Nat.le_of_lt hi)
    have size : 2*cnt.val≤128 := by
      rw [hcnt,←pow_succ']
      exact Nat.pow_le_pow_right (by decide) (show z.val-lvl.val+1≤7 by omega)
    simp only [address.Adrs.with_word2,bind_tc_eq,bind_ok]
    step as ⟨shift,shiftVal⟩
    step as ⟨first,firstVal⟩
    have firstEq : first.val=i.val*2^(z.val-lvl.val) := by
      rw [firstVal,shiftVal,Nat.shiftLeft_eq,U32.size_eq,Nat.mod_eq_of_lt]
      have positive := Nat.two_pow_pos (z.val-lvl.val)
      omega
    simp only [lift,bind_tc_eq,bind_ok,Array.to_slice_mut]
    apply WP.spec_bind (parent_prefix target p hp pk st st5 hs ⟨i1,i2,i3,i4,lvl,i6⟩ first vals.to_slice cnt
      (by simpa using size) (by rwa [firstEq]))
    rintro ⟨offset,written⟩ ⟨used,valid⟩
    obtain ⟨length,post⟩ := valid
    have restore : (Array.from_slice vals written).val=written.val :=
      Array.from_slice_val _ _ (by simpa [Slice.length] using length)
    apply fors_batch_loop3_loop2_spec p hp i z pk st st5 hs i1 i2 i3 i4 i5 i6 A0 hA0 vals lvl cnt
      hlvl hlz hz hcnt hi _ _ used
    · intro k hk
      have row := post k (by simp; omega)
      rw [if_pos hk] at row
      rw [restore]
      simpa only [nodeBytes,parentAt,treeAddress,children,adrsS,firstEq,hA0,Array.val_to_slice] using row
    · intro k hk
      by_cases bounded : k<128
      · have row := post k (by simpa)
        rw [if_neg (by omega),Array.val_to_slice] at row
        simpa only [restore] using row
      · rw [getElem!_neg _ _ (by simp; omega),getElem!_neg _ _ (by simp; omega)]
end slhdsa.PlatformFors
