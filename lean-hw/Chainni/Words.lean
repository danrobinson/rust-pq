import Chainni.Funs
import Slhdsa.Proofs.ShaNi
import Slhdsa.Proofs.Hash
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel.Chain

theorem big_endian (w : BitVec 32) : w.toBEBytes = Spec.toByte w.toNat 4 := by
  apply List.ext_getElem
  · simp [Spec.toByte]
  · intro i hi _
    have bound : i < 4 := by simpa using hi
    simp only [BitVec.toBEBytes,List.getElem_reverse,Spec.toByte,List.getElem_map,List.getElem_range]
    have len : w.toLEBytes.length = 4 := by simp
    ext k hk
    have h := BitVec.toLEBytes_getElem_testBit w (4-1-i) k (by omega) ⟨hk,by omega⟩
    simp only [len]
    have modbit (x : Nat) : (x % 256).testBit k = x.testBit k := by
      change (x % 2^8).testBit k = _
      rw [Nat.testBit_mod_two_pow x 8 k]; simp [hk]
    simp only [BitVec.getElem_eq_testBit_toNat,BitVec.toNat_ofNat,modbit,Nat.testBit_shiftRight]
    exact h

theorem digest_bytes (ws : List Word) : bytes (serialize ws) = ser ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    simp only [serialize,List.flatMap_cons,bytes,List.map_append,List.map_map,ser] at *
    simpa [Function.comp_def,big_endian] using ih

/-- The input transform used before a two-lane SHA-NI compression step. -/
def withIndex (b : Spec.Bytes) (t : Nat) := b.take 18 ++ Spec.toByte t 4 ++ b.drop 22

abbrev Rows := Slice (Array U8 64#usize)

def setIndex (pair : Rows) (starts : Slice U32) (step : U32) (i : Usize) := do
  let (a,back) ← Slice.index_mut_usize pair i
  let (s,backA) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) a (⟨18#usize,22#usize⟩ : core.ops.range.Range Usize)
  let t ← Slice.index_usize starts i
  let index ← t + step
  let encoded ← lift (core.num.U32.to_be_bytes index)
  let src ← lift (Array.to_slice encoded)
  let dst ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back (backA dst))

theorem set_index_spec (pair : Rows) (starts : Slice U32) (step : U32) (i : Usize)
    (hi : i.val < pair.length) (hs : i.val < starts.length)
    (bound : starts.val[i.val]!.val+step.val ≤ U32.max) :
    setIndex pair starts step i ⦃ r => r.length = pair.length ∧
      (∀ j, j ≠ i.val → r.val[j]! = pair.val[j]!) ∧
      bytes r.val[i.val]!.val = withIndex (bytes pair.val[i.val]!.val) (starts.val[i.val]!.val+step.val) ⦄ := by
  unfold setIndex
  have safe : starts.val[i.val].val+step.val ≤ U32.max := by simpa only [getElem!_pos starts.val i.val hs] using bound
  step as ⟨ab,ha,hback⟩
  obtain ⟨a,back⟩ := ab
  step as ⟨sb,hsub,hslen,hba⟩
  obtain ⟨s,backA⟩ := sb
  simp only at ha hback hsub hslen hba
  simp only [lift,bind_tc_eq,bind_ok]
  step as ⟨t,ht⟩
  step as ⟨index,hindex⟩
  step as ⟨dst,hd⟩
  all_goals try (simp only [Slice.length] at *; omega)
  simp only [step_simps,hback,Slice.set_val_eq]
  refine ⟨by simp,fun j hj => Avx2.setOther _ _ _ _ (Ne.symm hj),?_⟩
  rw [Avx2.setSame _ _ _ hi,hd,hba,bytes_setSlice]
  · simp only [Array.val_to_slice,ha,← getElem!_pos,withIndex]
    have be : bytes (core.num.U32.to_be_bytes index).val = Spec.toByte index.val 4 := by
      simpa [core.num.U32.to_be_bytes,bytes] using big_endian index.bv
    rw [be,hindex,ht,← getElem!_pos]
    simp
  · simp

abbrev Digests := Array (Array U8 32#usize) 2#usize

def putDigest (N limit i : Usize) (hashes : Digests) (pair : Rows) := do
  let (a,back) ← Slice.index_mut_usize pair i
  let (s,backA) ← core.array.Array.index_mut (core.ops.index.IndexMutSlice
    (core.slice.index.SliceIndexRangeUsizeSlice U8)) a (⟨22#usize,limit⟩ : core.ops.range.Range Usize)
  let h ← Array.index_usize hashes i
  let src ← core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8)) h
    (⟨N⟩ : core.ops.range.RangeTo Usize)
  let dst ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s src
  ok (back (backA dst))

theorem put_digest_spec (N limit i : Usize) (hashes : Digests) (pair : Rows)
    (hn : N.val ≤ 32) (hl : limit.val = 22+N.val) (hi : i.val < pair.length) (lane : i.val < 2) :
    putDigest N limit i hashes pair ⦃ r => r.length = pair.length ∧
      (∀ j, j ≠ i.val → r.val[j]! = pair.val[j]!) ∧
      bytes r.val[i.val]!.val = (bytes pair.val[i.val]!.val).take 22 ++
        (bytes hashes.val[i.val]!.val).take N.val ++ (bytes pair.val[i.val]!.val).drop limit.val ⦄ := by
  unfold putDigest
  step as ⟨ab,ha,hback⟩
  obtain ⟨a,back⟩ := ab
  step as ⟨sb,hsub,hslen,hba⟩
  obtain ⟨s,backA⟩ := sb
  simp only at ha hback hsub hslen hba
  step as ⟨h,hh⟩
  step as ⟨src,hsrc,hls⟩
  step as ⟨dst,hd⟩
  all_goals try (simp only [Slice.length] at *; omega)
  simp only [step_simps,hback,Slice.set_val_eq]
  refine ⟨by simp,fun j hj => Avx2.setOther _ _ _ _ (Ne.symm hj),?_⟩
  rw [Avx2.setSame _ _ _ hi,hd,hba,bytes_setSlice _ _ _ (by scalar_tac)]
  simp only [ha,hh,hsrc,← getElem!_pos,Array.val_to_slice,List.slice,List.drop_zero,bytes,List.map_take]
  simp [hl,hn]

end slhdsa.Intel.Chain
