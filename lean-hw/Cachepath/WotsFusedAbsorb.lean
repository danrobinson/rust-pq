import Cachepath.WotsFusedStream
import Shakebatch.WotsWords

open Aeneas Aeneas.Std Result slhdsa.ShakeBatch
namespace slhdsa.cache.builder.nativeShake.Vector.Fused
set_option linter.concreteInstances false
variable [machine : Machine]

def consume (count : Usize) (hashed pk : Matrix machine.width) (pos : Usize) :
    Result (Matrix machine.width × Usize) := do
  let rows ← core.array.Array.index (core.ops.index.IndexSlice
    (core.slice.index.SliceIndexRangeToUsizeSlice (Array U64 machine.width))) hashed ⟨count⟩
  let iter ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter rows
  generate_loop0_loop1 iter pk pos

theorem consume_spec {N : Usize} (p : params.Params) (hp : PN p N) (count : Usize) (length : count.val=N.val/8)
    (hashed pk : Matrix machine.width) (pos : Usize) (rate : pos.val < 17) (permutes : PermutationCorrect)
    (tip : Nat → Spec.Bytes)
    (expected : ∀ j<machine.width.val, Spec.Keccak.squeeze (ShakeBatch.lane hashed j) 0 N.val = tip j) :
    consume count hashed pk pos ⦃ out => out.2.val < 17 ∧ ∀ j<machine.width.val,
      (ShakeBatch.lane out.1 j,8*out.2.val) = (tip j).foldl Spec.Keccak.feed (ShakeBatch.lane pk j,8*pos.val) ⦄ := by
  have small := hp.le32
  have align := aligned_hash hp
  obtain ⟨values,digest,words⟩ := digest_words (N:=N) hashed (by omega) align
  unfold consume
  step as ⟨slice,data,len⟩
  simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,bind_ok]
  apply absorb_tip_rows slice pk pos rate permutes tip
  · intro j hj
    rw [← expected j hj,Spec.Keccak.squeeze_length]
    omega
  · intro j hj i hi
    have iw := words j hj i (by omega)
    rw [inputWord_eq,digest j hj,expected j hj] at iw
    rw [iw]
    unfold cell
    rw [data,Array.val_to_slice]
    simp only [List.slice,List.drop_zero]
    rw [List.getElem!_take_of_lt _ i _ (by omega)]

end slhdsa.cache.builder.nativeShake.Vector.Fused
