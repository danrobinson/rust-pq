import Slhdsa.Proofs.Slh
open Aeneas Aeneas.Std Result
namespace slhdsa.SegmentedApi

theorem prefix_bytes {N : Usize} (random : Array U8 N) (ctx msg : Slice U8)
    (tag : U8) (tagVal : tag=UScalar.cast .U8 ctx.len) (n used : Nat)
    (nVal : n=N.val+2) (usedVal : used=n+ctx.length) (fits : used≤289) :
    let domain := [0#u8,tag]
    let raw := (((List.replicate 289 0#u8).setSlice! 0 random.val).setSlice! N.val domain).setSlice! n ctx.val
    bytes (raw.take used ++ msg.val) = bytes random.val ++ Spec.withContext (bytes msg.val) (bytes ctx.val) := by
  dsimp only
  rw [build3 random.val [0#u8,tag] ctx.val 0#u8 289 N.val n (by simp) (by simpa using nVal)
    (by simpa [Slice.length,nVal,usedVal] using fits)]
  have len : (random.val ++ [0#u8,tag] ++ ctx.val).length=used := by simp [usedVal,nVal,Slice.length]; omega
  rw [List.take_left' len]
  simp [Spec.withContext,Spec.toByte,List.range,List.range.loop,bytes,tagVal,List.append_assoc]
  apply BitVec.eq_of_toNat_eq
  simp

theorem finish_bytes {α : Type} (inner : List α) (zero high tag : α) (k : Nat)
    (len : inner.length=k+3) :
    (((inner ++ List.replicate (k+3) zero).set inner.length tag).setSlice! (2*inner.length-2) [high,zero]) =
    ((inner ++ List.replicate (k+3) zero).set inner.length tag).set (2*inner.length-2) high := by
  have rep : List.replicate (k+3) zero=zero::(List.replicate k zero ++ [zero,zero]) := by
    rw [show k+3 = (k+2)+1 by omega,List.replicate_succ,List.replicate_add]; rfl
  rw [set2_tail inner k zero tag high _ _ rfl (by omega),rep,set_mid _ _ _ _ _ rfl]
  have layout : inner ++ tag :: (List.replicate k zero ++ [zero,zero]) =
      (inner ++ tag :: List.replicate k zero) ++ List.replicate 2 zero := by simp
  rw [layout,setSlice_app _ _ _ _ _ (by simp; omega) (by simp)]
  simp

end slhdsa.SegmentedApi
