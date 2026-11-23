import Streamround.Schedule
import Avx2.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Stream

theorem read32 (a : Array U8 4#usize) :
    (core.num.U32.from_be_bytes a).bv = a.val[0]!.bv ++ a.val[1]!.bv ++ a.val[2]!.bv ++ a.val[3]!.bv := by
  let xs := [a.val[0]!,a.val[1]!,a.val[2]!,a.val[3]!]
  have rebuild : a = Array.make 4#usize xs (by rfl) := by
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp [xs]
    · intro i hi _
      have lt : i < 4 := by simpa using hi
      interval_cases i <;> simp [xs,getElem!_pos]
  calc
    _ = (core.num.U32.from_be_bytes (Array.make 4#usize xs (by rfl))).bv := congrArg (fun x => (core.num.U32.from_be_bytes x).bv) rebuild
    _ = _ := Avx2.be_four _ _ _ _

private theorem be_eight (a b c d e f g h : U8) :
    (core.num.U64.from_be_bytes (Array.make 8#usize [a,b,c,d,e,f,g,h])).bv =
      a.bv ++ b.bv ++ c.bv ++ d.bv ++ e.bv ++ f.bv ++ g.bv ++ h.bv := by
  change (BitVec.fromLEBytes [h.bv,g.bv,f.bv,e.bv,d.bv,c.bv,b.bv,a.bv]).cast (by rfl) = _
  simp only [BitVec.fromLEBytes,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul,BitVec.cast_eq]
  ext i hi
  simp only [BitVec.getElem_append (n := 56) (m := 8),
    BitVec.getElem_append (n := 48) (m := 8),
    BitVec.getElem_append (n := 40) (m := 8),
    BitVec.getElem_append (n := 32) (m := 8),
    BitVec.getElem_append (n := 24) (m := 8),
    BitVec.getElem_append (n := 16) (m := 8),
    BitVec.getElem_append (n := 8) (m := 8)]
  interval_cases i <;> simp [BitVec.getElem_or,BitVec.getElem_shiftLeft,BitVec.getElem_setWidth]

theorem read64 (a : Array U8 8#usize) :
    (core.num.U64.from_be_bytes a).bv = a.val[0]!.bv ++ a.val[1]!.bv ++ a.val[2]!.bv ++ a.val[3]!.bv ++ a.val[4]!.bv ++ a.val[5]!.bv ++ a.val[6]!.bv ++ a.val[7]!.bv := by
  let xs := [a.val[0]!,a.val[1]!,a.val[2]!,a.val[3]!,a.val[4]!,a.val[5]!,a.val[6]!,a.val[7]!]
  have rebuild : a = Array.make 8#usize xs (by rfl) := by
    apply Aeneas.Std.Array.ext
    apply List.ext_getElem
    · simp [xs]
    · intro i hi _
      have lt : i < 8 := by simpa using hi
      interval_cases i <;> simp [xs,getElem!_pos]
  calc
    _ = (core.num.U64.from_be_bytes (Array.make 8#usize xs (by rfl))).bv := congrArg (fun x => (core.num.U64.from_be_bytes x).bv) rebuild
    _ = _ := be_eight _ _ _ _ _ _ _ _

private theorem loadedByte {n m} (block : Array U8 n) (part : Array U8 m) (off j : Nat)
    (piece : part.val = (block.val.drop off).take m.val)
    (room : off+m.val ≤ n.val) (hj : j < m.val) :
    part.val[j]!.bv = (bytes block.val)[off+j]! := by
  have a : j < part.val.length := by simpa using hj
  have b : off+j < block.val.length := by simpa using (show off+j < n.val by omega)
  have mapped : off+j < (bytes block.val).length := by simpa [bytes] using b
  rw [getElem!_pos part.val j a,getElem!_pos (bytes block.val) (off+j) mapped]
  simp only [bytes,List.getElem_map]
  rw [List.getElem_of_eq piece a]
  simp [List.getElem_take,List.getElem_drop]

theorem load256 (block : Array U8 64#usize) (i : Nat) (hi : i < 16)
    (part : Array U8 4#usize) (piece : part.val = (block.val.drop (4*i)).take 4) :
    (core.num.U32.from_be_bytes part).bv = (Spec.SHA256.schedule (bytes block.val))[i]! := by
  rw [read32,slhdsa.schedule_lt16 _ _ hi]
  unfold Spec.SHA256.word
  have h := loadedByte block part (4*i)
  have room : 4*i+(4#usize).val ≤ (64#usize).val := by change 4*i+4 ≤ 64; omega
  simp only [h 0 piece room (by decide),h 1 piece room (by decide),h 2 piece room (by decide),h 3 piece room (by decide),Nat.add_zero]

theorem load512 (block : Array U8 128#usize) (i : Nat) (hi : i < 16)
    (part : Array U8 8#usize) (piece : part.val = (block.val.drop (8*i)).take 8) :
    (core.num.U64.from_be_bytes part).bv = (Spec.SHA512.schedule (bytes block.val))[i]! := by
  rw [read64,slhdsa.H512.schedule_lt16 _ _ hi]
  unfold Spec.SHA512.word
  have h := loadedByte block part (8*i)
  have room : 8*i+(8#usize).val ≤ (128#usize).val := by change 8*i+8 ≤ 128; omega
  simp only [h 0 piece room (by decide),h 1 piece room (by decide),h 2 piece room (by decide),h 3 piece room (by decide),h 4 piece room (by decide),h 5 piece room (by decide),h 6 piece room (by decide),h 7 piece room (by decide),Nat.add_zero]
end slhdsa.X86.Stream
