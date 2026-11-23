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
end slhdsa.X86.Stream
