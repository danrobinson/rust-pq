import Kgridbulk.Input
import Spec.ShakeWords
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kgridbulk

/-- Match the x86 little-endian load to the eight byte contributions in the FIPS sponge. -/
theorem wordAt_laneBytes (input : List U8) (offset : Nat) (room : offset + 8 ≤ input.length) :
    wordAt input offset = laneBytes 0 (slhdsa.bytes ((input.drop offset).take 8)) := by
  have sub : (input.drop offset).take 8 =
      [input[offset]!,input[offset+1]!,input[offset+2]!,input[offset+3]!,
       input[offset+4]!,input[offset+5]!,input[offset+6]!,input[offset+7]!] := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi _
      have small : i<8 := by simpa using ‹i < [input[offset]!,input[offset+1]!,input[offset+2]!,input[offset+3]!,
        input[offset+4]!,input[offset+5]!,input[offset+6]!,input[offset+7]!].length›
      interval_cases i <;> simp (disch := omega) [getElem!_pos]
  rw [sub]
  simp only [wordAt,GatherRust.core.core_arch.x86.littleWord,slhdsa.bytes,List.map_cons,
    List.map_nil,laneBytes]
  generalize input[offset]! = a
  generalize input[offset+1]! = b
  generalize input[offset+2]! = c
  generalize input[offset+3]! = d
  generalize input[offset+4]! = e
  generalize input[offset+5]! = f
  generalize input[offset+6]! = g
  generalize input[offset+7]! = h
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem,BitVec.getLsbD_append,BitVec.getLsbD_xor,
    BitVec.getLsbD_shiftLeft,BitVec.getLsbD_setWidth]
  interval_cases i <;> simp
end slhdsa.Kgridbulk
