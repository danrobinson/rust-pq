import Gather512.Funs
import Parent512.Load
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.S512.Gather
open GatherRust.core.core_arch.x86
open _root_.core.core_arch.x86

def swapControl : Reg := fun j => slhdsa.Intel.get ⟨0x04050607,0x00010203,0x0c0d0e0f,0x08090a0b⟩ j.val
def rev32 (w : BitVec 32) :=
  w.extractLsb' 0 8 ++ w.extractLsb' 8 8 ++ w.extractLsb' 16 8 ++ w.extractLsb' 24 8

/-- Each 128-bit shuffle lane independently reverses bytes within each quadword. -/
theorem shuffle_swap (v : Reg) :
    GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8 v swapControl ⦃ r => ∀ j : Fin 8,
      word64 r j = rev32 (v ⟨2*j.val,by omega⟩) ++ rev32 (v ⟨2*j.val+1,by omega⟩) ⦄ := by
  simp only [GatherRust.core.core_arch.x86.avx512bw._mm512_shuffle_epi8,step_simps]
  intro j
  fin_cases j <;> rfl

/-- Reconstruction of eight memory bytes from the little-endian gather result and the byte shuffle. -/
theorem big_after_little (a : List U8) (i : Nat) (bound : i+8 ≤ a.length) :
    let w := littleWord a i
    rev32 (w.extractLsb' 0 32) ++ rev32 (w.extractLsb' 32 32) = Spec.SHA512.word (bytes a) i
    := by
  simp only [littleWord,rev32,Spec.SHA512.word]
  repeat rw [bytes_getElem! _ _ (by omega)]
  simp (disch := omega) only [getElem!_pos]
  generalize a[i] = b0
  generalize a[i+1] = b1
  generalize a[i+2] = b2
  generalize a[i+3] = b3
  generalize a[i+4] = b4
  generalize a[i+5] = b5
  generalize a[i+6] = b6
  generalize a[i+7] = b7
  simp (disch := decide) only [BitVec.extractLsb'_extractLsb'_of_le, Nat.reduceAdd, Nat.reduceSub, BitVec.extractLsb'_eq_self,
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv ++ b3.bv ++ b2.bv ++ b1.bv) (xlo := b0.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv ++ b3.bv ++ b2.bv ++ b1.bv) (b := b0.bv),
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv ++ b3.bv ++ b2.bv) (xlo := b1.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv ++ b3.bv ++ b2.bv) (b := b1.bv),
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv ++ b3.bv) (xlo := b2.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv ++ b3.bv) (b := b2.bv),
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv) (xlo := b3.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv ++ b6.bv ++ b5.bv ++ b4.bv) (b := b3.bv),
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv ++ b6.bv ++ b5.bv) (xlo := b4.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv ++ b6.bv ++ b5.bv) (b := b4.bv),
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv ++ b6.bv) (xlo := b5.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv ++ b6.bv) (b := b5.bv),
    BitVec.extractLsb'_append_eq_of_le (xhi := b7.bv) (xlo := b6.bv),
    BitVec.extractLsb'_append_eq_right (a := b7.bv) (b := b6.bv)]
  let x := b0.bv ++ b1.bv ++ b2.bv ++ b3.bv
  calc
    _ = (x ++ (b4.bv ++ b5.bv ++ b6.bv)) ++ b7.bv :=
      BitVec.append_assoc' (x₁ := x) (x₂ := b4.bv ++ b5.bv ++ b6.bv) (x₃ := b7.bv)
    _ = ((x ++ (b4.bv ++ b5.bv)) ++ b6.bv) ++ b7.bv :=
      congrArg (· ++ b7.bv) (BitVec.append_assoc' (x₁ := x) (x₂ := b4.bv ++ b5.bv) (x₃ := b6.bv))
    _ = _ := congrArg (fun w : BitVec 48 => (w ++ b6.bv) ++ b7.bv)
      (BitVec.append_assoc' (x₁ := x) (x₂ := b4.bv) (x₃ := b5.bv))

#print axioms shuffle_swap
end slhdsa.X86.S512.Gather
