import Platform.Funs
import Spec.Sha256

open Aeneas Aeneas.Std Result
open core.core_arch.x86.avx512f
namespace slhdsa.X86

private theorem xor3 (a b c : BitVec 32) : ternary 150 a b c = a ^^^ b ^^^ c := by
  change (selectWord a (selectWord b (selectWord c (BitVec.allOnes 32) 0#32) (selectWord c 0#32 (BitVec.allOnes 32))) (selectWord b (selectWord c 0#32 (BitVec.allOnes 32)) (selectWord c (BitVec.allOnes 32) 0#32))) = _
  ext i hi
  simp only [selectWord, Spec.SHA256.ch, Spec.SHA256.maj, BitVec.getElem_and,
    BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_xor, BitVec.getElem_zero,
    BitVec.getElem_allOnes]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

private theorem choose (a b c : BitVec 32) : ternary 202 a b c = Spec.SHA256.ch a b c := by
  change (selectWord a (selectWord b (selectWord c (BitVec.allOnes 32) (BitVec.allOnes 32)) (selectWord c 0#32 0#32)) (selectWord b (selectWord c (BitVec.allOnes 32) 0#32) (selectWord c (BitVec.allOnes 32) 0#32))) = _
  ext i hi
  simp only [selectWord, Spec.SHA256.ch, Spec.SHA256.maj, BitVec.getElem_and,
    BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_xor, BitVec.getElem_zero,
    BitVec.getElem_allOnes]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

private theorem majority (a b c : BitVec 32) : ternary 232 a b c = Spec.SHA256.maj a b c := by
  change (selectWord a (selectWord b (selectWord c (BitVec.allOnes 32) (BitVec.allOnes 32)) (selectWord c (BitVec.allOnes 32) 0#32)) (selectWord b (selectWord c (BitVec.allOnes 32) 0#32) (selectWord c 0#32 0#32))) = _
  ext i hi
  simp only [selectWord, Spec.SHA256.ch, Spec.SHA256.maj, BitVec.getElem_and,
    BitVec.getElem_or, BitVec.getElem_not, BitVec.getElem_xor, BitVec.getElem_zero,
    BitVec.getElem_allOnes]
  cases a[i] <;> cases b[i] <;> cases c[i] <;> rfl

open Spec.SHA256
abbrev Reg := core.core_arch.x86.__m512i

def laneState (a : Array Reg 8#usize) (j : Fin 16) : State :=
  (a.val[0]! j, a.val[1]! j, a.val[2]! j, a.val[3]! j,
   a.val[4]! j, a.val[5]! j, a.val[6]! j, a.val[7]! j)

private theorem laneState_make (a b c d e f g h : Reg) (j : Fin 16) :
    laneState (Array.make 8#usize [a,b,c,d,e,f,g,h]) j =
      (a j, b j, c j, d j, e j, f j, g j, h j) := rfl

private theorem read_lane (a : Array Reg 8#usize) (i : Usize) (h : i.val < 8) :
    a.index_usize i = ok (a.val[i.val]!) := by
  have hi : i.val < a.val.length := by simpa using h
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq, getElem?_pos a.val i.val hi, getElem!_pos a.val i.val hi]

/-- Each register lane performs the FIPS 180-4 step for its own message schedule. -/
theorem round_spec (a : Array Reg 8#usize) (w : Reg) (k : U32)
    (W : Fin 16 → List Word) (t : Nat) (hk : k.bv = K[t]!) (hw : ∀ j, w j = (W j)[t]!) :
    sha256.x86.avx512.round a w k ⦃ out => ∀ j,
      laneState out j = Spec.SHA256.round (W j) (laneState a j) t ⦄ := by
  simp (disch := decide) only [sha256.x86.avx512.round, read_lane, _mm512_ror_epi32,
    _mm512_ternarylogic_epi32, _mm512_add_epi32, _mm512_set1_epi32, lift, bind_ok, step_simps]
  intro j
  rw [laneState_make]
  simp only [laneState, Spec.SHA256.round, bsig0, bsig1,
    show (2#i32).bv.toNat % 32 = 2 by decide,
    show (13#i32).bv.toNat % 32 = 13 by decide,
    show (22#i32).bv.toNat % 32 = 22 by decide,
    show (6#i32).bv.toNat % 32 = 6 by decide,
    show (11#i32).bv.toNat % 32 = 11 by decide,
    show (25#i32).bv.toNat % 32 = 25 by decide,
    show (150#i32).bv.toNat % 256 = 150 by decide,
    show (202#i32).bv.toNat % 256 = 202 by decide,
    show (232#i32).bv.toNat % 256 = 232 by decide,
    show (0#usize).val = 0 by rfl,
    show (1#usize).val = 1 by rfl,
    show (2#usize).val = 2 by rfl,
    show (3#usize).val = 3 by rfl,
    show (4#usize).val = 4 by rfl,
    show (5#usize).val = 5 by rfl,
    show (6#usize).val = 6 by rfl,
    show (7#usize).val = 7 by rfl, xor3, choose, majority,
    show (UScalar.hcast .I32 k).bv = k.bv by rfl, hk, hw]
  congr 1 <;> ac_rfl

#print axioms round_spec
end slhdsa.X86
