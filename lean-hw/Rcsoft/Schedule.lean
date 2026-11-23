import Rcsoft.Funs
import Streamround.Read
import Slhdsa.Proofs.Sha512Core
open Aeneas Aeneas.Std Result
namespace slhdsa.RcSoftProof
open Spec.SHA512

/-- Before round i, the array holds the most recent sixteen expanded words,
or the initial sixteen input words while i is below sixteen. -/
def Ring (w : List Word) (ring : Array U64 16#usize) (i : Nat) :=
  ∀ j, max i 16 - 16 ≤ j → j < max i 16 → (ring.val[j % 16]!).bv = w[j]!

theorem ring_init (w : List Word) (ring : Array U64 16#usize)
    (words : ∀ j < 16, (ring.val[j]!).bv = w[j]!) : Ring w ring 0 := by
  intro j _ hj
  change j < 16 at hj
  simpa only [Nat.mod_eq_of_lt hj] using words j hj

private theorem advance (w : List Word) (ring : Array U64 16#usize) (i : Nat)
    (hi : 16 ≤ i) (hr : Ring w ring i) (v : U64) (hv : v.bv = w[i]!)
    (out : Array U64 16#usize) (hset : out.val = ring.val.set (i % 16) v) : Ring w out (i+1) := by
  intro j hlo hhi
  have le : 16 ≤ i+1 := by omega
  rw [Nat.max_eq_left le] at hlo hhi
  rw [hset]
  by_cases h : j = i
  · subst j
    have inside : i % 16 < ring.val.length := by simp; omega
    rw [getElem!_pos _ _ (by simpa using inside), List.getElem_set_self]
    exact hv
  · have ne : i % 16 ≠ j % 16 := by omega
    rw [List.getElem!_eq_getElem?_getD,List.getElem?_set_ne ne,← List.getElem!_eq_getElem?_getD]
    apply hr <;> rw [Nat.max_eq_left hi] <;> omega

def nextWord (block : Array U64 16#usize) (i : Usize) : Result (Array U64 16#usize × U64) :=
      if i < 16#usize
      then do
           let w1 ← Array.index_usize block i
           ok (block, w1)
      else
        do
        let i1 ← i - 15#usize
        let i2 ← i1 % 16#usize
        let w15 ← Array.index_usize block i2
        let i3 ← lift (core.num.U64.rotate_right w15 1#u32)
        let i4 ← lift (core.num.U64.rotate_right w15 8#u32)
        let i5 ← lift (i3 ^^^ i4)
        let i6 ← w15 >>> 7#i32
        let s0 ← lift (i5 ^^^ i6)
        let i7 ← i - 2#usize
        let i8 ← i7 % 16#usize
        let w2 ← Array.index_usize block i8
        let i9 ← lift (core.num.U64.rotate_right w2 19#u32)
        let i10 ← lift (core.num.U64.rotate_right w2 61#u32)
        let i11 ← lift (i9 ^^^ i10)
        let i12 ← w2 >>> 6#i32
        let s1 ← lift (i11 ^^^ i12)
        let i13 ← i % 16#usize
        let i14 ← Array.index_usize block i13
        let i15 ← lift (core.num.U64.wrapping_add i14 s0)
        let i16 ← i - 7#usize
        let i17 ← i16 % 16#usize
        let i18 ← Array.index_usize block i17
        let i19 ← lift (core.num.U64.wrapping_add i15 i18)
        let i20 ← lift (core.num.U64.wrapping_add i19 s1)
        let block2 ← Array.update block i13 i20
        let w1 ← Array.index_usize block2 i13
        ok (block2, w1)

private theorem reverse_sum (a b c d : Word) : a+b+c+d = d+c+b+a := by ac_rfl

set_option maxHeartbeats 400000 in
theorem next_word (B : Spec.Bytes) (ring : Array U64 16#usize) (i : Usize) (hi : i.val < 80)
    (hr : Ring (schedule B) ring i.val) :
    nextWord ring i ⦃ out => Ring (schedule B) out.1 (i.val+1) ∧ out.2.bv = (schedule B)[i.val]! ⦄ := by
  unfold nextWord
  split
  · rename_i h
    have low : i.val < 16 := h
    step
    constructor
    · simpa only [Ring, Nat.max_eq_right (by omega : i.val+1 ≤ 16),
        Nat.max_eq_right (by omega : i.val ≤ 16)] using hr
    · have x := hr i.val (by omega) (by omega)
      rw [Nat.mod_eq_of_lt low] at x
      simpa [getElem!_pos, *] using x
  · rename_i h
    have high : 16 ≤ i.val := by scalar_tac
    step*
    have index (j : Nat) (lo : i.val-16 ≤ j) (lt : j < i.val) (idx : Usize)
        (eq : idx.val = j%16) (valid : idx.val < ring.val.length) :
        (ring.val[idx.val]'valid).bv = (schedule B)[j]! := by
      rw [← getElem!_pos ring.val idx.val valid, eq]
      apply hr <;> rw [Nat.max_eq_left high] <;> omega
    have a15 : w15.bv = (schedule B)[i.val-15]! := by
      rw [w15_post]; apply index <;> omega
    have a2 : w2.bv = (schedule B)[i.val-2]! := by
      rw [w2_post]; apply index <;> omega
    have a7 : i18.bv = (schedule B)[i.val-7]! := by
      rw [i18_post]; apply index <;> omega
    have a16 : i14.bv = (schedule B)[i.val-16]! := by
      rw [i14_post]; apply index <;> omega
    have lo : s0.bv = ssig0 (schedule B)[i.val-15]! := by
      simp only [s0_post1,i5_post1,i3_post,i4_post,i6_post1,S512.rotr_bv,a15,ssig0]
      rfl
    have hiWord : s1.bv = ssig1 (schedule B)[i.val-2]! := by
      simp only [s1_post1,i11_post1,i9_post,i10_post,i12_post1,S512.rotr_bv,a2,ssig1]
      rfl
    have value : i20.bv = (schedule B)[i.val]! := by
      rw [i20_post, core.num.U64.wrapping_add_bv_eq, i19_post, core.num.U64.wrapping_add_bv_eq,
        i15_post, core.num.U64.wrapping_add_bv_eq, a16, lo, a7, hiWord, H512.schedule_rec B i.val high hi]
      apply reverse_sum
    have updated : block2.val = ring.val.set (i.val%16) i20 := by
      rw [block2_post,Array.set_val_eq,i13_post]
    refine ⟨advance _ _ _ high hr i20 value _ updated, ?_⟩
    rw [w1_post]
    simpa only [block2_post, Array.set_val_eq, List.getElem_set_self] using value

end slhdsa.RcSoftProof
