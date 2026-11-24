import Shani.Rounds
open Aeneas Aeneas.Std Result
namespace slhdsa.Intel
open core.core_arch.x86

def nextWord (a b c d : Word) := a + ssig0 b + c + ssig1 d

def expand (a b c d : Reg) : Result Reg := do
  let x ← sha._mm_sha256msg1_epu32 a b
  let y ← ssse3._mm_alignr_epi8 4#i32 d c
  let z ← sse2._mm_add_epi32 x y
  sha._mm_sha256msg2_epu32 z d

theorem expand_spec (W : List Word) (p : Nat) (limit : p+19 < 64)
    (rec : ∀ k, 16 ≤ k → k < 64 → W[k]! = Spec.SHA256.ssig1 W[k-2]! + W[k-7]! +
        Spec.SHA256.ssig0 W[k-15]! + W[k-16]!) :
    expand (group W p) (group W (p+4)) (group W (p+8)) (group W (p+12)) =
      ok (group W (p+16)) := by
  have algebra (a b c d : Word) : nextWord a b c d =
      Spec.SHA256.ssig1 d + c + Spec.SHA256.ssig0 b + a := by
    unfold nextWord
    change a + ssig0 b + c + ssig1 d = ssig1 d + c + ssig0 b + a
    generalize ssig0 b = x
    generalize ssig1 d = y
    ac_rfl
  have h (j : Nat) (hj : j < 4) : nextWord W[p+j]! W[p+j+1]! W[p+j+9]! W[p+j+14]! = W[p+j+16]! := by
    rw [algebra, rec (p+j+16) (by omega) (by omega)]
    rw [show p+j+16-2 = p+j+14 by omega, show p+j+16-7 = p+j+9 by omega, show p+j+16-15 = p+j+1 by omega, show p+j+16-16 = p+j by omega]
  simp only [expand, align4, sha._mm_sha256msg1_epu32, sha._mm_sha256msg2_epu32, sse2._mm_add_epi32,
    bind_ok, group]
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  simp only [Nat.add_zero, Nat.add_assoc, Nat.reduceAdd] at h0 h1 h2 h3 ⊢
  unfold nextWord at h0 h1 h2 h3
  rw [h0,h1,h2,h3]

#print axioms expand_spec
end slhdsa.Intel
