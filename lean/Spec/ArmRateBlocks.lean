import Spec.ShakeWords

namespace Spec.Keccak.ArmRateBlocks
open Spec.Keccak

/-- The compiled blocks path XORs a little-endian message word into each of the
first 17 lanes, and then executes its linked 24-round permutation. The cursor here
is a word index, obtained from the register allocation in the block checker. -/
def word (keccak : State → State) (s : State × Nat) (bytes : Bytes) : State × Nat :=
  let i := s.2
  let a := s.1.setIfInBounds i (s.1[i]! ^^^ laneBytes 0 bytes)
  if i = 16 then (keccak a,0) else (a,i+1)

private theorem permuted_size (a : State) : (permute a).size = 25 := by
  have split : rc = rc.extract 0 23 ++ #[rc[23]!] := by decide
  unfold permute
  rw [split, Array.foldl_append]
  simp [round]

theorem foldWords (keccak : State → State) (linked : ∀ a, keccak a = permute a)
    (words : List Bytes) (width : ∀ w ∈ words, w.length = 8)
    (a : State) (size : a.size = 25) (i : Nat) (hi : i < 17) :
    let out := words.foldl (word keccak) (a,i)
    (out.1, 8*out.2) = words.flatten.foldl feed (a,8*i) := by
  induction words generalizing a i with
  | nil => rfl
  | cons w ws ih =>
    have head := feedWord a i w (width w (by simp)) (by omega) hi
    have tailWidth : ∀ x ∈ ws, x.length = 8 := fun x hx => width x (by simp [hx])
    let next := a.setIfInBounds i (a[i]! ^^^ laneBytes 0 w)
    have sz : next.size = 25 := by simp [next,size]
    simp only [List.foldl_cons,List.flatten_cons,List.foldl_append,head]
    by_cases last : i=16
    · simp only [word,last,ite_true,linked]
      exact ih tailWidth _ (permuted_size _) 0 (by decide)
    · simp only [word,last,ite_false]
      simpa [Nat.mul_add] using ih tailWidth next sz (i+1) (by omega)

end Spec.Keccak.ArmRateBlocks
