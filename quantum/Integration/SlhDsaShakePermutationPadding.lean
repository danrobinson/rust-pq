import Integration.SlhDsaShakePermutationCost

namespace Reduction.ShakePermutation
open Spec.Keccak

/-- The delimiter and high bit share a byte when only one byte is free. -/
def suffix (pos : Nat) : Spec.Bytes :=
  if pos = 135 then [0x9f] else 0x1f :: List.replicate (134-pos) 0 ++ [0x80]

def padded (xs : Spec.Bytes) : Spec.Bytes := xs ++ suffix (xs.length % 136)

private def unpad (bytes : Spec.Bytes) : Spec.Bytes :=
  match bytes.reverse with
  | [] => []
  | b :: bs => if b = 0x9f then bs.reverse else ((bs.dropWhile (· == 0)).drop 1).reverse

theorem padded_injective : Function.Injective padded := by
  have inv (xs : Spec.Bytes) : unpad (padded xs) = xs := by
    by_cases h : xs.length % 136 = 135 <;> simp [unpad,padded,suffix,h,List.reverse_append,List.append_assoc]
  exact Function.LeftInverse.injective inv

theorem padded_length (xs : Spec.Bytes) : (padded xs).length = 136*(xs.length / 136 + 1) := by
  unfold padded suffix
  split <;> simp only [List.length_append,List.length_cons,List.length_nil,List.length_replicate] <;> omega

private theorem xor_zero (a : State) (i : Nat) : xorByte a i 0 = a := by
  apply Array.ext
  · simp [xorByte]
  · intro j hj hj'
    by_cases he : j=i/8
    · subst j
      simp [xorByte,getElem!_pos,hj']
    · simp [xorByte,hj',Ne.symm he]

private theorem xor_last (a : State) :
    xorByte a 135 0x9f = xorByte (xorByte a 135 0x1f) 135 0x80 := by
  apply Array.ext
  · simp [xorByte]
  · intro j hj hj'
    by_cases he : j=16
    · subst j
      have hi : 16 < a.size := by simpa [xorByte] using hj
      simp [xorByte,getElem!_pos,hi,BitVec.xor_assoc]
    · have hj0 : j < a.size := by simpa [xorByte] using hj
      simp [xorByte,hj0,Ne.symm he]

private theorem zeros_feed (p : State → State) (a : State) (pos n : Nat) (h : pos+n ≤ 135) :
    (List.replicate n (0 : Spec.Byte)).foldl (feed p) (a,pos) = (a,pos+n) := by
  induction n generalizing pos with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ,List.foldl_cons]
    simp only [feed,xor_zero,ite_eq_right (show pos+1 ≠ 136 by omega)]
    rw [ih (pos+1) (by omega)]
    congr 1; omega

theorem fold_suffix (p : State → State) (a : State) (pos : Nat) (h : pos < 136) :
    (suffix pos).foldl (feed p) (a,pos) = (finish p (a,pos),0) := by
  by_cases last : pos = 135
  · subst pos; change (p (xorByte a 135 0x9f),0) = _; rw [xor_last]; rfl
  · simp only [suffix,ite_eq_right last,List.foldl_cons,List.foldl_append]
    simp only [feed,ite_eq_right (show pos+1 ≠ 136 by omega)]
    rw [zeros_feed p _ _ _ (by omega),show pos+1+(134-pos)=135 by omega]
    rfl

/-- The bytewise sponge's state at its first squeeze is absorption of exactly
the padded message, ending on a permutation boundary. -/
theorem fold_padded (p : State → State) (xs : Spec.Bytes) :
    (padded xs).foldl (feed p) initial = (finish p (xs.foldl (feed p) initial),0) := by
  unfold padded
  rw [List.foldl_append]
  change (suffix _).foldl (feed p) (xs.foldl (feed p) (initial.1,0)) = (finish p (xs.foldl (feed p) (initial.1,0)),0)
  rw [foldl_feed p xs initial.1 0 (by decide)]
  simp only [Nat.zero_add]
  exact fold_suffix _ _ _ (Nat.mod_lt _ (by decide))

end Reduction.ShakePermutation
#print axioms Reduction.ShakePermutation.padded_injective
#print axioms Reduction.ShakePermutation.fold_padded
