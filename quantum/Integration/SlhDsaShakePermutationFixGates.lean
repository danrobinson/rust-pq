import Integration.SlhDsaShakePermutationFix

namespace Reduction.ShakePermutation.Fix

/-- XOR a single word of a variable-length block register. Indices beyond
the active length leave the register alone. -/
def xorAt (v : Rate) : ℕ → List Rate → List Rate
  | _, [] => []
  | 0, x::xs => rateXor x v :: xs
  | i+1, x::xs => x :: xorAt v i xs

@[simp] theorem xorAt_length (v : Rate) (i : ℕ) (xs : List Rate) : (xorAt v i xs).length = xs.length := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [xorAt,ih]

@[simp] theorem xorAt_take (v : Rate) (i : ℕ) (xs : List Rate) : (xorAt v i xs).take i = xs.take i := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [xorAt,ih]

@[simp] theorem xorAt_twice (v : Rate) (i : ℕ) (xs : List Rate) : xorAt v i (xorAt v i xs) = xs := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp [xorAt,ih]

theorem xorAt_append (v : Rate) (p : List Rate) (x : Rate) (tail : List Rate) :
    xorAt v p.length (p ++ x::tail) = p ++ rateXor x v :: tail := by
  induction p <;> simp [xorAt, *]

theorem xorAt_past (v : Rate) (i : ℕ) (xs : List Rate) (h : xs.length ≤ i) : xorAt v i xs = xs := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i <;> simp_all [xorAt]

/-- The control prefix of each gate is disjoint from the selected target. -/
def gate (f : List Rate → Rate) (i : ℕ) (xs : List Rate) : List Rate :=
  if i = 0 then xs else xorAt (f (xs.take i)) i xs

@[simp] theorem gate_length (f : List Rate → Rate) (i : ℕ) (xs : List Rate) :
    (gate f i xs).length = xs.length := by by_cases h : i = 0 <;> simp [gate,h]

theorem gate_involution (f : List Rate → Rate) (i : ℕ) : Function.Involutive (gate f i) := by
  intro xs
  by_cases h : i = 0 <;> simp [gate,h]

theorem gate_append (f : List Rate → Rate) (p : List Rate) (x : Rate) (tail : List Rate) :
    gate f p.length (p ++ x :: tail) = p ++ maskNext f p x :: tail := by
  cases p with
  | nil => rfl
  | cons a l =>
    let p := a::l
    have ne : p.length ≠ 0 := by simp [p]
    change gate f p.length (p ++ x::tail) = p ++ maskNext f p x :: tail
    rw [gate,ite_eq_right ne,List.take_left,xorAt_append]
    rfl

def sweep (f : List Rate → Rate) : ℕ → List Rate → List Rate
  | 0 => id
  | i+1 => gate f i ∘ sweep f i

theorem sweep_prefix (f : List Rate → Rate) (p tail : List Rate) :
    sweep f p.length (p ++ tail) = fix f p ++ tail := by
  induction p using List.reverseRecOn generalizing tail with
  | nil => rfl
  | append_singleton p x ih =>
    simp only [List.length_append,List.length_singleton,sweep,Function.comp_apply,List.append_assoc,List.singleton_append]
    rw [ih,← fix_length f p,gate_append,fix_append,List.append_assoc,List.singleton_append]

theorem sweep_done (f : List Rate → Rate) (i : ℕ) (xs : List Rate) (h : xs.length ≤ i) :
    sweep f i xs = fix f xs := by
  induction i with
  | zero => have : xs = [] := List.length_eq_zero_iff.mp (by omega); subst xs; rfl
  | succ i ih =>
    by_cases ht : xs.length ≤ i
    · rw [sweep,Function.comp_apply,ih ht]
      unfold gate
      split <;> first | rfl | exact xorAt_past _ _ _ (by simpa using ht)
    · have he : xs.length = i+1 := by omega
      rw [← he]
      simpa only [List.append_nil] using sweep_prefix f xs []

end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.sweep_done
