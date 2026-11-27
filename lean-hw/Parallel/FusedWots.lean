import Std

namespace ParallelFusedWots

/-- After computing a chain step, the fused loop records the lane only if
the chain length selected by the digit equals the number of hashes so far. -/
def capture {α : Type} (chain : Nat → α) (digit : Nat) (initial : α) : Nat → α
  | 0 => if digit = 0 then chain 0 else initial
  | n+1 => if n+1 = digit then chain (n+1) else capture chain digit initial n

theorem selected {α : Type} (chain : Nat → α) (digit : Nat) (initial : α)
    (n : Nat) (bounded : digit ≤ n) : capture chain digit initial n = chain digit := by
  induction n with
  | zero => have : digit = 0 := by omega
            simp [capture, this]
  | succ n ih =>
    by_cases hit : n+1 = digit
    · simp [capture, hit]
    · simp [capture, hit, ih (by omega)]

end ParallelFusedWots
