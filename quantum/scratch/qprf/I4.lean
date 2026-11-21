example (l : List ℕ) (f : ℕ → ℕ → ℕ) (b : ℕ) : b ∈ l.mapIdx f ↔ ∃ (i : ℕ) (h : i < l.length), f i l[i] = b := by exact?
