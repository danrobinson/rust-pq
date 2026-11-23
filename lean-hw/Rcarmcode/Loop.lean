import Slhdsa.Proofs.Hw.Model

namespace slhdsa.RcArmCode

/-- The release loops increment a 64-bit byte pointer once per block, compare it
with the precomputed end pointer, and branch on inequality. A valid Rust slice
fits in its address space and each block has positive stride. -/
theorem pointer_loop (base stride count i : Nat) (positive : 0 < stride) (within : i < count)
    (valid : base + stride * count < 2 ^ 64) :
    let current := BitVec.ofNat 64 (base + stride * i)
    let limit := BitVec.ofNat 64 (base + stride * count)
    let next := current + BitVec.ofNat 64 stride
    next.toNat = base + stride * (i + 1) ∧ (next = limit ↔ i + 1 = count) := by
  have safe : base + stride * (i + 1) < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left stride within) base) valid
  have curSafe : base + stride * i < 2 ^ 64 :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left stride (Nat.le_of_lt within)) base) valid
  have strideSafe : stride < 2 ^ 64 := by
    rw [Nat.mul_succ] at safe
    omega
  have eq : (BitVec.ofNat 64 (base + stride * i) + BitVec.ofNat 64 stride).toNat =
      base + stride * (i + 1) := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt curSafe, Nat.mod_eq_of_lt strideSafe]
    rw [Nat.mul_succ] at safe ⊢
    simpa only [Nat.add_assoc] using Nat.mod_eq_of_lt safe
  refine ⟨eq, ?_⟩
  rw [← BitVec.toNat_inj, eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt valid]
  exact Nat.add_left_cancel_iff.trans (Nat.mul_right_inj (Nat.ne_of_gt positive))

end slhdsa.RcArmCode
