import Aeneas

/-! Facts about successful checked machine arithmetic, used by the `Ct` proofs. -/

open Aeneas Aeneas.Std

namespace Ct.Arith

theorem sub_ok {ty} {x y z : UScalar ty} (h : x - y = Result.ok z) :
    y.val ≤ x.val ∧ z.val = x.val - y.val := by
  have := UScalar.sub_equiv x y
  rw [h] at this
  simp only [Result.match.ok] at this
  omega

theorem add_ok {ty} {x y z : UScalar ty} (h : x + y = Result.ok z) :
    z.val = x.val + y.val := by
  have := UScalar.add_equiv x y
  rw [h] at this
  simp only [Result.match.ok] at this
  exact this.2.1

theorem mul_ok {ty} {x y z : UScalar ty} (h : x * y = Result.ok z) :
    z.val = x.val * y.val := by
  have := UScalar.mul_equiv x y
  have hm : x * y = UScalar.mul x y := rfl
  rw [← hm, h] at this
  simp only [Result.match.ok] at this
  exact this.2.1

end Ct.Arith
