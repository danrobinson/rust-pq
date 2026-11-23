import Shakebatch.SignProgram
import Shakebatch.ForsNodes
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ShakeBatch
set_option linter.concreteInstances false
variable [machine : Machine]
abbrev Buffer := alloc.vec.Vec U8
abbrev Range := core.ops.range.Range Usize
abbrev Rows (N : Usize) := Array (Array U8 N) machine.width

def Scattered {N} (rows : Rows N) (first stride offset count : Nat) (before after : Buffer) :=
  after.length=before.length ∧ ∀ t q, q < stride → t*stride+q < before.length →
    after.val[t*stride+q]! = if first ≤ t ∧ t < first+count ∧ offset ≤ q ∧ q < offset+N.val
      then rows.val[t-first]!.val[q-offset]! else before.val[t*stride+q]!

omit machine in
private theorem write_at {N : Usize} (xs : List U8) (row : Array U8 N) (t r q stride off : Nat)
    (valid : q < stride) (width : off+N.val ≤ stride) (fit : (r+1)*stride ≤ xs.length) :
    (xs.setSlice! (r*stride+off) row.val)[t*stride+q]! =
      if t=r ∧ off ≤ q ∧ q < off+N.val then row.val[q-off]! else xs[t*stride+q]! := by
  by_cases eq : t=r
  · subst t
    by_cases middle : off ≤ q ∧ q < off+N.val
    · rw [if_pos ⟨rfl,middle⟩,List.getElem!_setSlice!_middle _ _ _ _ (by simp; rw [Nat.add_mul] at fit; omega)]
      congr 1
      omega
    · rw [if_neg (by simp [middle])]
      by_cases pre : q < off
      · exact List.getElem!_setSlice!_prefix _ _ _ _ (by omega)
      · exact List.getElem!_setSlice!_suffix _ _ _ _ (by simp; omega)
  · rw [if_neg (by simp [eq])]
    by_cases pre : t < r
    · have le := Nat.mul_le_mul_right stride (show t+1 ≤ r by omega)
      exact List.getElem!_setSlice!_prefix _ _ _ _ (by rw [Nat.add_mul] at le; omega)
    · have le := Nat.mul_le_mul_right stride (show r+1 ≤ t by omega)
      exact List.getElem!_setSlice!_suffix _ _ _ _ (by rw [Nat.add_mul] at le; simp; omega)

theorem scatter_step {N : Usize} (rows : Rows N) (first stride offset count : Nat)
    (before current after : Buffer) (fit : (first+count+1)*stride ≤ before.length)
    (within : offset+N.val ≤ stride) (prior : Scattered rows first stride offset count before current)
    (save : after.val = current.val.setSlice! ((first+count)*stride+offset) rows.val[count]!.val) :
    Scattered rows first stride offset (count+1) before after := by
  obtain ⟨len,h⟩ := prior
  refine ⟨by change after.val.length = _; rw [save]; simpa using len,?_⟩
  intro t q qbound idx
  rw [save,write_at _ _ _ _ _ _ _ qbound within (by simpa [len] using fit),h _ _ qbound idx]
  by_cases eq : t=first+count
  · subst t
    simp [Nat.add_assoc]
  · have equiv : t < first+(count+1) ↔ t < first+count := by omega
    simp [eq,equiv]

end slhdsa.ShakeBatch
