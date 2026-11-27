import Armwide.StoreProgram
import Armwide.Kernel
import Aeneas
namespace slhdsa.Armwide.Transitions
open Spec.SHA256
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

private def regByte (lo hi : Arm.V) (i : Nat) : Spec.Byte :=
  ((vwords lo ++ vwords hi)[i/4]!).extractLsb' (8*(i%4)) 8

def storedBytes (n : Nat) (lo hi : Arm.V) : Spec.Bytes :=
  (storeIndices n).map (regByte lo hi)

theorem stored_eq (n : Nat) (hn : n=16 ∨ n=24 ∨ n=32) (lo hi : Arm.V) :
    storedBytes n lo hi = Kernel.storeN n lo hi := by
  rcases hn with rfl|rfl|rfl <;> rfl

/-- The native store writes exactly the digest block of the retiring chain. -/
theorem retirement_store (n : Nat) (hn : n=16 ∨ n=24 ∨ n=32) (c : Nat)
    (out : Spec.Bytes) (room : (c+1)*n ≤ out.length) (lo hi : Arm.V) :
    let next := out.setSlice! (c*n) (storedBytes n lo hi)
    next.length = out.length ∧ ∀ i < out.length,
      next[i]! = if c*n ≤ i ∧ i < (c+1)*n then (Kernel.storeN n lo hi)[i-c*n]! else out[i]! := by
  change (out.setSlice! _ _).length = _ ∧ _
  have size : (storedBytes n lo hi).length = n := by rcases hn with rfl|rfl|rfl <;> rfl
  refine ⟨List.length_setSlice! ..,?_⟩
  intro i h
  rw [Nat.add_mul, Nat.one_mul] at room ⊢
  split
  · rename_i inside
    rw [List.getElem!_setSlice!_middle _ _ _ _ (by omega), stored_eq n hn]
  · rename_i outside
    by_cases front : i < c*n
    · exact List.getElem!_setSlice!_prefix _ _ _ _ front
    · exact List.getElem!_setSlice!_suffix _ _ _ _ (by omega)

end slhdsa.Armwide.Transitions
