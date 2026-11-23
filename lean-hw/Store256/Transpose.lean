import Store256.Funs
import Platform.Rounds
open Aeneas Aeneas.Std Result
namespace slhdsa.X86.Store
open StoreRust
abbrev Reg512 := core.core_arch.x86.__m512i

def rowAt (r : Rows) (lane : Nat) := (r.val[lane%4]!).val[lane/4]!
def chooseWord (a b c d : Reg512) (i : Nat) := if i = 0 then a else if i = 1 then b else if i = 2 then c else d

private theorem arr4_get {α : Type} [Inhabited α] (f : Fin 4 → α) (j : Nat) (hj : j < 4) :
    (arr4 f).val[j]! = f ⟨j,hj⟩ := by
  change (Array.from (List.ofFn f) _).val[j]! = _
  rw [Array.from_val, List.getElem!_ofFn]
private theorem arr16_get {α : Type} [Inhabited α] (f : Fin 16 → α) (j : Nat) (hj : j < 16) :
    (arr16 f).val[j]! = f ⟨j,hj⟩ := by
  change (Array.from (List.ofFn f) _).val[j]! = _
  rw [Array.from_val, List.getElem!_ofFn]

theorem transpose_rows_spec (a b c d : Reg512) :
    sha256.x86.avx512.transpose_rows a b c d ⦃ r => ∀ j k : Fin 16,
      ((rowAt r j.val).val[k.val]!).bv = (chooseWord a b c d (k.val/4) j).extractLsb' (8*(k.val%4)) 8 ⦄ := by
  simp only [sha256.x86.avx512.transpose_rows, StoreRust.core.core_arch.x86.unpack,
    core.intrinsics.transmute,step_simps]
  intro j k
  unfold rowAt
  change (((arr4 _ : Rows).val[j.val%4]!).val[j.val/4]!).val[k.val]!.bv = _
  rw [arr4_get _ _ (by omega), arr4_get _ _ (by omega), arr16_get _ _ k.isLt]
  fin_cases j <;> fin_cases k <;> rfl

#print axioms transpose_rows_spec
end slhdsa.X86.Store
