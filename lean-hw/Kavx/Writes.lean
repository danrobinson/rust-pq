import Kavx.Rows
import Mathlib.Tactic.IntervalCases
open Aeneas Aeneas.Std Result
namespace slhdsa.Kavx
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
private theorem setAt (a : Rows) (k : Usize) (v : Reg) (i : Nat) (h : k.val = i) (hi : i < 25) :
    (a.set k v).val[i]! = v := by
  rw [Array.set_val_eq,getElem!_pos _ _ (by simp; omega),List.getElem_set,if_pos h]
private theorem setOther (a : Rows) (k : Usize) (v : Reg) (i : Nat) (h : k.val ≠ i) (hi : i < 25) :
    (a.set k v).val[i]! = a.val[i]! := by
  rw [Array.set_val_eq,getElem!_pos _ _ (by simp; omega),List.getElem_set,if_neg h,getElem!_pos _ _ (by simpa using hi)]
theorem written (a : Rows) (rc v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 : Reg) (i : Nat) (hi : i < 25) (j : Fin 8) :
    (writeRows a rc v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24).val[i]! j =
      (if i=0 then v0 j ^^^ rc j else ([v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24] : List Reg)[i]! j) := by
  unfold writeRows
  interval_cases i <;> simp (config := {maxSteps := 500000}) (disch := decide) only [
    Id.run,pure,setAt,setOther,List.getElem!_cons_zero,List.getElem!_cons_succ]
  all_goals rfl
end slhdsa.Kavx
