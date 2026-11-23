import Kmixed.Operations
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kmixed
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
private theorem word (a : Rows) (rc : U64) (i : Nat) (hi : i < 25) :
    (compactRound a rc).val[i]! = (pureRound a rc).val[i]! := by
  simp only [compactRound,pureRound,Id.run,pure,written _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi]
  interval_cases i <;> simp only [List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,
    Operations.xor3,Operations.theta,Operations.rho,Operations.chi,reduceCtorEq]
  all_goals rfl
private theorem rowsEq (x y : Rows) (same : ∀ i, i < 25 → x.val[i]! = y.val[i]!) : x=y := by
  apply Aeneas.Std.Array.ext
  apply List.ext_getElem
  · simp
  · intro i hi hj
    rw [← getElem!_pos x.val i hi,← getElem!_pos y.val i hj]
    exact same i (by simpa using hi)

theorem compactEq (a : Rows) (rc : U64) : compactRound a rc = pureRound a rc :=
  rowsEq _ _ (word a rc)
end slhdsa.Kmixed
