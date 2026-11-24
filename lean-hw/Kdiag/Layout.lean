import Kdiag.Odd
open Aeneas Aeneas.Std Result Spec.Keccak
namespace slhdsa.Kdiag
open KdiagRust.shake256.stream_x86
set_option maxRecDepth 24000
set_option maxHeartbeats 1500000

def gridView (diagonal : Bool) (a : Grid) : State :=
  _root_.Array.ofFn (n := 25) fun k =>
    let x := k.val%5
    let y := k.val/5
    a.val[if diagonal then (y+5-x)%5 else y]! ⟨x,by dsimp [x]; omega⟩

theorem gridAt (diag : Bool) (a : Grid) (i : Nat) (hi : i<25) :
    (gridView diag a)[i]! =
      a.val[if diag then (i/5+5-i%5)%5 else i/5]! ⟨i%5,by omega⟩ := by
  unfold gridView
  rw [ofFnAt _ _ hi]


theorem parity_view (diag : Bool) (a : Grid) (x : Nat) (bound : x < 5) :
    Spec.Keccak.parity (gridView diag a) x = parity a ⟨x,by omega⟩ := by
  cases diag <;> interval_cases x <;>
    simp (disch := decide) only [Spec.Keccak.parity,gridAt,parity,
      Bool.false_eq_true,ite_true,ite_false,Nat.reduceAdd,Nat.reduceSub,Nat.reduceMod,Nat.reduceDiv]
  all_goals ac_rfl

theorem delta_view (diag : Bool) (a : Grid) (x : Nat) :
    Spec.Keccak.delta (gridView diag a) x = theta a ⟨x%5,by omega⟩ := by
  unfold Spec.Keccak.delta theta
  rw [parity_view _ _ _ (by omega),parity_view _ _ _ (by omega)]
  congr 3 <;> simp [col] <;> omega


private def origin (i : Nat) := ((i%5)+3*(i/5))%5 + 5*(i%5)
def sourceRow (diag : Bool) (i : Nat) :=
  if diag then (origin i/5 + 5 - origin i%5)%5 else origin i/5
def sourceLane (i : Nat) : Fin 8 := ⟨origin i%5,by omega⟩

private theorem rotationAt (diag : Bool) (i : Nat) (hi : i<25) :
    rotations[origin i]! = rotation diag (sourceRow diag i) (sourceLane i).val % 64 := by
  unfold rotation KdiagRust.shake256.stream_x86.ROT
  cases diag <;> interval_cases i <;> decide +kernel

theorem rhoPi_view (diag : Bool) (a : Grid) (i : Nat) (hi : i<25) :
    Spec.Keccak.rhoPi (gridView diag a) i = rotated a diag (sourceRow diag i) (sourceLane i) := by
  have valid : origin i<25 := by unfold origin; omega
  change ((gridView diag a)[origin i]! ^^^ Spec.Keccak.delta (gridView diag a) (origin i%5)).rotateLeft
      rotations[origin i]! = _
  rw [gridAt _ _ _ valid,delta_view,rotationAt diag i hi]
  simp only [rotated,sourceRow,sourceLane,Nat.mod_mod]

end slhdsa.Kdiag
