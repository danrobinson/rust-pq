import Kmixed.Writes

import Keccakasm.Proof
open Aeneas Aeneas.Std Result
open Spec.Keccak
namespace slhdsa.Kmixed
set_option maxRecDepth 65536
set_option maxHeartbeats 6500000

def project (v : V) (j : Fin 3) : Lane :=
  if h : j.val < 2 then v.pair ⟨j.val,h⟩ else v.scalar.bv

private theorem project0 (v : V) : project v 0 = v.pair 0 := rfl
private theorem project1 (v : V) : project v 1 = v.pair 1 := rfl
private theorem project2 (v : V) : project v 2 = v.scalar.bv := rfl

def lane (a : Rows) (j : Fin 3) : State :=
  _root_.Array.ofFn (n := 25) (fun i => project a.val[i.val]! j)

private theorem shiftRotate (x : Lane) (l r : Nat) (h : l < 64) (hr : r = 64-l) :
    ((x <<< l) &&& (BitVec.allOnes 64 <<< l)) ||| (x >>> r) = x.rotateLeft l := by
  rw [← BitVec.shiftLeft_and_distrib,BitVec.and_allOnes]
  simp [BitVec.rotateLeft_def,Nat.mod_eq_of_lt h,hr]

private theorem bx (x y : U64) : (x ^^^ y).bv = x.bv ^^^ y.bv := rfl
private theorem ba (x y : U64) : (x &&& y).bv = x.bv &&& y.bv := rfl
private theorem bn (x : U64) : (~~~x).bv = ~~~x.bv := rfl
private theorem br (x : U64) (k : U32) : (core.num.U64.rotate_left x k).bv = x.bv.rotateLeft k.val := rfl

private theorem cell0 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[0]! j = (round (lane a j) rc.bv)[0]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[0]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 0 ^^^ ((~~~((lane a j)[6]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 44) &&& ((lane a j)[12]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 43)) ^^^ rc.bv
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell1 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[1]! j = (round (lane a j) rc.bv)[1]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[6]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 44 ^^^ ((~~~((lane a j)[12]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 43) &&& ((lane a j)[18]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 21))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell2 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[2]! j = (round (lane a j) rc.bv)[2]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[12]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 43 ^^^ ((~~~((lane a j)[18]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 21) &&& ((lane a j)[24]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 14))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell3 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[3]! j = (round (lane a j) rc.bv)[3]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[18]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 21 ^^^ ((~~~((lane a j)[24]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 14) &&& ((lane a j)[0]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 0))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell4 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[4]! j = (round (lane a j) rc.bv)[4]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[24]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 14 ^^^ ((~~~((lane a j)[0]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 0) &&& ((lane a j)[6]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 44))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell5 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[5]! j = (round (lane a j) rc.bv)[5]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[3]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 28 ^^^ ((~~~((lane a j)[9]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 20) &&& ((lane a j)[10]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 3))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell6 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[6]! j = (round (lane a j) rc.bv)[6]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[9]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 20 ^^^ ((~~~((lane a j)[10]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 3) &&& ((lane a j)[16]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 45))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell7 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[7]! j = (round (lane a j) rc.bv)[7]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[10]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 3 ^^^ ((~~~((lane a j)[16]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 45) &&& ((lane a j)[22]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 61))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell8 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[8]! j = (round (lane a j) rc.bv)[8]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[16]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 45 ^^^ ((~~~((lane a j)[22]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 61) &&& ((lane a j)[3]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 28))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell9 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[9]! j = (round (lane a j) rc.bv)[9]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[22]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 61 ^^^ ((~~~((lane a j)[3]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 28) &&& ((lane a j)[9]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 20))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell10 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[10]! j = (round (lane a j) rc.bv)[10]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[1]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 1 ^^^ ((~~~((lane a j)[7]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 6) &&& ((lane a j)[13]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 25))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell11 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[11]! j = (round (lane a j) rc.bv)[11]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[7]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 6 ^^^ ((~~~((lane a j)[13]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 25) &&& ((lane a j)[19]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 8))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell12 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[12]! j = (round (lane a j) rc.bv)[12]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[13]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 25 ^^^ ((~~~((lane a j)[19]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 8) &&& ((lane a j)[20]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 18))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell13 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[13]! j = (round (lane a j) rc.bv)[13]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[19]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 8 ^^^ ((~~~((lane a j)[20]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 18) &&& ((lane a j)[1]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 1))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell14 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[14]! j = (round (lane a j) rc.bv)[14]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[20]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 18 ^^^ ((~~~((lane a j)[1]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 1) &&& ((lane a j)[7]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 6))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell15 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[15]! j = (round (lane a j) rc.bv)[15]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[4]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 27 ^^^ ((~~~((lane a j)[5]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 36) &&& ((lane a j)[11]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 10))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell16 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[16]! j = (round (lane a j) rc.bv)[16]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[5]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 36 ^^^ ((~~~((lane a j)[11]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 10) &&& ((lane a j)[17]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 15))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell17 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[17]! j = (round (lane a j) rc.bv)[17]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[11]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 10 ^^^ ((~~~((lane a j)[17]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 15) &&& ((lane a j)[23]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 56))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell18 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[18]! j = (round (lane a j) rc.bv)[18]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[17]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 15 ^^^ ((~~~((lane a j)[23]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 56) &&& ((lane a j)[4]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 27))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell19 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[19]! j = (round (lane a j) rc.bv)[19]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[23]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 56 ^^^ ((~~~((lane a j)[4]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 27) &&& ((lane a j)[5]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 36))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell20 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[20]! j = (round (lane a j) rc.bv)[20]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[2]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 62 ^^^ ((~~~((lane a j)[8]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 55) &&& ((lane a j)[14]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 39))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell21 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[21]! j = (round (lane a j) rc.bv)[21]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[8]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 55 ^^^ ((~~~((lane a j)[14]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 39) &&& ((lane a j)[15]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 41))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell22 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[22]! j = (round (lane a j) rc.bv)[22]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[14]! ^^^ (((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!) ^^^ ((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!).rotateLeft 1)).rotateLeft 39 ^^^ ((~~~((lane a j)[15]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 41) &&& ((lane a j)[21]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 2))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell23 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[23]! j = (round (lane a j) rc.bv)[23]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[15]! ^^^ (((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!) ^^^ ((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!).rotateLeft 1)).rotateLeft 41 ^^^ ((~~~((lane a j)[21]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 2) &&& ((lane a j)[2]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 62))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

private theorem cell24 (a : Rows) (rc : U64) (j : Fin 3) :
    project (pureRound a rc).val[24]! j = (round (lane a j) rc.bv)[24]! := by
  rw [roundAt _ _ _ (by decide)]
  change _ = (((lane a j)[21]! ^^^ (((lane a j)[0]! ^^^ (lane a j)[5]! ^^^ (lane a j)[10]! ^^^ (lane a j)[15]! ^^^ (lane a j)[20]!) ^^^ ((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!).rotateLeft 1)).rotateLeft 2 ^^^ ((~~~((lane a j)[2]! ^^^ (((lane a j)[1]! ^^^ (lane a j)[6]! ^^^ (lane a j)[11]! ^^^ (lane a j)[16]! ^^^ (lane a j)[21]!) ^^^ ((lane a j)[3]! ^^^ (lane a j)[8]! ^^^ (lane a j)[13]! ^^^ (lane a j)[18]! ^^^ (lane a j)[23]!).rotateLeft 1)).rotateLeft 62) &&& ((lane a j)[8]! ^^^ (((lane a j)[2]! ^^^ (lane a j)[7]! ^^^ (lane a j)[12]! ^^^ (lane a j)[17]! ^^^ (lane a j)[22]!) ^^^ ((lane a j)[4]! ^^^ (lane a j)[9]! ^^^ (lane a j)[14]! ^^^ (lane a j)[19]! ^^^ (lane a j)[24]!).rotateLeft 1)).rotateLeft 55))
  simp (disch := decide) only [lane,ofFnAt]
  fin_cases j <;> simp (config := {maxSteps := 1200000}) (disch := decide) only [project, dif_pos, dif_neg, pureRound,Id.run,pure,written,List.getElem!_cons_zero,List.getElem!_cons_succ,ite_true,ite_false,reduceCtorEq,shiftRotate,bx,ba,bn,br]
  all_goals ac_rfl

theorem lanes_fips (a : Rows) (rc : U64) (j : Fin 3) :
    lane (pureRound a rc) j = round (lane a j) rc.bv := by
  apply ext25 _ _ (by simp [lane]) (by simp [round])
  intro i hi
  rw [show (lane (pureRound a rc) j)[i]! = _ from ofFnAt _ _ hi]
  interval_cases i
  · exact cell0 a rc j
  · exact cell1 a rc j
  · exact cell2 a rc j
  · exact cell3 a rc j
  · exact cell4 a rc j
  · exact cell5 a rc j
  · exact cell6 a rc j
  · exact cell7 a rc j
  · exact cell8 a rc j
  · exact cell9 a rc j
  · exact cell10 a rc j
  · exact cell11 a rc j
  · exact cell12 a rc j
  · exact cell13 a rc j
  · exact cell14 a rc j
  · exact cell15 a rc j
  · exact cell16 a rc j
  · exact cell17 a rc j
  · exact cell18 a rc j
  · exact cell19 a rc j
  · exact cell20 a rc j
  · exact cell21 a rc j
  · exact cell22 a rc j
  · exact cell23 a rc j
  · exact cell24 a rc j
end slhdsa.Kmixed
