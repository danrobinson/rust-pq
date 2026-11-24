import Integration.SlhDsaShakePermutationSparsePort
import Integration.SlhDsaShakePermutationFixAccess

/-! Reversible compilation of the sparse two-way oracle using exactly
twelve coherent reads of the independently sampled head function. -/
namespace Reduction.ShakePermutation.SparsePort
open Classical Quantum Fix Fix.Circuit PQ.Interactive
noncomputable section
set_option linter.unusedSectionVars false
variable {J Y Z U : Type} [Fintype J] [DecidableEq J] [DecidableEq Y] [DecidableEq Z] [AddCommGroup Y]
variable (e : Words ≃ Y × Z) (a : J ↪ Words) (π : Permutation) (suffix : J → Z) (base : J)

abbrev Aux (Y U : Type) := (Fin 3 → Y) × U

def cell (i : Fin 3) (y : Y) : Equiv.Perm (Aux Y U) where
  toFun u := (Function.update u.1 i (u.1 i + y),u.2)
  invFun u := (Function.update u.1 i (u.1 i - y),u.2)
  left_inv u := by simp
  right_inv u := by simp

def store (select : U → Port) (i : Fin 3) : Circuit J Y (Aux Y U) :=
  lookup base (fun u => (slot e a π suffix (select u.2) i).getD base) (cell i)

def gather (select : U → Port) : Circuit J Y (Aux Y U) :=
  .seq (store e a π suffix base select 0)
    (.seq (store e a π suffix base select 1) (store e a π suffix base select 2))

theorem gather_run (select : U → Port) (F : J → Y) (u : U) :
    (gather e a π suffix base select).run F ((base,0),(0,u)) =
      ((base,0),(value e a π suffix F base (select u),u)) := by
  have one (i : Fin 3) (r : Fin 3 → Y) :
      (store e a π suffix base select i).run F ((base,0),(r,u)) =
        ((base,0),(Function.update r i (r i + value e a π suffix F base (select u) i),u)) :=
    lookup_clean base _ _ (fun _ _ => rfl) _ _
  simp only [gather,Circuit.run,Equiv.trans_apply,one]
  congr 3
  funext i
  fin_cases i <;> simp

def applyValue (select : U → Port) (act : Words → Equiv.Perm U) (stable : ∀ w u, select (act w u) = select u) :
    Equiv.Perm (Aux Y U) where
  toFun u := (u.1,act (eval e a π suffix (select u.2) u.1) u.2)
  invFun u := (u.1,(act (eval e a π suffix (select u.2) u.1)).symm u.2)
  left_inv u := by simp [stable]
  right_inv u := by
    have hs (w : Words) (z : U) : select ((act w).symm z) = select z := by
      simpa only [Equiv.apply_symm_apply] using (stable w ((act w).symm z)).symm
    simp [hs]

def circuit (select : U → Port) (act : Words → Equiv.Perm U) (stable : ∀ w u, select (act w u) = select u) :
    Circuit J Y (Aux Y U) :=
  let g := gather e a π suffix base select
  .seq g (.seq (.localOp ((Equiv.refl _).prodCongr (applyValue e a π suffix select act stable))) g.reverse)

theorem circuit_cost (select : U → Port) (act : Words → Equiv.Perm U) (stable) :
    (circuit e a π suffix base select act stable).cost = 12 := by
  simp only [circuit,gather,store,Circuit.cost,Circuit.reverse_cost,lookup_cost]

theorem circuit_run (select : U → Port) (act : Words → Equiv.Perm U) (stable) (F : J → Y) (u : U) :
    (circuit e a π suffix base select act stable).run F ((base,0),(0,u)) =
      ((base,0),(0,act (eval e a π suffix (select u) (value e a π suffix F base (select u))) u)) := by
  let v := value e a π suffix F base (select u)
  let w := eval e a π suffix (select u) v
  have back := (gather_run e a π suffix base select F (act w u))
  simp only [stable] at back
  have inv := ((gather e a π suffix base select).run F).symm_apply_eq.mpr back.symm
  simp only [circuit,Circuit.run,Equiv.trans_apply,gather_run,Circuit.run_reverse]
  exact inv

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.circuit_run
#print axioms Reduction.ShakePermutation.SparsePort.circuit_cost
