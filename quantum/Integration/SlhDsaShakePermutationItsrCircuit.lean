import Integration.SlhDsaShakePermutationItsrReplay
import Integration.SlhDsaShakePermutationSparsePrefix
import Integration.SlhDsaShakePermutationPort

/-! Coherent evaluation of the native salted forward/inverse port using a
single homogeneous word-valued function oracle. Only one scratch word is live. -/
namespace Reduction.ShakePermutation.ItsrCircuit
open Classical Quantum Fix Fix.Circuit ItsrLabel
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
variable {U : Type} (sel : U → Port)
abbrev Mem (U : Type) := SparsePort.Aux Words U
abbrev C (U : Type) := Circuit Addr Words (Mem U)
def base : Addr := tailHead 0

def view (w : Words) (u : U) : Mem U := (Function.update 0 0 w,u)

def changeWord (g : U → Equiv.Perm Words) : Equiv.Perm (Mem U) where
  toFun s := (Function.update s.1 0 (g s.2 (s.1 0)),s.2)
  invFun s := (Function.update s.1 0 ((g s.2).symm (s.1 0)),s.2)
  left_inv s := by simp
  right_inv s := by simp

@[simp] theorem change_view (g : U → Equiv.Perm Words) (w : Words) (u : U) :
    changeWord g (view w u) = view (g u w) u := by simp [view,changeWord]

def capRead (first : Bool) : C U :=
  lookup base (fun s => ItsrLabel.mask (if first then (sel s.2).1 else !(sel s.2).1) (rateOf (s.1 0)))
    (fun v => changeWord fun _ => RoundPort.capGate (capOf v))

def headRead (d : Bool) : C U :=
  lookup base (fun s => tailHead (capOf (s.1 0)))
    (fun v => changeWord fun u => RoundPort.chooseHead d (rateOf v) (sel u).1)

def round (π : Permutation) : C U :=
  .seq (headRead sel true) (.seq (capRead sel true)
    (.seq (.localOp ((Equiv.refl _).prodCongr (changeWord fun u => RoundPort.direction π (sel u).1)))
      (.seq (capRead sel false) (headRead sel false))))

theorem cap_run (first : Bool) (H : Table) (u : U) (w : Words) :
    (capRead sel first).run H ((base,0),view w u) =
      ((base,0),view (ShakePermutation.mask (fun r => capOf (H (ItsrLabel.mask (if first then (sel u).1 else !(sel u).1) r))) w) u) := by
  let addr := fun s : Mem U => ItsrLabel.mask (if first then (sel s.2).1 else !(sel s.2).1) (rateOf (s.1 0))
  let gate := fun v : Words => changeWord (fun _ : U => RoundPort.capGate (capOf v))
  have stable (v : Words) (s : Mem U) : addr (gate v s) = addr s := by
    simp only [addr,gate,changeWord,Equiv.coe_fn_mk,Function.update_self]
    simp only [RoundPort.capGate,maskEquiv,Function.Involutive.toPerm,Equiv.coe_fn_mk,rate_mask]
  change (lookup base addr gate).run H _ = _
  rw [lookup_clean base addr gate stable]
  simp only [gate,change_view]
  rfl

theorem head_run (d : Bool) (H : Table) (u : U) (w : Words) :
    (headRead sel d).run H ((base,0),view w u) =
      ((base,0),view (if (sel u).1 = d then shear (fun z => rateOf (H (tailHead z))) w else w) u) := by
  let addr := fun s : Mem U => tailHead (capOf (s.1 0))
  let gate := fun v : Words => changeWord (fun u : U => RoundPort.chooseHead d (rateOf v) (sel u).1)
  have stable (v : Words) (s : Mem U) : addr (gate v s) = addr s := by
    simp only [addr,gate,changeWord,Equiv.coe_fn_mk,Function.update_self,RoundPort.chooseHead]
    split
    · simp only [RoundPort.headGate,shearEquiv,Function.Involutive.toPerm,Equiv.coe_fn_mk,Manifest.cap_shear]
    · rfl
  change (lookup base addr gate).run H _ = _
  rw [lookup_clean base addr gate stable]
  simp only [gate,change_view,RoundPort.chooseHead]
  split <;> simp [addr,view,RoundPort.headGate,shearEquiv,Function.Involutive.toPerm,shear]

theorem round_run (π : Permutation) (H : Table) (u : U) (w : Words) :
    (round sel π).run H ((base,0),view w u) = ((base,0),view (oracle (perm π H) ((sel u).1,w)) u) := by
  simp only [round,Circuit.run,Equiv.trans_apply,head_run,cap_run,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,change_view]
  cases e : (sel u).1 <;> simp only [Bool.false_eq_true,ite_false,ite_true,Bool.not_true,Bool.not_false,RoundPort.direction] <;> rfl

def addSelected (act : Words → Equiv.Perm U) : Equiv.Perm (Mem U) where
  toFun s := (s.1,act (s.1 0) s.2)
  invFun s := (s.1,(act (s.1 0)).symm s.2)
  left_inv s := by simp
  right_inv s := by simp

def seed : Equiv.Perm (Mem U) := changeWord fun u => Equiv.addRight (sel u).2

def nativePort (π : Permutation) (act : Words → Equiv.Perm U) : C U :=
  let c := .seq (.localOp ((Equiv.refl _).prodCongr (seed sel))) (round sel π)
  .seq c (.seq (.localOp ((Equiv.refl _).prodCongr (addSelected act))) c.reverse)

theorem public_cost (π : Permutation) (act : Words → Equiv.Perm U) : (nativePort sel π act).cost = 16 := by
  simp only [nativePort,round,capRead,headRead,Circuit.cost,lookup_cost,reverse_cost]

theorem public_run (π : Permutation) (H : Table) (act : Words → Equiv.Perm U)
    (stable : ∀ w u, sel (act w u) = sel u) (u : U) :
    (nativePort sel π act).run H ((base,0),(0,u)) =
      ((base,0),(0,act (oracle (perm π H) (sel u)) u)) := by
  let c : C U := .seq (.localOp ((Equiv.refl _).prodCongr (seed sel))) (round sel π)
  have gather (s : U) : c.run H ((base,0),(0,s)) =
      ((base,0),view (oracle (perm π H) (sel s)) s) := by
    have empty : (0,s) = view 0 s := by simp [view]
    rw [empty]
    simp only [c,Circuit.run,Equiv.trans_apply,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,seed,change_view,
      Equiv.coe_addRight,zero_add,round_run]
  let a := oracle (perm π H) (sel u)
  have back := gather (act a u)
  rw [stable] at back
  change c.reverse.run H (((Equiv.refl _).prodCongr (addSelected act)) (c.run H ((base,0),(0,u)))) = _
  rw [gather,run_reverse]
  apply (c.run H).symm_apply_eq.mpr
  simpa only [addSelected,view,Equiv.prodCongr_apply,Prod.map_apply,Equiv.refl_apply,Equiv.coe_fn_mk,Function.update_self] using back.symm

end
end Reduction.ShakePermutation.ItsrCircuit
