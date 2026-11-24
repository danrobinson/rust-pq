import Integration.SlhDsaShakePermutationFixGates
import QuantumFoundations.Oracle.Unitary

/-! Reversible implementation of coherent table reads. Only the `port`
constructor can depend on the oracle. Every other instruction is an ordinary
basis permutation, and so acts on all superpositions by linear extension. -/
namespace Reduction.ShakePermutation.Fix
open Quantum
abbrev Register (X Y Z : Type) := (X × Y) × Z

inductive Circuit (X Y Z : Type) where
  | localOp (gate : Equiv.Perm (Register X Y Z))
  | port
  | seq (a b : Circuit X Y Z)

namespace Circuit
variable {X Y Z : Type}
def cost : Circuit X Y Z → ℕ
  | .localOp _ => 0
  | .port => 1
  | .seq a b => a.cost + b.cost

def run [AddCommGroup Y] (H : X → Y) : Circuit X Y Z → Equiv.Perm (Register X Y Z)
  | .localOp e => e
  | .port => (oracleEquiv H).prodCongr (Equiv.refl _)
  | .seq a b => (a.run H).trans (b.run H)

def inversePort [AddCommGroup Y] : Circuit X Y Z :=
  let n : Equiv.Perm (Register X Y Z) :=
    Function.Involutive.toPerm (fun s => ((s.1.1,-s.1.2),s.2)) (by intro s; simp)
  .seq (.localOp n) (.seq .port (.localOp n))

@[simp] theorem inversePort_apply [AddCommGroup Y] (H : X → Y) (x : X) (y : Y) (z : Z) :
    inversePort.run H ((x,y),z) = ((x,y-H x),z) := by
  simp [inversePort,run,Function.Involutive.toPerm,sub_eq_add_neg,add_comm]

def reverse [AddCommGroup Y] : Circuit X Y Z → Circuit X Y Z
  | .localOp e => .localOp e.symm
  | .port => inversePort
  | .seq a b => .seq b.reverse a.reverse

@[simp] theorem reverse_cost [AddCommGroup Y] (c : Circuit X Y Z) : c.reverse.cost = c.cost := by
  induction c <;> simp [reverse,cost,inversePort,add_comm, *]

theorem run_reverse [AddCommGroup Y] (H : X → Y) (c : Circuit X Y Z) :
    c.reverse.run H = (c.run H).symm := by
  induction c with
  | localOp => rfl
  | port => ext ⟨⟨x,y⟩,z⟩ : 1; exact inversePort_apply H x y z
  | seq a b ha hb => simp [reverse,run,ha,hb]

/-- Address selection can depend on arbitrary workspace coordinates. -/
noncomputable def load [DecidableEq X] (base : X) (select : Z → X) : Equiv.Perm (Register X Y Z) :=
  Function.Involutive.toPerm (fun s => ((Equiv.swap base (select s.2) s.1.1,s.1.2),s.2))
    (by intro s; simp)

/-- Use the answer as a classical control, while preserving coherence. -/
def use (act : Y → Equiv.Perm Z) : Equiv.Perm (Register X Y Z) where
  toFun s := (s.1,act s.1.2 s.2)
  invFun s := (s.1,(act s.1.2).symm s.2)
  left_inv s := by simp
  right_inv s := by simp

noncomputable def lookup [AddCommGroup Y] [DecidableEq X] (base : X) (select : Z → X)
    (act : Y → Equiv.Perm Z) : Circuit X Y Z :=
  let addr : Circuit X Y Z := .localOp (load base select)
  .seq addr (.seq .port (.seq (.localOp (use act)) (.seq inversePort addr)))

@[simp] theorem lookup_cost [AddCommGroup Y] [DecidableEq X] (base : X) (select : Z → X)
    (act : Y → Equiv.Perm Z) : (lookup base select act).cost = 2 := rfl

theorem lookup_clean [AddCommGroup Y] [DecidableEq X] (base : X) (select : Z → X)
    (act : Y → Equiv.Perm Z) (stable : ∀ y z, select (act y z) = select z)
    (H : X → Y) (z : Z) :
    (lookup base select act).run H ((base,0),z) = ((base,0),act (H (select z)) z) := by
  simp [lookup,run,load,Function.Involutive.toPerm,use,inversePort,stable]

end Circuit
end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.Circuit.lookup_clean
