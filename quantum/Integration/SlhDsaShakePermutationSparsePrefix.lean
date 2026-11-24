import Integration.SlhDsaShakePermutationSparseWorkspace
import PQ.Interactive.QromBridgeEvalProg

namespace Reduction.ShakePermutation.SparsePort
open Fix Fix.Circuit Classical PQ.Interactive Quantum OracleSpec OracleComp
noncomputable section
variable {X Y Z α : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype Z] [DecidableEq Z]
local notation "Mach" => (X → Y) → Closed (WS X Y Z) α

def compute : Circuit X Y Z → Mach → Mach
  | .localOp e,k => fun H => liftM ((instrSpec (WS X Y Z) + unifSpec).query (.inl (framedIdx (permIdx e)))) >>= fun _ => k H
  | .port,k => fun H => liftM ((instrSpec (WS X Y Z) + unifSpec).query (.inl (portIdx H))) >>= fun _ => k H
  | .seq a b,k => compute a (compute b k)

theorem compute_cost (c : Circuit X Y Z) (k : Mach) (q : ℕ) (h : PUE (spec := unifSpec) cnt0 k q) :
    PUE (spec := unifSpec) cnt0 (compute c k) (c.cost+q) := by
  induction c generalizing k q with
  | localOp e => simpa only [compute,Circuit.cost,zero_add] using PUE.instr (permIdx e) (fun _ => k) q (fun _ => h)
  | port => simpa only [compute,Circuit.cost,Nat.add_comm 1 q] using PUE.port k q h
  | seq a b ha hb => simpa only [Circuit.cost,Nat.add_assoc,compute] using ha _ _ (hb _ _ h)

theorem compute_weight (c : Circuit X Y Z) (k : Mach) (H : X → Y) (ev : α → Prop) [DecidablePred ev]
    (M : Matrix (WS X Y Z) (WS X Y Z) ℂ) :
    qWeight ev (compute c k H) M = qWeight ev (k H) (transport (c.run H) M) := by
  induction c generalizing k M with
  | localOp e =>
    rw [compute,qWeight_instr_bind]
    change (∑ i : Fin 1, qWeight ev (k H) _) = _
    rw [Fin.sum_univ_one]
    exact congrArg _ (local_branch e 0 M)
  | port =>
    rw [compute,qWeight_instr_bind]
    change (∑ i : Fin 1, qWeight ev (k H) _) = _
    rw [Fin.sum_univ_one]
    exact congrArg _ (port_branch H 0 M)
  | seq a b ha hb => rw [compute,ha,hb]; rfl

end
end Reduction.ShakePermutation.SparsePort
#print axioms Reduction.ShakePermutation.SparsePort.compute_weight
