import Integration.SlhDsaShakePermutationFixQuery
import PQ.Interactive.Examples
import PQ.Interactive.QromBridgeUnif

namespace Reduction.ShakePermutation.Fix.Circuit
open OracleComp OracleSpec PQ.Interactive Quantum Matrix
variable {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z] [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
variable [AddCommGroup Y] {ι α : Type} {sp : OracleSpec ι}

noncomputable def permIdx (e : Equiv.Perm (Register X Y Z)) : InstrIdx (Register X Y Z) :=
  unitaryIdx (basisMatrix e) (conjTranspose_basisMatrix_mul_self e.injective)

/-- Compile a reversible circuit directly into the signature adversary's
instruction/port interface, followed by an arbitrary continuation. -/
noncomputable def program : Circuit X Y Z → QOC (Register X Y Z) (portSpec + sp) α →
    QOC (Register X Y Z) (portSpec + sp) α
  | .localOp e, k => liftM ((instrSpec (Register X Y Z) + (portSpec + sp)).query (.inl (permIdx e))) >>= fun _ => k
  | .port, k => liftM ((instrSpec (Register X Y Z) + (portSpec + sp)).query (.inr (.inl ()))) >>= fun _ => k
  | .seq a b, k => a.program (b.program k)

omit [AddCommGroup Y] in
theorem program_count (c : Circuit X Y Z) (k : QOC (Register X Y Z) (portSpec + sp) α) (q : ℕ)
    (hk : CountBound isPort k q) : CountBound isPort (c.program k) (c.cost + q) := by
  induction c generalizing k q with
  | localOp =>
    rw [program,countBound_query_bind]
    simpa [isPort,cost] using hk
  | port =>
    rw [program,countBound_query_bind]
    simp [isPort,cost,hk]
  | seq a b ha hb =>
    simpa [program,cost,Nat.add_assoc] using ha _ _ (hb _ _ hk)

def transport (e : Equiv.Perm (Register X Y Z)) (M : Matrix (WS X Y Z) (WS X Y Z) ℂ) :
    Matrix (WS X Y Z) (WS X Y Z) ℂ :=
  M.submatrix (fun p => (e.symm p.1,p.2)) (fun p => (e.symm p.1,p.2))

omit [AddCommGroup Y] in
private theorem local_branch (e : Equiv.Perm (Register X Y Z)) (i : Fin 1)
    (M : Matrix (WS X Y Z) (WS X Y Z) ℂ) : (framedIdx (permIdx e)).2.1.branch i M = transport e M := by
  change ((unitaryInstr (basisMatrix e) (conjTranspose_basisMatrix_mul_self e.injective)).frame Unit).branch i M = _
  ext p q
  rw [DSubInstrument.branch_frame_apply,MatrixMap.amplify_apply,branch_unitaryInstr]
  change (MatrixMap.conj (basisMatrix e) _ ) _ _ = _
  rw [conj_basisMatrix_equiv]
  rfl

theorem port_branch (H : X → Y) (i : Fin 1) (M : Matrix (WS X Y Z) (WS X Y Z) ℂ) :
    (portInstr H).branch i M = transport ((Circuit.port (Z := Z)).run H) M := by
  change ((oracleRt H).queryStep () (QReg.of Z) (idSplit X Y Z)).branch () _ = _
  rw [QuantumRuntime.queryStep_branch_apply]
  simp only [SubInstrument.branch_relabel,conj_basisMatrix_equiv]
  ext p q
  simp only [submatrix_apply,DSubInstrument.branch_frame_apply,MatrixMap.amplify_apply]
  change (((oracleQuery H).frame Unit).branch () _) _ _ = _
  rw [DSubInstrument.branch_frame_apply,MatrixMap.amplify_apply,branch_oracleQuery_apply]
  unfold oracleUnitary
  rw [conj_basisMatrix_equiv]
  rfl

/-- Exact Born semantics for arbitrary (including off-diagonal) input
operators and arbitrary closed continuations. -/
theorem program_weight (c : Circuit X Y Z) (H : X → Y)
    (k : QOC (Register X Y Z) (portSpec + unifSpec) α) (ev : α → Prop) [DecidablePred ev]
    (M : Matrix (WS X Y Z) (WS X Y Z) ℂ) :
    qWeight ev (compileQ H (c.program k)) M = qWeight ev (compileQ H k) (transport (c.run H) M) := by
  induction c generalizing k M with
  | localOp e =>
    rw [program,compileQ_instr_bind,qWeight_instr_bind]
    change (∑ i : Fin 1, qWeight ev (compileQ H k) ((framedIdx (permIdx e)).2.1.branch i M)) = _
    rw [Fin.sum_univ_one]
    exact congrArg _ (local_branch e 0 M)
  | port =>
    rw [program,compileQ_port_bind,qWeight_instr_bind]
    change (∑ i : Fin 1, qWeight ev (compileQ H k) ((portInstr (E := Z) H).branch i M)) = _
    simp [port_branch]
  | seq a b ha hb =>
    rw [program,ha,hb]
    rfl

/-- The circuit semantics also commute with a stateful probabilistic signer.
The continuation may make further signing calls. -/
theorem program_close_weight {σ : Type} (c : Circuit X Y Z) (H : X → Y)
    (impl : QueryImpl sp (StateT σ ProbComp)) (s : σ)
    (k : QOC (Register X Y Z) (portSpec + sp) α) (ev : α × σ → Prop) [DecidablePred ev]
    (M : Matrix (WS X Y Z) (WS X Y Z) ℂ) :
    qWeight ev (close impl (compileQ H (c.program k)) s) M =
      qWeight ev (close impl (compileQ H k) s) (transport (c.run H) M) := by
  induction c generalizing k M with
  | localOp e =>
    rw [program,compileQ_instr_bind,close_instr_bind,qWeight_instr_bind]
    change (∑ i : Fin 1, qWeight ev (close impl (compileQ H k) s) ((framedIdx (permIdx e)).2.1.branch i M)) = _
    rw [Fin.sum_univ_one]
    exact congrArg _ (local_branch e 0 M)
  | port =>
    rw [program,compileQ_port_bind,close_instr_bind,qWeight_instr_bind]
    change (∑ i : Fin 1, qWeight ev (close impl (compileQ H k) s) ((portInstr (E := Z) H).branch i M)) = _
    simp [port_branch]
  | seq a b ha hb =>
    rw [program,ha,hb]
    rfl

end Reduction.ShakePermutation.Fix.Circuit
#print axioms Reduction.ShakePermutation.Fix.Circuit.program_weight
#print axioms Reduction.ShakePermutation.Fix.Circuit.program_count
#print axioms Reduction.ShakePermutation.Fix.Circuit.program_close_weight
