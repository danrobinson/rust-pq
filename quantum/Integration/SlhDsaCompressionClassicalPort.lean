import Integration.SlhDsaCompressionWideMixed
import MIdeal.PureCompression

namespace Reduction.Compression.ClassicalPort
open MLink Ideal PQ.Interactive PQ.QROM Quantum OracleComp OracleSpec ENNReal Matrix
open scoped ComplexOrder Kronecker
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
abbrev Reg (X Y : Type) := (X × Y) × Unit
local notation "R" => Reg X Y
noncomputable def label (Y : Type) [Fintype Y] [Nonempty Y] : Y ≃ Fin ((Fintype.card Y - 1)+1) :=
  Fintype.equivFinOfCardEq (by have := Fintype.card_pos (α := Y); omega)

noncomputable def act {W : Type} [Fintype W] [DecidableEq W] {n : ℕ}
    (read : W → Fin (n+1)) (next : W → W) : InstrIdx W :=
  ⟨n,DSubInstrument.classical (B := fun _ => W) read next,DSubInstrument.lossless_classical (B := fun _ => W) read next⟩

omit [AddCommGroup Y] in
private theorem framed {n : ℕ} (read : R → Fin (n+1)) (next : R → R) (r : R) (i : Fin (n+1)) :
    (framedIdx (act read next)).2.1.branch i (Matrix.single (r,()) (r,()) 1) =
      if read r = i then Matrix.single (next r,()) (next r,()) 1 else 0 := by
  change ((DSubInstrument.classical (B := fun _ => R) read next).frame Unit).branch i _ = _
  rw [DSubInstrument.branch_frame_single,DSubInstrument.branch_classical_basis]
  split <;> simp_all [Matrix.single_kronecker_single,eq_comm]

private theorem port (H : X → Y) (x : X) :
    (portInstr (E := Unit) H).branch 0 (Matrix.single (((x,0),()),()) (((x,0),()),()) 1) =
      Matrix.single (((x,H x),()),()) (((x,H x),()),()) 1 := by
  change ((oracleRt H).queryStep () (QReg.of Unit) (idSplit X Y Unit)).branch () _ = _
  have step (m : X × Y) : ((oracleRt H).step ()).branch () (Matrix.single (m,()) (m,()) 1) =
      Matrix.single ((m.1,m.2 + H m.1),()) ((m.1,m.2 + H m.1),()) 1 :=
    additiveOracleRuntime_step_branch_single H m ()
  rw [QuantumRuntime.queryStep_branch_single, step, Matrix.single_kronecker_single,one_mul,
      SubInstrument.branch_relabel,conj_basisMatrix_equiv_single]
  simp [idSplit,QuantumRuntime.queryEquivOut_apply]

variable {ι α σ : Type} {sp : OracleSpec ι}
noncomputable def readBasis (x : X) : QOC R (portSpec + sp) Y := do
  let init := fun _ : R => ((x,(0:Y)),())
  let _ ← (instrSpec R + (portSpec + sp)).query (.inl (act (fun _ => (0 : Fin 1)) init))
  let _ ← (instrSpec R + (portSpec + sp)).query (.inr (.inl ()))
  let i ← (instrSpec R + (portSpec + sp)).query (.inl (act (fun r => label Y r.1.2) init))
  return (label Y).symm i

omit [AddCommGroup Y] in
private theorem weight_zero (ev : α → Prop) [DecidablePred ev] (K : Closed (WS X Y Unit) α) :
    qWeight ev K 0 = 0 := by
  have h := qWeight_le_trace ev K (Matrix.PosSemidef.zero)
  simpa using h

/-- A basis read makes one quantum port call. The input basis register can be reused
between reads, and the classical control receives the exact answer. -/
theorem read_weight (H : X → Y) (impl : QueryImpl sp (StateT σ ProbComp))
    (x : X) (r : R) (s : σ) (K : Y × σ → Closed (WS X Y Unit) α)
    (ev : α → Prop) [DecidablePred ev] :
    qWeight ev (close impl (compileQ H (readBasis (sp := sp) x)) s >>= K)
      (Matrix.single (r,()) (r,()) 1) =
    qWeight ev (K (H x,s)) (Matrix.single (((x,0),()),()) (((x,0),()),()) 1) := by
  unfold readBasis compileQ
  simp only [simulateQ_bind,simulateQ_spec_query,simulateQ_pure,compileImplQ,bind_map_left,
    close_instr_bind,close_pure,bind_assoc,pure_bind,qWeight_instr_bind]
  let init := fun _ : R => ((x,(0:Y)),())
  let res := fun v : R => label Y v.1.2
  change (∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin (Fintype.card Y - 1 + 1),
    qWeight ev (K ((label Y).symm k,s)) ((framedIdx (act res init)).2.1.branch k
      ((portInstr H).branch j ((framedIdx (act (fun _ => (0:Fin 1)) init)).2.1.branch i
        (Matrix.single (r,()) (r,()) 1))))) = _
  have prep := framed (X := X) (Y := Y) (fun _ => (0:Fin 1)) init r 0
  rw [ite_eq_left rfl] at prep
  simp only [Fin.sum_univ_one]
  rw [prep]
  change (∑ k, qWeight ev (K ((label Y).symm k,s)) ((framedIdx (act res init)).2.1.branch k
    ((portInstr H).branch 0 (Matrix.single (((x,0),()),()) (((x,0),()),()) 1)))) = _
  rw [port H x]
  have meas := framed (X := X) (Y := Y) res init ((x,H x),())
  simp_rw [meas]
  rw [Finset.sum_eq_single ((label Y) (H x))]
  · simp [res,init]
  · intro i _ hi
    simp [res,Ne.symm hi,weight_zero]
  · simp

end Reduction.Compression.ClassicalPort

#print axioms Reduction.Compression.ClassicalPort.read_weight
