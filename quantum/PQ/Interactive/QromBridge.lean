import PQ.Interactive.Model
import PQ.QROM.Defs

/-!
# Bridge: Part-1 machines with an oracle port ⟷ VCVio quantum query programs

A *QROM program* on the fixed workspace `W = (X × Y) × E` is a classical control tree whose nodes
are lossless instruments on `W` and calls of one *oracle port* acting on the `X × Y` factor:
`QProg X Y E α = QOC ((X × Y) × E) portSpec α`.

Two semantics:

* **Part 1** (`compile H P`): for a fixed function `H : X → Y` every port call is replaced by an
  instrument node — the oracle unitary `U_H |x, y⟩ = |x, y + H x⟩` on the `X × Y` factor, as VCVio's
  `queryStep` of `additiveOracleRuntime H` — giving a closed Part-1 machine on the workspace
  `W × Unit` (VCVio runs programs next to the runtime's private register, here `Unit`), with Born
  semantics `qWeight`.
* **Part 2** (`toQC P`): the same tree as a VCVio program `QuantumComp LocalSig.instruments
  (qromSpec X Y) (fun _ ↦ α) (QReg.of W)` (instrument nodes are local operations, port calls are
  `queryBind` at the identity splitting of the register), run against `additiveOracleRuntime H`,
  with semantics `PQ.QROM.qprob`.

`qprob_toQC_eq_qWeight_compile`: the two semantics agree for every program, every `H`, every
initial substate and every event on the output.

Restriction: programs on ONE fixed register `W = (X × Y) × E` whose oracle calls all act on the
same `X × Y` factor and whose local operations are lossless instruments with finitely many
outcomes `Fin (n+1)` returning to `W` (the Part-1 model has a fixed finite workspace).  No
classical oracle (signing queries / classical requests of `IAdv`) and no uniform-sampling nodes
in this file.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.Interactive

variable {X Y E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype E] [DecidableEq E] {α : Type}

/-- VCVio's `additiveOracleRuntime H`, as a reducible definition (so that its private register
`Unit` is visible to unification); `additiveOracleRuntime_eq`. -/
@[reducible] noncomputable def oracleRt (H : X → Y) : QuantumRuntime (qromSpec X Y) where
  D := QReg.of Unit
  init := SubState.basis ()
  step _ := (oracleQuery H).frame Unit

lemma additiveOracleRuntime_eq (H : X → Y) : additiveOracleRuntime H = oracleRt H := rfl

/-- The oracle port: one query type, no classical result. -/
@[reducible] def portSpec : OracleSpec Unit := fun _ ↦ Unit

/-- QROM programs on the fixed workspace `(X × Y) × E`: instruments on the workspace and calls of
the oracle port (acting on the `X × Y` factor). -/
abbrev QProg (X Y E : Type) [Fintype X] [Fintype Y] [Fintype E] (α : Type) : Type :=
  QOC ((X × Y) × E) portSpec α

/-! ## Part-2 semantics as a weight functional -/

section leafW

universe uL

variable {L : LocalSig.{uL, 0}} {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec)
  (I : L.Interp) {A : QReg}

/-- Total weight of the leaves with output in `Ev`, for the program `x` run against the runtime
`R` from the joint (program register × runtime register) matrix `M`. -/
noncomputable def leafW (x : QuantumComp L spec (fun _ ↦ α) A) (M : Matrix (A × R.D) (A × R.D) ℂ)
    (Ev : α → Prop) [DecidablePred Ev] : ℝ≥0∞ :=
  ∑' p : Σ _u : QReg, α, if Ev p.2 then ENNReal.ofReal ((R.run I x).branch p M).trace.re else 0

lemma leafW_pure (a : α) (M : Matrix (A × R.D) (A × R.D) ℂ) (Ev : α → Prop) [DecidablePred Ev] :
    leafW R I (QuantumComp.pure (L := L) (spec := spec) (X := fun _ ↦ α) a) M Ev =
      if Ev a then ENNReal.ofReal M.trace.re else 0 := by
  unfold leafW
  rw [tsum_eq_single (⟨A, a⟩ : Σ _u : QReg, α)]
  · simp
  · intro p hp
    rw [QuantumRuntime.run_pure, DSubInstrument.branch_ret_of_ne _ hp]
    simp

/-- The weight functional of a step with finitely many outcomes followed by continuations. -/
lemma leafW_bind_aux {ι : Type} [Fintype ι] {B : ι → QReg}
    (p : DSubInstrument (A × R.D) ι fun i ↦ B i × R.D)
    (k : (i : ι) → QuantumComp L spec (fun _ ↦ α) (B i))
    (M : Matrix (A × R.D) (A × R.D) ℂ) (hM : M.PosSemidef) (Ev : α → Prop) [DecidablePred Ev] :
    (∑' q : Σ _u : QReg, α, if Ev q.2 then
        ENNReal.ofReal ((p.bind fun i ↦ R.run I (k i)).branch q M).trace.re else 0) =
      ∑ i, leafW R I (k i) (p.branch i M) Ev := by
  unfold leafW
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  refine tsum_congr fun q ↦ ?_
  by_cases hq : Ev q.2
  · simp only [hq, ite_true]
    rw [DSubInstrument.branch_bind_apply_univ, LinearMap.sum_apply, Matrix.trace_sum,
      Complex.re_sum, ENNReal.ofReal_sum_of_nonneg]
    · rfl
    · intro i _
      exact (((R.run I (k i)).isCP_branch q).posSemidef
        ((p.isCP_branch i).posSemidef hM)).trace_re_nonneg
  · simp [hq]

end leafW

/-! ## Part 2: the VCVio program of a QROM program -/

/-- The program register `(X × Y) × E`. -/
abbrev progReg (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype E]
    [DecidableEq E] : QReg := QReg.of ((X × Y) × E)

/-- The Part-1 workspace of a compiled program: the program register next to the (trivial)
private register of the oracle runtime. -/
abbrev WS (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype E]
    [DecidableEq E] : Type := progReg X Y E × QReg.of Unit

/-- The identity splitting of the program register into the oracle's input register `X × Y` and
the rest `E`. -/
def idSplit (X Y E : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype E]
    [DecidableEq E] : progReg X Y E ≃ (qromSpec X Y).In () × QReg.of E :=
  Equiv.refl _

/-- The local operation of an instrument node. -/
@[reducible] def instrOp (j : InstrIdx ((X × Y) × E)) :
    (LocalSig.instruments.{0}).Op (progReg X Y E) :=
  ⟨Fin (j.1 + 1), fun _ ↦ progReg X Y E, j.2.1⟩

/-- The VCVio quantum query program of a QROM program: instrument nodes are local operations,
port calls are oracle calls on the `X × Y` factor. -/
noncomputable def toQC (P : QProg X Y E α) :
    QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ α) (progReg X Y E) :=
  OracleComp.construct
    (C := fun _ ↦ QuantumComp LocalSig.instruments.{0} (qromSpec X Y) (fun _ ↦ α)
      (progReg X Y E))
    (fun a ↦ QuantumComp.pure a)
    (fun t _ ih ↦
      match t, ih with
      | .inl j, ih => QuantumComp.primBind (instrOp j) fun b ↦ ih b
      | .inr (), ih => QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E)
          (idSplit X Y E) fun _ ↦ ih ()) P

lemma toQC_pure (a : α) : toQC (pure a : QProg X Y E α) = QuantumComp.pure a := rfl

lemma toQC_instr_bind (j : InstrIdx ((X × Y) × E)) (k : Fin (j.1 + 1) → QProg X Y E α) :
    toQC (liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inl j)) >>= k) =
      QuantumComp.primBind (instrOp j) fun b ↦ toQC (k b) := rfl

lemma toQC_port_bind (k : Unit → QProg X Y E α) :
    toQC (liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inr ())) >>= k) =
      QuantumComp.queryBind (spec := qromSpec X Y) () (QReg.of E) (idSplit X Y E)
        fun _ ↦ toQC (k ()) := rfl

/-! ## Part 1: the compiled machine -/

/-- An instrument on the workspace, on the workspace next to the trivial runtime register. -/
@[reducible] noncomputable def framedIdx (j : InstrIdx ((X × Y) × E)) : InstrIdx (WS X Y E) :=
  ⟨j.1, (LocalSig.Interp.instruments (instrOp j)).frame (QReg.of Unit),
    DSubInstrument.Lossless.frame j.2.2 (QReg.of Unit)⟩

lemma fin1_bijective : Function.Bijective (fun _ : Fin (0 + 1) ↦ ()) :=
  ⟨fun a b _ ↦ Fin.ext (by have := a.2; have := b.2; omega), fun _ ↦ ⟨0, rfl⟩⟩

/-- VCVio's oracle call of `H` on the program register next to the trivial runtime register:
`queryStep` of `additiveOracleRuntime H` at the identity splitting — the unitary
`U_H |x, y⟩ = |x, y + H x⟩` on the `X × Y` factor. -/
noncomputable def portStep (H : X → Y) :=
  (oracleRt H).queryStep (A := progReg X Y E) () (QReg.of E) (idSplit X Y E)

lemma lossless_portStep (H : X → Y) : (portStep (E := E) H).Lossless := by
  have hi : ((oracleRt H).step ()).Lossless := lossless_additiveOracleRuntime_step H ()
  unfold portStep
  exact QuantumRuntime.lossless_queryStep (oracleRt H) hi (QReg.of E) (idSplit X Y E)

/-- The oracle call of `H` as an instrument node of the Part-1 model (outcome type `Fin 1`). -/
noncomputable def portInstr (H : X → Y) : SubInstrument (WS X Y E) (WS X Y E) (Fin (0 + 1)) :=
  (portStep (E := E) H).comap (fun _ : Fin (0 + 1) ↦ ()) fin1_bijective.injective

lemma lossless_portInstr (H : X → Y) : (portInstr (E := E) H).Lossless :=
  DSubInstrument.Lossless.comap (lossless_portStep H) fin1_bijective

/-- Index of the oracle-call instrument. -/
@[reducible] noncomputable def portIdx (H : X → Y) : InstrIdx (WS X Y E) :=
  ⟨0, portInstr H, lossless_portInstr H⟩

/-- The handler compiling a QROM program for the function `H`. -/
noncomputable def compileImpl (H : X → Y) :
    QueryImpl (instrSpec ((X × Y) × E) + portSpec) (Closed (WS X Y E))
  | .inl j => liftM ((instrSpec (WS X Y E) + unifSpec).query (Sum.inl (framedIdx j)))
  | .inr () => (fun _ ↦ ()) <$>
      (liftM ((instrSpec (WS X Y E) + unifSpec).query (Sum.inl (portIdx H))) :
        Closed (WS X Y E) _)

/-- **The Part-1 machine of a QROM program for the function `H`**: every port call is replaced
by the instrument `U_H` on the workspace.  A closed machine in the model of `Model.lean`. -/
noncomputable def compile (H : X → Y) (P : QProg X Y E α) : Closed (WS X Y E) α :=
  simulateQ (compileImpl H) P

@[simp] lemma compile_pure (H : X → Y) (a : α) :
    compile H (pure a : QProg X Y E α) = pure a := by
  simp [compile]

lemma compile_instr_bind (H : X → Y) (j : InstrIdx ((X × Y) × E))
    (k : Fin (j.1 + 1) → QProg X Y E α) :
    compile H (liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inl j)) >>= k) =
      liftM ((instrSpec (WS X Y E) + unifSpec).query (Sum.inl (framedIdx j))) >>=
        fun i ↦ compile H (k i) := by
  unfold compile
  rw [simulateQ_bind, simulateQ_spec_query]
  rfl

lemma compile_port_bind (H : X → Y) (k : Unit → QProg X Y E α) :
    compile H (liftM ((instrSpec ((X × Y) × E) + portSpec).query (Sum.inr ())) >>= k) =
      liftM ((instrSpec (WS X Y E) + unifSpec).query (Sum.inl (portIdx H))) >>=
        fun _ ↦ compile H (k ()) := by
  unfold compile
  rw [simulateQ_bind, simulateQ_spec_query]
  change ((fun _ ↦ ()) <$> _) >>= _ = _
  simp

/-! ## The semantic equation -/

/-- **Bridge, matrix form.**  For every QROM program, function `H` and positive semidefinite
joint matrix `M`, the Part-2 leaf weight of the VCVio program equals the Part-1 Born weight of the
compiled machine. -/
theorem leafW_toQC_eq_qWeight_compile (H : X → Y) (Ev : α → Prop) [DecidablePred Ev]
    (P : QProg X Y E α) (M : Matrix (WS X Y E) (WS X Y E) ℂ) (hM : M.PosSemidef) :
    leafW (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments (toQC P) M Ev =
      qWeight Ev (compile H P) M := by
  induction P using OracleComp.inductionOn generalizing M with
  | pure a =>
    rw [toQC_pure, compile_pure, qWeight_pure]
    exact leafW_pure (oracleRt H) LocalSig.Interp.instruments a M Ev
  | query_bind t k ih =>
    rcases t with j | ⟨⟩
    · rw [toQC_instr_bind, compile_instr_bind, qWeight_instr_bind]
      have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
        ((LocalSig.Interp.instruments (instrOp j)).frame (QReg.of Unit))
        (fun b ↦ toQC (k b)) M hM Ev
      refine Eq.trans h ?_
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      exact ih i _ (((framedIdx j).2.1.isCP_branch i).posSemidef hM)
    · rw [toQC_port_bind, compile_port_bind, qWeight_instr_bind]
      have h := leafW_bind_aux (A := progReg X Y E) (oracleRt H) LocalSig.Interp.instruments
        (portStep (E := E) H) (fun _ ↦ toQC (k ())) M hM Ev
      rw [Fintype.sum_unique] at h
      refine Eq.trans h ?_
      change _ = ∑ i : Fin (0 + 1), qWeight Ev (compile H (k ())) ((portInstr H).branch i M)
      rw [Fin.sum_univ_one]
      exact ih () _ (((portStep (E := E) H).isCP_branch ()).posSemidef hM)

/-- **Bridge.**  The Part-2 probability (`PQ.QROM.qprob`: the VCVio program `toQC P` run against
the oracle unitary of `H` from the substate `ρ`) of an event on the output equals the Part-1 Born
weight (`qWeight`) of the compiled machine `compile H P` started in `ρ ⊗ |()⟩⟨()|`. -/
theorem qprob_toQC_eq_qWeight_compile (H : X → Y) (Ev : α → Prop) [DecidablePred Ev]
    (P : QProg X Y E α) (ρ : SubState ((X × Y) × E)) :
    PQ.QROM.qprob LocalSig.Interp.instruments H (toQC P) ρ (fun p ↦ Ev p.2) =
      qWeight Ev (compile H P) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix) := by
  have hM : (ρ.matrix ⊗ₖ (SubState.basis ()).matrix).PosSemidef :=
    (ρ.prod (SubState.basis ())).posSemidef
  rw [← leafW_toQC_eq_qWeight_compile H Ev P _ hM]
  unfold PQ.QROM.qprob
  rw [additiveOracleRuntime_eq, QuantumRuntime.evalDistMap_apply _ _ _ _ _
    (MeasurableSet.of_discrete)]
  unfold leafW
  refine tsum_congr fun p ↦ ?_
  rw [QuantumRuntime.matrix_jointPost]
  by_cases hp : Ev p.2 <;> simp [hp, Set.indicator]

end PQ.Interactive

open PQ.Interactive in
#print axioms leafW_toQC_eq_qWeight_compile
open PQ.Interactive in
#print axioms qprob_toQC_eq_qWeight_compile
