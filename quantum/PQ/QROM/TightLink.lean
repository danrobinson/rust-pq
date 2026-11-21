import PQ.QROM.TightInstances
import PQ.QROM.NonVacuity
import QuantumFoundations.Pure.Instrument

/-!
# The tight bounds for VCVio programs: unitary circuits as `QuantumComp`

`PQ/QROM/TightCore.lean` proves the second-order bound `8 q² ε` in a pure-state vector model
(`QAlg`, `acc`).  The other QROM bounds of this project are about VCVio programs
(`qprob I H x ρ E` for `x : QuantumComp L (qromSpec X Y) W A`, `QueryBounded x q`).  This file
closes the gap for the sub-class of all `q`-query **unitary circuits with a final
computational-basis measurement**:

* `circuitComb ψ hψ U hU q p : QuantumComb ((X × Y) × Wk) Bool q`: initial pure state `|ψ⟩⟨ψ|`,
  steps the unitary channels of arbitrary unitary matrices `U 0, …, U q`, final projective
  measurement of an arbitrary predicate `p` of the basis; `circuitProg` is its VCVio program
  (`QuantumComb.toComp`, queries on the factor `X × Y` of the register), and
  `queryBounded_circuitProg : QueryBounded (circuitProg …) q`.
* `traceRight_post_combQuery_ofVector`: one oracle call of the program model against
  `additiveOracleRuntime H` acts on a pure state as `(stdOracle X Y Wk).O H`, i.e.
  `oracleUnitary H ⊗ 1`.
* `traceRight_stateAfterStep`: the state of the program after step `i` is the pure state of the
  vector `(QAlg.ofUnitaries ψ hψ U hU).state (stdOracle X Y Wk) H i`.
* `qprob_circuitProg_true` (**link theorem**):
  `(qprob .instruments H (circuitProg …) |ψ⟩⟨ψ| (outputs true)).toReal =
     (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle X Y Wk) q (measProj p) H`.
* `prf_tight_qprob`, `ud_tight_qprob`, `dspr_tight_qprob`, `dspr_tight_adv_qprob`: the tight
  bounds as statements about `qprob` of these programs — the same objects, the same experiments
  and the same events as `prf_qprob_real_le_ideal_add`, `ud_qprob_real_le_ideal_add`,
  `dspr_qprob_le` of `PQ/QROM/Distinguish.lean` (with probabilities read in `ℝ`).

Since `Wk` is an arbitrary finite workspace and the `U t` are arbitrary unitaries, this is the
standard model of a `q`-query quantum algorithm (Boneh et al.); a general two-outcome projective
measurement is a basis measurement after a unitary.

## General adaptive / mixed programs

The tight bounds for **all** VCVio programs (intermediate measurements with classical control,
arbitrary local instruments, mixed input, varying numbers of queries per path) are proved in
`PQ/QROM/PurifyTight.lean` (`qprob_tight_avg`) and `PQ/QROM/PurifyInstances.lean`
(`prf_tight_program`, `ud_tight_program`, `dspr_tight_program`, `dspr_tight_adv_program`), by a
direct induction over the program in which the run on a pure vector is a branch sum over Kraus
operators.  The theorems of this file are the special case of unitary circuits, kept because they
identify `qprob` with the acceptance probability `acc` of the circuit model.

What is still not formalised is the *representation* statement itself (a purification lemma:
every program has the same acceptance probabilities as ONE `QAlg` with a single final contraction
on a larger space).  It is not needed for the bounds.
-/

open Quantum Matrix MeasureTheory ENNReal
open scoped Kronecker ComplexOrder Matrix.Norms.L2Operator

set_option linter.unusedSectionVars false

namespace PQ.QROM.Tight

variable {X Y Wk : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype Wk] [DecidableEq Wk]

theorem traceRight_post_combQuery_apply (H : X → Y) (σ : SubState (Reg X Y Wk × (additiveOracleRuntime H).D))
    (m m' : Reg X Y Wk) :
    (((additiveOracleRuntime H).combQuery () (QReg.of Wk) (Equiv.refl (Reg X Y Wk))
        (Equiv.refl (Reg X Y Wk))).post σ ()).traceRight.matrix m m' =
      σ.traceRight.matrix ((m.1.1, m.1.2 - H m.1.1), m.2) ((m'.1.1, m'.1.2 - H m'.1.1), m'.2) := by
  rw [SubState.matrix_traceRight, SubState.matrix_traceRight, DSubInstrument.matrix_post,
    QuantumRuntime.combQuery, DSubInstrument.branch_bind_unit, LinearMap.comp_apply,
    QuantumRuntime.queryStep_branch_apply]
  simp only [MatrixMap.traceRight_apply, DSubInstrument.branch_frame_apply,
    SubInstrument.relabel_branch_apply, MatrixMap.amplify_apply, Matrix.submatrix_apply,
    additiveOracleRuntime_step]
  refine (Fintype.sum_unique (ι := Unit) _).trans ?_
  refine Eq.trans ?_ (Fintype.sum_unique (ι := Unit) _).symm
  obtain ⟨⟨x, y⟩, u⟩ := m
  obtain ⟨⟨x', y'⟩, u'⟩ := m'
  change (((oracleQuery H).branch ()).amplify Unit).amplify Wk
    (σ.matrix.submatrix
      (QuantumRuntime.queryEquivIn (Equiv.refl (Reg X Y Wk)) Unit).symm
      (QuantumRuntime.queryEquivIn (Equiv.refl (Reg X Y Wk)) Unit).symm)
    (((x, y), ()), u) (((x', y'), ()), u') = _
  rw [MatrixMap.amplify_apply, MatrixMap.amplify_apply, branch_oracleQuery_apply,
    conj_oracleUnitary_apply]
  rfl

/-- Tracing out the ancilla commutes with a framed step. -/
theorem traceRight_post_frame {A B R : Type} [Fintype A] [Fintype B] [Fintype R]
    (s : SubInstrument A B Unit) (σ : SubState (A × R)) :
    ((s.frame R).post σ ()).traceRight = s.post σ.traceRight () := by
  refine SubState.ext ?_
  rw [SubState.matrix_traceRight, DSubInstrument.matrix_post, DSubInstrument.branch_frame_apply,
    DSubInstrument.matrix_post, SubState.matrix_traceRight, ← LinearMap.comp_apply,
    MatrixMap.traceRight_comp_amplify, LinearMap.comp_apply]

/-- **One oracle call of the program model is one application of `O_H` of the vector model.** -/
theorem traceRight_post_combQuery_ofVector (H : X → Y)
    (σ : SubState (Reg X Y Wk × (additiveOracleRuntime H).D))
    (φ : EuclideanSpace ℂ (Reg X Y Wk)) (hφ : ‖φ‖ ≤ 1) (hσ : σ.traceRight = SubState.ofVector φ hφ)
    (h : ‖(stdOracle X Y Wk).O H φ‖ ≤ 1) :
    (((additiveOracleRuntime H).combQuery () (QReg.of Wk) (Equiv.refl (Reg X Y Wk))
        (Equiv.refl (Reg X Y Wk))).post σ ()).traceRight =
      SubState.ofVector ((stdOracle X Y Wk).O H φ) h := by
  refine SubState.ext ?_
  ext m m'
  rw [traceRight_post_combQuery_apply, hσ, SubState.matrix_ofVector, SubState.matrix_ofVector,
    ketBra_apply, ketBra_apply]
  have e : ∀ i : Reg X Y Wk, ((stdOracle X Y Wk).O H φ).ofLp i =
      φ.ofLp ((i.1.1, i.1.2 - H i.1.1), i.2) := fun i ↦ oracle_apply H φ i
  rw [e, e]

section Comb

variable {n : Type} [Fintype n] [DecidableEq n]

/-- The two projections of the computational-basis measurement of a predicate `p`. -/
noncomputable def measMat (p : n → Prop) [DecidablePred p] (b : Bool) : Matrix n n ℂ :=
  Matrix.diagonal fun i ↦ if decide (p i) = b then 1 else 0

theorem isStarProjection_measMat (p : n → Prop) [DecidablePred p] (b : Bool) :
    IsStarProjection (measMat p b) := by
  refine ⟨?_, ?_⟩
  · rw [IsIdempotentElem, measMat, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    split_ifs <;> simp
  · rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, measMat, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp only [Pi.star_apply]
    split_ifs <;> simp

theorem sum_measMat (p : n → Prop) [DecidablePred p] : ∑ b, measMat p b = 1 := by
  rw [Fintype.sum_bool, measMat, measMat, Matrix.diagonal_add, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : p i <;> simp [h]

theorem measMat_true (p : n → Prop) [DecidablePred p] (φ : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (measMat p true) φ = measProj p φ := by
  have : measMat p true = Matrix.diagonal fun i ↦ if p i then (1 : ℂ) else 0 := by
    rw [measMat]
    congr 1
    funext i
    by_cases h : p i <;> simp [h]
  rw [this]
  rfl

theorem measMat_false (p : n → Prop) [DecidablePred p] (φ : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (measMat p false) φ = measProj (fun i ↦ ¬ p i) φ := by
  have : measMat p false = Matrix.diagonal fun i ↦ if ¬ p i then (1 : ℂ) else 0 := by
    rw [measMat]
    congr 1
    funext i
    by_cases h : p i <;> simp [h]
  rw [this]
  rfl

/-- The `q`-query unitary circuit `U_q O U_{q-1} … O U_0 |ψ⟩` with a final computational-basis
measurement of the predicate `p` (output `true` iff `p` holds), as a VCVio `QuantumComb`. -/
noncomputable def circuitComb (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ ≤ 1) (U : ℕ → Matrix n n ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ) (q : ℕ) (p : n → Prop) [DecidablePred p] :
    QuantumComb n Bool q where
  init := SubState.ofVector ψ hψ
  step i := SubInstrument.ofContraction (U i) (l2_opNorm_le_one_of_mem_unitaryGroup (hU i))
  lossless_step i := SubInstrument.lossless_ofContraction _ (Matrix.mem_unitaryGroup_iff'.1 (hU i))
  final := SubInstrument.ofProjective (measMat p) (isStarProjection_measMat p) (sum_measMat p)
  lossless_final := SubInstrument.lossless_ofProjective _ _ _

end Comb

section Link

variable (ψ : EuclideanSpace ℂ (Reg X Y Wk)) (hψ : ‖ψ‖ ≤ 1)
  (U : ℕ → Matrix (Reg X Y Wk) (Reg X Y Wk) ℂ)
  (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Reg X Y Wk) ℂ) (q : ℕ)
  (p : Reg X Y Wk → Prop) [DecidablePred p]

/-- **State correspondence.**  After step `i` of the comb run against the oracle runtime of `H`,
the comb's register is in the pure state of the vector `ψ_i^H` of the circuit model. -/
theorem traceRight_stateAfterStep (H : X → Y) (i : Fin (q + 1)) :
    ((((circuitComb ψ hψ U hU q p).frame (additiveOracleRuntime H).D
        (additiveOracleRuntime H).init).stateAfterStep
          ((additiveOracleRuntime H).combQuery () (QReg.of Wk) (Equiv.refl (Reg X Y Wk))
            (Equiv.refl (Reg X Y Wk)))) i).traceRight =
      SubState.ofVector ((QAlg.ofUnitaries ψ hψ U hU).state (stdOracle X Y Wk) H i)
        ((QAlg.ofUnitaries ψ hψ U hU).norm_state_le (stdOracle X Y Wk) H i) := by
  induction i using Fin.induction with
  | zero =>
    rw [QuantumComb.stateAfterStep_zero]
    change (((SubInstrument.ofContraction (U 0)
      (l2_opNorm_le_one_of_mem_unitaryGroup (hU 0))).frame _).post
      ((SubState.ofVector ψ hψ).prod (SubState.basis ())) ()).traceRight = _
    rw [traceRight_post_frame, SubState.traceRight_prod _ (by simp [SubState.matrix_basis]),
      SubInstrument.post_ofContraction_ofVector]
    rfl
  | succ i ih =>
    rw [QuantumComb.stateAfterStep_succ]
    change (((SubInstrument.ofContraction (U (i.succ : ℕ))
      (l2_opNorm_le_one_of_mem_unitaryGroup (hU _))).frame _).post _ ()).traceRight = _
    rw [traceRight_post_frame,
      traceRight_post_combQuery_ofVector H _ _ _ ih
        (((stdOracle X Y Wk).O_le H _).trans
          ((QAlg.ofUnitaries ψ hψ U hU).norm_state_le (stdOracle X Y Wk) H _)),
      SubInstrument.post_ofContraction_ofVector]
    rfl

/-- The VCVio program of the circuit: a `QuantumComp` over `qromSpec X Y` on the register
`(X × Y) × Wk`, each oracle call acting on the factor `X × Y`, with Boolean output. -/
noncomputable def circuitProg :
    QComp (qromSpec X Y) (QReg.of (Reg X Y Wk)) (QReg.of (Reg X Y Wk)) Bool :=
  (circuitComb ψ hψ U hU q p).toComp (spec := qromSpec X Y) () (QReg.of Wk)
    (Equiv.refl (Reg X Y Wk)) (Equiv.refl (Reg X Y Wk))

/-- The program of a `q`-query circuit is a `q`-query program in the sense of the other QROM
bounds. -/
theorem queryBounded_circuitProg : QueryBounded (circuitProg ψ hψ U hU q p) q :=
  NonVacuity.queryBounded_comb _ _ _ _

/-- The leaf event "the program outputs `b`". -/
def outputs (b : Bool) : (Σ u, QuantumComp₂.Leaf (QReg.of (Reg X Y Wk)) Bool u) → Prop :=
  fun leaf ↦ (QuantumComp₂.leafEquiv (QReg.of (Reg X Y Wk)) Bool).symm leaf = b

/-- **`qprob` of the program = Born weight of the vector model**, for either output. -/
theorem qprob_circuitProg_measMat (H : X → Y) (b : Bool) :
    qprob .instruments H (circuitProg ψ hψ U hU q p) (SubState.ofVector ψ hψ) (outputs b) =
      ENNReal.ofReal (‖Matrix.toEuclideanLin (measMat p b)
        ((QAlg.ofUnitaries ψ hψ U hU).state (stdOracle X Y Wk) H q)‖ ^ 2) := by
  have h1 := NonVacuity.qprob_eq_evalDist₂ .instruments H (circuitProg ψ hψ U hU q p)
    (SubState.ofVector ψ hψ) (fun a : Bool ↦ a = b) (measurableSet_singleton b)
  refine h1.trans ?_
  have h2 := QuantumComb.evalDist_toComp (circuitComb ψ hψ U hU q p) (additiveOracleRuntime H) ()
    (QReg.of Wk) (Equiv.refl (Reg X Y Wk)) (Equiv.refl (Reg X Y Wk))
  rw [QuantumComb.outcomeMeasure_run] at h2
  have h3 := traceRight_stateAfterStep ψ hψ U hU q p H (Fin.last q)
  have h4 : ((circuitComb ψ hψ U hU q p).frame (additiveOracleRuntime H).D
      (additiveOracleRuntime H).init).final =
      (SubInstrument.ofProjective (measMat p) (isStarProjection_measMat p)
        (sum_measMat p)).frame (additiveOracleRuntime H).D := rfl
  rw [h4, DSubInstrument.outcomeMeasure_frame, h3] at h2
  have h5 : {a : Bool | a = b} = {b} := Set.ext fun a ↦ Iff.rfl
  rw [h5]
  refine (congrArg (fun μ ↦ μ {b}) h2).trans ?_
  rw [SubInstrument.outcomeMeasure_ofProjective_ofVector_singleton]
  rfl

/-- **Link theorem.**  The probability that the VCVio program of the circuit outputs `true`,
run from the pure state `|ψ⟩⟨ψ|` against the oracle unitary of `H`, is the acceptance probability
of the circuit in the vector model with the standard oracle. -/
theorem qprob_circuitProg_true (H : X → Y) :
    (qprob .instruments H (circuitProg ψ hψ U hU q p) (SubState.ofVector ψ hψ)
        (outputs true)).toReal =
      (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle X Y Wk) q (measProj p) H := by
  rw [qprob_circuitProg_measMat, measMat_true, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

/-- The same for the output `false`. -/
theorem qprob_circuitProg_false (H : X → Y) :
    (qprob .instruments H (circuitProg ψ hψ U hU q p) (SubState.ofVector ψ hψ)
        (outputs false)).toReal =
      (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle X Y Wk) q (measProj fun i ↦ ¬ p i) H := by
  rw [qprob_circuitProg_measMat, measMat_false, ENNReal.toReal_ofReal (sq_nonneg _)]
  rfl

end Link

/-! ## The tight bounds for programs -/

section Programs

/-- **Tight PRF bound for VCVio programs of unitary circuits.**  Same experiment as
`prf_qprob_real_le_ideal_add`; the program is the `q`-query circuit `circuitProg`. -/
theorem prf_tight_qprob {K D Y Wk : Type} [Fintype K] [DecidableEq K] [Fintype D] [DecidableEq D]
    [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Wk] [DecidableEq Wk] [Nonempty K]
    [Nonempty D]
    (ψ : EuclideanSpace ℂ (Reg ((K × D) ⊕ D) Y Wk)) (hψ : ‖ψ‖ ≤ 1)
    (U : ℕ → Matrix (Reg ((K × D) ⊕ D) Y Wk) (Reg ((K × D) ⊕ D) Y Wk) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Reg ((K × D) ⊕ D) Y Wk) ℂ) (q : ℕ)
    (p : Reg ((K × D) ⊕ D) Y Wk → Prop) [DecidablePred p] :
    |∑ k : K, ∑ F : K × D → Y,
          ((Fintype.card K : ℝ)⁻¹ * (Fintype.card (K × D → Y) : ℝ)⁻¹) *
            (qprob .instruments (prfReal k F) (circuitProg ψ hψ U hU q p)
              (SubState.ofVector ψ hψ) (outputs true)).toReal -
        ∑ F : K × D → Y, ∑ R : D → Y,
          ((Fintype.card (K × D → Y) : ℝ)⁻¹ * (Fintype.card (D → Y) : ℝ)⁻¹) *
            (qprob .instruments (prfIdeal F R) (circuitProg ψ hψ U hU q p)
              (SubState.ofVector ψ hψ) (outputs true)).toReal| ≤
      8 * (q : ℝ) ^ 2 / Fintype.card K := by
  have e : ∀ H : (K × D) ⊕ D → Y,
      (qprob .instruments H (circuitProg ψ hψ U hU q p) (SubState.ofVector ψ hψ)
        (outputs true)).toReal =
      (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle ((K × D) ⊕ D) Y Wk) q (measProj p) H :=
    fun H ↦ qprob_circuitProg_true ψ hψ U hU q p H
  simp only [e]
  exact prf_tight _ _ q _ (norm_measProj_le p)

/-- **Tight multi-target undetectability for VCVio programs of unitary circuits.**  Same
experiment as `ud_qprob_real_le_ideal_add`; the circuit (initial state, gates, measured
predicate) may depend on the targets. -/
theorem ud_tight_qprob {T Msg Y Wk : Type} [Fintype T] [DecidableEq T] [Fintype Msg]
    [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] [Fintype Wk] [DecidableEq Wk]
    [Nonempty T] [Nonempty Msg]
    (ψ : (T → Y) → EuclideanSpace ℂ (Reg (T × Msg) Y Wk)) (hψ : ∀ y, ‖ψ y‖ ≤ 1)
    (U : (T → Y) → ℕ → Matrix (Reg (T × Msg) Y Wk) (Reg (T × Msg) Y Wk) ℂ)
    (hU : ∀ y t, U y t ∈ Matrix.unitaryGroup (Reg (T × Msg) Y Wk) ℂ) (q : ℕ)
    (p : (T → Y) → Reg (T × Msg) Y Wk → Prop) [∀ y, DecidablePred (p y)] :
    |∑ xs : T → Msg, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Msg) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            (qprob .instruments H
              (circuitProg (ψ (udTargets xs H)) (hψ _) (U (udTargets xs H)) (hU _) q
                (p (udTargets xs H)))
              (SubState.ofVector (ψ (udTargets xs H)) (hψ _)) (outputs true)).toReal -
        ∑ y : T → Y, ∑ H : T × Msg → Y,
          ((Fintype.card (T → Y) : ℝ)⁻¹ * (Fintype.card (T × Msg → Y) : ℝ)⁻¹) *
            (qprob .instruments H (circuitProg (ψ y) (hψ y) (U y) (hU y) q (p y))
              (SubState.ofVector (ψ y) (hψ y)) (outputs true)).toReal| ≤
      8 * (q : ℝ) ^ 2 / Fintype.card Msg := by
  have e : ∀ (y : T → Y) (H : T × Msg → Y),
      (qprob .instruments H (circuitProg (ψ y) (hψ y) (U y) (hU y) q (p y))
        (SubState.ofVector (ψ y) (hψ y)) (outputs true)).toReal =
      (QAlg.ofUnitaries (ψ y) (hψ y) (U y) (hU y)).acc (stdOracle (T × Msg) Y Wk) q
        (measProj (p y)) H :=
    fun y H ↦ qprob_circuitProg_true (ψ y) (hψ y) (U y) (hU y) q (p y) H
  simp only [e]
  exact ud_tight (stdOracle (T × Msg) Y Wk) (fun y ↦ QAlg.ofUnitaries (ψ y) (hψ y) (U y) (hU y)) q
    (fun y ↦ measProj (p y)) (fun y ↦ norm_measProj_le (p y))

variable {X Y Wk : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype Wk] [DecidableEq Wk]

/-- For DSPR programs: the probability of answering correctly is the acceptance probability of
the matching outcome in the vector model. -/
theorem qprob_circuitProg_iff (ψ : EuclideanSpace ℂ (Reg X Y Wk)) (hψ : ‖ψ‖ ≤ 1)
    (U : ℕ → Matrix (Reg X Y Wk) (Reg X Y Wk) ℂ)
    (hU : ∀ t, U t ∈ Matrix.unitaryGroup (Reg X Y Wk) ℂ) (q : ℕ)
    (p : Reg X Y Wk → Prop) [DecidablePred p] (H : X → Y) (P : Prop) [Decidable P] :
    (qprob .instruments H (circuitProg ψ hψ U hU q p) (SubState.ofVector ψ hψ)
        (fun leaf ↦ outputs true leaf ↔ P)).toReal =
      if P then (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle X Y Wk) q (measProj p) H
      else (QAlg.ofUnitaries ψ hψ U hU).acc (stdOracle X Y Wk) q (measProj fun i ↦ ¬ p i) H := by
  by_cases hP : P
  · have e : (fun leaf : (Σ u, QuantumComp₂.Leaf (QReg.of (Reg X Y Wk)) Bool u) ↦
        outputs true leaf ↔ P) = outputs true := by
      funext leaf; simp [hP]
    rw [e, qprob_circuitProg_true]
    simp [hP]
  · have e : (fun leaf : (Σ u, QuantumComp₂.Leaf (QReg.of (Reg X Y Wk)) Bool u) ↦
        outputs true leaf ↔ P) = outputs false := by
      funext leaf; simp [hP, outputs]
    rw [e, qprob_circuitProg_false]
    simp [hP]

/-- **Tight DSPR for VCVio programs of unitary circuits.**  Same experiment and event as
`dspr_qprob_le`: the program gets `x` (the circuit may depend on it), outputs a bit, and wins iff
the bit says correctly whether `x` has a second preimage. -/
theorem dspr_tight_qprob (ψ : X → EuclideanSpace ℂ (Reg X Y Wk)) (hψ : ∀ x, ‖ψ x‖ ≤ 1)
    (U : X → ℕ → Matrix (Reg X Y Wk) (Reg X Y Wk) ℂ)
    (hU : ∀ x t, U x t ∈ Matrix.unitaryGroup (Reg X Y Wk) ℂ) (q : ℕ)
    (p : X → Reg X Y Wk → Prop) [∀ x, DecidablePred (p x)] :
    ∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (qprob .instruments H (circuitProg (ψ x) (hψ x) (U x) (hU x) q (p x))
          (SubState.ofVector (ψ x) (hψ x))
          (fun leaf ↦ outputs true leaf ↔ SecondPreimage H x)).toReal ≤
      max (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))
          ((1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1)) +
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  classical
  have e : ∀ (H : X → Y) (x : X),
      (qprob .instruments H (circuitProg (ψ x) (hψ x) (U x) (hU x) q (p x))
        (SubState.ofVector (ψ x) (hψ x))
        (fun leaf ↦ outputs true leaf ↔ SecondPreimage H x)).toReal =
      if SecondPreimage H x then
        (QAlg.ofUnitaries (ψ x) (hψ x) (U x) (hU x)).acc (stdOracle X Y Wk) q (measProj (p x)) H
      else (QAlg.ofUnitaries (ψ x) (hψ x) (U x) (hU x)).acc (stdOracle X Y Wk) q
        (measProj fun i ↦ ¬ p x i) H :=
    fun H x ↦ qprob_circuitProg_iff (ψ x) (hψ x) (U x) (hU x) q (p x) H _
  simp only [e]
  exact dspr_tight (stdOracle X Y Wk) (fun x ↦ QAlg.ofUnitaries (ψ x) (hψ x) (U x) (hU x)) q
    (fun x ↦ measProj (p x)) (fun x ↦ measProj fun i ↦ ¬ p x i)
    (fun x φ ↦ (norm_measProj_add_compl (p x) φ).le)

/-- **Tight DSPR for programs, Bernstein–Hülsing advantage form**, for `|Y| < |X|`. -/
theorem dspr_tight_adv_qprob (ψ : X → EuclideanSpace ℂ (Reg X Y Wk)) (hψ : ∀ x, ‖ψ x‖ ≤ 1)
    (U : X → ℕ → Matrix (Reg X Y Wk) (Reg X Y Wk) ℂ)
    (hU : ∀ x t, U x t ∈ Matrix.unitaryGroup (Reg X Y Wk) ℂ) (q : ℕ)
    (p : X → Reg X Y Wk → Prop) [∀ x, DecidablePred (p x)]
    (hcard : Fintype.card Y < Fintype.card X) :
    max 0 (∑ H : X → Y, ∑ x : X, ((Fintype.card (X → Y) : ℝ)⁻¹ * (Fintype.card X : ℝ)⁻¹) *
        (qprob .instruments H (circuitProg (ψ x) (hψ x) (U x) (hU x) q (p x))
          (SubState.ofVector (ψ x) (hψ x))
          (fun leaf ↦ outputs true leaf ↔ SecondPreimage H x)).toReal -
      (1 - (1 - (Fintype.card Y : ℝ)⁻¹) ^ (Fintype.card X - 1))) ≤
        8 * (q : ℝ) ^ 2 / Fintype.card Y := by
  have h := dspr_tight_qprob ψ hψ U hU q p
  have hp := pow_noSP_le_half (X := X) (Y := Y) hcard
  rw [max_eq_left (by linarith)] at h
  refine max_le (by positivity) ?_
  linarith

end Programs

end PQ.QROM.Tight

#print axioms PQ.QROM.Tight.traceRight_post_combQuery_ofVector
#print axioms PQ.QROM.Tight.traceRight_stateAfterStep
#print axioms PQ.QROM.Tight.queryBounded_circuitProg
#print axioms PQ.QROM.Tight.qprob_circuitProg_true
#print axioms PQ.QROM.Tight.qprob_circuitProg_false
#print axioms PQ.QROM.Tight.prf_tight_qprob
#print axioms PQ.QROM.Tight.ud_tight_qprob
#print axioms PQ.QROM.Tight.dspr_tight_qprob
#print axioms PQ.QROM.Tight.dspr_tight_adv_qprob
