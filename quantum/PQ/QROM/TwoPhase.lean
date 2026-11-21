import PQ.QROM.Hybrid
import PQ.QROM.Average

/-!
# Two-phase QROM experiments: operator-level infrastructure

This file provides what the exact two-phase games (`PQ/QROM/TwoPhaseGame.lean`,
`PQ/QROM/ExactTcr.lean`) need below the level of games.

* `leafProb R I x σ E`: the Born probability that the program `x`, run against the runtime `R`
  from an arbitrary (unnormalised) joint operator `σ` on the program and runtime registers, ends
  in a leaf satisfying `E`; with its behaviour under sequencing (`leafProb_bind`).
* Query weights under sequencing and under changes of unused ports
  (`queryWeight_bind_of_zero`, `queryWeight_eq_zero_of_unused`, `queryWeight_congr_of_unused`).
* `qrom2Spec X Y`, `twoRuntime G`: the two-port hash oracle.  Port `false` is the access of the
  first phase, port `true` the access of the second phase; `twoRuntime G` answers port `b` with
  the oracle unitary of `G b`.  The real game uses the same function on both ports.
* `twoRuntime_sqrt_le`, `twoRuntime_sqrt_le'`: the square-root hybrid bound between two two-port
  runtimes from any positive semidefinite joint operator, with the index masses of one run.
* `HybridModel.ofSecondPort`: a program that only calls port `true`, run from an unnormalised
  joint operator, as a `HybridModel` in the function on port `true` (normalised by the trace of
  the operator).
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

universe u v u₁ v₁ w w₂

namespace PQ.QROM

/-! ## Indicators -/

/-- The indicator of a proposition, in `ℝ≥0∞`. -/
noncomputable def ind (P : Prop) : ℝ≥0∞ := Set.indicator {True} 1 P

theorem ind_of_true {P : Prop} (h : P) : ind P = 1 := by simp [ind, h]

theorem ind_of_false {P : Prop} (h : ¬ P) : ind P = 0 := by simp [ind, h]

theorem ind_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases hp : P
  · rw [ind_of_true hp, ind_of_true (h hp)]
  · rw [ind_of_false hp]; exact zero_le

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  by_cases hp : P
  · rw [ind_of_true hp]
  · rw [ind_of_false hp]; exact zero_le

/-! ## Leaf probabilities from an arbitrary joint operator -/

section Leaf

variable {spec : QuantumOracleSpec.{u₁, v₁}} (R : QuantumRuntime spec) {L : LocalSig.{u, v}}
  (I : L.Interp) {W : QReg → Type w} {W₂ : QReg → Type w₂} {A : QReg}

/-- The probability that `x`, run against `R` from the joint operator `σ` on `A × R.D`, ends in
a leaf satisfying `E`: the sum of the traces of the unnormalised post-states of those leaves. -/
noncomputable def leafProb (x : QuantumComp L spec W A) (σ : Matrix (A × R.D) (A × R.D) ℂ)
    (E : (Σ u, W u) → Prop) : ℝ≥0∞ :=
  ∑' p, ENNReal.ofReal ((R.run I x).branch p σ).trace.re * ind (E p)

/-- From a substate, with the runtime register in its initial state, this is the probability of
the event under `evalDistMap`. -/
theorem evalDistMap_eq_leafProb (x : QuantumComp L spec W A) (ρ : SubState A)
    (E : (Σ u, W u) → Prop) :
    R.evalDistMap I x ρ E {True} = leafProb R I x (ρ.matrix ⊗ₖ R.init.matrix) E :=
  R.evalDistMap_apply I x ρ E (MeasurableSet.singleton True)

variable {R I}

theorem leafProb_mono (x : QuantumComp L spec W A) (σ : Matrix (A × R.D) (A × R.D) ℂ)
    {E E' : (Σ u, W u) → Prop} (h : ∀ p, E p → E' p) :
    leafProb R I x σ E ≤ leafProb R I x σ E' :=
  tsum_le_tsum fun p ↦ mul_le_mul' le_rfl (ind_mono (h p))

theorem leafProb_le (x : QuantumComp L spec W A) {σ : Matrix (A × R.D) (A × R.D) ℂ}
    (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    leafProb R I x σ E ≤ ENNReal.ofReal σ.trace.re :=
  (tsum_le_tsum fun _ ↦ (mul_le_mul' le_rfl (ind_le_one _)).trans (mul_one _).le).trans
    ((R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hσ)

/-- The weights of all leaves add up to at most the trace of the input. -/
theorem tsum_leaf_le (x : QuantumComp L spec W A) {σ : Matrix (A × R.D) (A × R.D) ℂ}
    (hσ : σ.PosSemidef) :
    ∑' p, ENNReal.ofReal ((R.run I x).branch p σ).trace.re ≤ ENNReal.ofReal σ.trace.re :=
  (R.run I x).isCPTNIFamily.tsum_ofReal_trace_re_le hσ

theorem leafProb_pure (y : W A) (σ : Matrix (A × R.D) (A × R.D) ℂ) (E : (Σ u, W u) → Prop) :
    leafProb R I (QuantumComp.pure (L := L) (spec := spec) y) σ E =
      ENNReal.ofReal σ.trace.re * ind (E ⟨A, y⟩) := by
  unfold leafProb
  rw [QuantumRuntime.run_pure, tsum_eq_single (⟨A, y⟩ : Σ u, W u) fun _ hp ↦ by
    rw [DSubInstrument.branch_ret_of_ne _ hp]; simp]
  rw [DSubInstrument.branch_ret_self, LinearMap.id_apply]

/-- **Sequencing.** The probability of an event of `x.bind k` sums, over the leaves `p` of `x`,
the probability of the event for the continuation run from the post-state of `p`. -/
theorem leafProb_bind (x : QuantumComp L spec W A) (k : ∀ u, W u → QuantumComp L spec W₂ u)
    {σ : Matrix (A × R.D) (A × R.D) ℂ} (hσ : σ.PosSemidef) (E : (Σ u, W₂ u) → Prop) :
    leafProb R I (x.bind k) σ E =
      ∑' p, leafProb R I (k p.1 p.2) ((R.run I x).branch p σ) E := by
  unfold leafProb
  rw [tsum_comm]
  refine tsum_congr fun c ↦ ?_
  have h := Matrix.ofReal_trace_re_tsum
    (((R.run I x).isCPTNIFamily.comp_eval
      (fun p ↦ (R.run I (k p.1 p.2)).isCPTNIFamily) c).summable_apply σ)
    (fun p ↦ (R.run I (k p.1 p.2)).posSemidef_branch_apply c
      ((R.run I x).posSemidef_branch_apply p hσ))
  simp only [LinearMap.comp_apply] at h
  rw [QuantumRuntime.run_bind, DSubInstrument.branch_bind_apply, h, ENNReal.tsum_mul_right]

/-- The events `out = k` have total probability at most the trace of the input. -/
theorem sum_leafProb_eq_le {K : Type} [Fintype K] [DecidableEq K]
    (x : QuantumComp L spec W A) {σ : Matrix (A × R.D) (A × R.D) ℂ} (hσ : σ.PosSemidef)
    (out : (Σ u, W u) → K) :
    ∑ k, leafProb R I x σ (fun p ↦ out p = k) ≤ ENNReal.ofReal σ.trace.re := by
  unfold leafProb
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine le_trans (le_of_eq (tsum_congr fun p ↦ ?_)) (tsum_leaf_le (I := I) x hσ)
  rw [← Finset.mul_sum, Finset.sum_eq_single (out p)]
  · rw [ind_of_true rfl, mul_one]
  · intro k _ hk
    exact ind_of_false (Ne.symm hk)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem leafProb_mem_le_sum {K : Type} [DecidableEq K]
    (x : QuantumComp L spec W A) (σ : Matrix (A × R.D) (A × R.D) ℂ)
    (out : (Σ u, W u) → K) (T : Finset K) :
    leafProb R I x σ (fun p ↦ out p ∈ T) ≤ ∑ k ∈ T, leafProb R I x σ (fun p ↦ out p = k) := by
  unfold leafProb
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine tsum_le_tsum fun p ↦ ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  by_cases h : out p ∈ T
  · rw [Finset.sum_eq_single_of_mem (out p) h]
    · rw [ind_of_true h, ind_of_true rfl]
    · intro k _ hk
      exact ind_of_false (Ne.symm hk)
  · rw [ind_of_false h]; exact zero_le

end Leaf

/-! ## Query weights: sequencing and unused ports -/

section Weights

variable {spec : QuantumOracleSpec.{u₁, v₁}} {L : LocalSig.{u, v}} (I : L.Interp)
  {W : QReg → Type w} {W₂ : QReg → Type w₂} {A : QReg}

/-- A weight that vanishes on every port the program may call gives weight zero. -/
theorem queryWeight_eq_zero_of_unused (R : QuantumRuntime spec)
    {wt : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    {x : QuantumComp L spec W A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hw : ∀ i, b i ≠ 0 → ∀ σ, wt i σ = 0) (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I wt x ρ j = 0 := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rfl
  | primBind _ o k ih =>
    rw [QuantumComp.isQueryBound_primBind_iff] at hx
    rw [QuantumRuntime.queryWeight_primBind]
    simp only [fun c ↦ ih c (hx c), tsum_zero]
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hb, hk⟩ := hx.of_queryBind
    cases j with
    | zero => rw [QuantumRuntime.queryWeight_queryBind_zero]; exact hw i hb.ne' _
    | succ j =>
      rw [QuantumRuntime.queryWeight_queryBind_succ]
      simp only [fun r ↦ ih r (hk r), tsum_zero]

/-- If the continuations carry no weight, the weights of `x.bind k` are those of `x`. -/
theorem queryWeight_bind_of_zero (R : QuantumRuntime spec)
    {wt : ∀ i, Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ → ℝ≥0∞}
    (x : QuantumComp L spec W A) (k : ∀ u, W u → QuantumComp L spec W₂ u)
    (hk : ∀ u y σ j, R.queryWeight I wt (k u y) σ j = 0)
    (ρ : Matrix (A × R.D) (A × R.D) ℂ) (j : ℕ) :
    R.queryWeight I wt (x.bind k) ρ j = R.queryWeight I wt x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ y => rw [QuantumComp.pure_bind, hk, QuantumRuntime.queryWeight_pure]
  | primBind _ o k' ih =>
    rw [QuantumComp.primBind_bind, QuantumRuntime.queryWeight_primBind,
      QuantumRuntime.queryWeight_primBind]
    exact tsum_congr fun c ↦ ih c _ j
  | queryBind _ i E ℓ k' ih =>
    rw [QuantumComp.queryBind_bind]
    cases j with
    | zero =>
      rw [QuantumRuntime.queryWeight_queryBind_zero, QuantumRuntime.queryWeight_queryBind_zero]
    | succ j =>
      rw [QuantumRuntime.queryWeight_queryBind_succ, QuantumRuntime.queryWeight_queryBind_succ]
      exact tsum_congr fun r ↦ ih r _ j

/-- **Unused ports do not matter** for query weights: two runtimes on the same register whose
steps agree on every port with a nonzero budget give every program within that budget the same
weights. -/
theorem queryWeight_congr_of_unused {D : QReg} {σ₁ σ₂ : SubState D}
    {s₁ s₂ : ∀ i, SubInstrument (spec.In i × D) (spec.Out i × D) (spec.Result i)}
    {wt : ∀ i, Matrix (spec.In i × D) (spec.In i × D) ℂ → ℝ≥0∞}
    {x : QuantumComp L spec W A} {b : spec.Port → ℕ} (hx : x.IsQueryBound b)
    (hs : ∀ i, b i ≠ 0 → s₁ i = s₂ i) (ρ : Matrix (A × D) (A × D) ℂ) (j : ℕ) :
    (QuantumRuntime.mk D σ₁ s₁).queryWeight I wt x ρ j =
      (QuantumRuntime.mk D σ₂ s₂).queryWeight I wt x ρ j := by
  induction x using QuantumComp.inductionOn generalizing j with
  | pure _ _ => rw [QuantumRuntime.queryWeight_pure, QuantumRuntime.queryWeight_pure]
  | primBind _ o k ih =>
    rw [QuantumComp.isQueryBound_primBind_iff] at hx
    rw [QuantumRuntime.queryWeight_primBind, QuantumRuntime.queryWeight_primBind]
    exact tsum_congr fun c ↦ ih c (hx c) _ j
  | queryBind _ i E ℓ k ih =>
    obtain ⟨hb, hk⟩ := hx.of_queryBind
    cases j with
    | zero =>
      rw [QuantumRuntime.queryWeight_queryBind_zero, QuantumRuntime.queryWeight_queryBind_zero]
    | succ j =>
      rw [QuantumRuntime.queryWeight_queryBind_succ, QuantumRuntime.queryWeight_queryBind_succ]
      have hstep : (QuantumRuntime.mk D σ₁ s₁).queryStep i E ℓ =
          (QuantumRuntime.mk D σ₂ s₂).queryStep i E ℓ := by
        simp only [QuantumRuntime.queryStep, hs i hb.ne']
      rw [hstep]
      exact tsum_congr fun r ↦ ih r (hk r) _ j

end Weights

/-! ## The two-port hash oracle -/

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The signature of a hash oracle with two ports, both on the register `X × Y` (query input,
then response): port `false` is the access of the first phase of a two-phase adversary, port
`true` the access of its second phase.  The signature names no function. -/
@[reducible]
def qrom2Spec (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] :
    QuantumOracleSpec.{0, 0} where
  Port := Bool
  In _ := QReg.of (X × Y)
  Out _ := QReg.of (X × Y)
  Result _ := Unit

/-- The projection `|k⟩⟨k| ⊗ 1_Y` on the register of either port. -/
noncomputable def block2 (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (i : (qrom2Spec X Y).Port) (k : X) :
    Matrix ((qrom2Spec X Y).In i) ((qrom2Spec X Y).In i) ℂ :=
  inputBlock X Y () k

theorem isCoherentIndex_block2 :
    Hybrid.IsCoherentIndex (spec := qrom2Spec X Y) (κ := fun _ ↦ X) (block2 X Y)
      (block2 X Y) where
  sum_eq_one _ := sum_inputBlock ()
  mul_self _ k := inputBlock_mul_self () k
  conjTranspose_mul_of_ne _ a b hab := by
    unfold block2
    rw [inputBlock_conjTranspose]
    exact inputBlock_mul_of_ne () hab

theorem sum_conjTranspose_block2_mul (i : (qrom2Spec X Y).Port) :
    ∑ k, (block2 X Y i k)ᴴ * block2 X Y i k = 1 :=
  sum_conjTranspose_inputBlock_mul ()

variable [AddCommGroup Y]

/-- The runtime answering port `b` with the oracle unitary of `G b`, with no private memory.
The real two-phase game uses `fun _ ↦ Th`. -/
@[reducible]
noncomputable def twoRuntime (G : Bool → X → Y) : QuantumRuntime (qrom2Spec X Y) where
  D := QReg.of Unit
  init := SubState.basis ()
  step b := (oracleQuery (G b)).frame Unit

/-- The Kraus operator of the step of `twoRuntime G` on port `i`. -/
noncomputable def stepOp2 (G : Bool → X → Y) (i : (qrom2Spec X Y).Port)
    (_ : (qrom2Spec X Y).Result i) :
    Matrix ((qrom2Spec X Y).Out i × Unit) ((qrom2Spec X Y).In i × Unit) ℂ :=
  stepOp (G i) () ()

theorem step2_branch_eq (G : Bool → X → Y) (i : (qrom2Spec X Y).Port)
    (r : (qrom2Spec X Y).Result i) :
    ((oracleQuery (G i)).frame Unit).branch r = MatrixMap.conj (stepOp2 G i r) :=
  step_branch_eq (G i) () ()

theorem respectsIndex_stepOp2 (G : Bool → X → Y) :
    Hybrid.RespectsIndex (spec := qrom2Spec X Y) (κ := fun _ ↦ X) (block2 X Y)
      (block2 X Y) (D := Unit) (stepOp2 G) := fun i _ k ↦
  respectsIndex_stepOp (G i) () () k

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Index mass of the run of `x` against `twoRuntime G` from `σ`, on port `b` and query input
`k`. -/
noncomputable def mass2 (I : L.Interp) (G : Bool → X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ) (b : Bool)
    (k : X) : ℝ≥0∞ :=
  (twoRuntime G).indexMass I (κ := fun _ ↦ X) (block2 X Y) x σ ⟨b, k⟩

/-- The masses on port `b` add up to at most the budget of `b` times the trace. -/
theorem sum_mass2_le (I : L.Interp) (G : Bool → X → Y)
    {x : QuantumComp L (qrom2Spec X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {b : Bool} {n : ℕ} (hx : x.IsQueryBoundAt b n) :
    ∑ k, mass2 I G x σ b k ≤ n * ENNReal.ofReal σ.trace.re := by
  have h := (twoRuntime G).tsum_indexMass_eq_queryMass I (κ := fun _ ↦ X)
    (block2 X Y) b (sum_conjTranspose_block2_mul b) x hσ
  rw [tsum_fintype] at h
  exact h.le.trans ((twoRuntime G).queryMass_le_of_isQueryBoundAt I hx hσ)

section Hybrid2

open scoped Matrix.Norms.L2Operator
open Classical in
/-- The observable of an event. -/
private noncomputable def obs {W : QReg → Type w} (E : (Σ u, W u) → Prop) (p : Σ u, W u) :
    Matrix (p.1 × Unit) (p.1 × Unit) ℂ :=
  if E p then 1 else 0

private theorem obs_posSemidef {W : QReg → Type w} (E : (Σ u, W u) → Prop) (p : Σ u, W u) :
    (1 - (obs E p)ᴴ * obs E p).PosSemidef := by
  unfold obs
  by_cases h : E p <;> simp [h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]

private theorem leafProb_eq_obs (I : L.Interp) (G : Bool → X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (E : (Σ u, W u) → Prop) :
    leafProb (twoRuntime G) I x σ E = ∑' p, ENNReal.ofReal (MatrixMap.conj (obs E p)
      (((twoRuntime G).run I x).branch p σ)).trace.re := by
  unfold leafProb obs
  refine tsum_congr fun p ↦ ?_
  by_cases h : E p
  · rw [ind_of_true h, mul_one]; simp [h]
  · rw [ind_of_false h, mul_zero]; simp [h]

/-- **Square-root hybrid bound between two-port runtimes**, Kraus-weight form: the weights are
those of the run against `G`. -/
theorem twoRuntime_sqrt_le_kraus (I : L.Interp) (H G : Bool → X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    leafProb (twoRuntime H) I x σ E ^ (2⁻¹ : ℝ) ≤ leafProb (twoRuntime G) I x σ E ^ (2⁻¹ : ℝ) +
      ∑' j, (twoRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOp2 G i r - stepOp2 H i r) x σ j ^
          (2⁻¹ : ℝ) := by
  rw [leafProb_eq_obs, leafProb_eq_obs]
  have h := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le' I (D := QReg.of Unit)
    (s₀ := fun b ↦ (oracleQuery (G b)).frame Unit) (s₁ := fun b ↦ (oracleQuery (H b)).frame Unit)
    (U := stepOp2 G) (W := stepOp2 H) (SubState.basis ()) (SubState.basis ())
    (step2_branch_eq G) (step2_branch_eq H) x (obs E) (obs_posSemidef E) hσ
  exact h

/-- Converse direction, same weights (of the run against `G`). -/
theorem twoRuntime_sqrt_le_kraus' (I : L.Interp) (H G : Bool → X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) (E : (Σ u, W u) → Prop) :
    leafProb (twoRuntime G) I x σ E ^ (2⁻¹ : ℝ) ≤ leafProb (twoRuntime H) I x σ E ^ (2⁻¹ : ℝ) +
      ∑' j, (twoRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOp2 G i r - stepOp2 H i r) x σ j ^
          (2⁻¹ : ℝ) := by
  rw [leafProb_eq_obs, leafProb_eq_obs]
  have h := QuantumRuntime.rpow_inv_two_tsum_trace_conj_run_le I (D := QReg.of Unit)
    (s₀ := fun b ↦ (oracleQuery (G b)).frame Unit) (s₁ := fun b ↦ (oracleQuery (H b)).frame Unit)
    (U := stepOp2 G) (W := stepOp2 H) (SubState.basis ()) (SubState.basis ())
    (step2_branch_eq G) (step2_branch_eq H) x (obs E) (obs_posSemidef E) hσ
  exact h

/-- The Kraus weight of the change between two runtimes vanishes on a port where they agree. -/
theorem krausWeight_sub_eq_zero {H G : Bool → X → Y} {i : Bool} (h : H i = G i)
    (σ : Matrix ((qrom2Spec X Y).In i × Unit) ((qrom2Spec X Y).In i × Unit) ℂ) :
    QuantumRuntime.krausWeight (spec := qrom2Spec X Y) (D := QReg.of Unit)
      (fun i r ↦ stepOp2 G i r - stepOp2 H i r) i σ = 0 := by
  unfold QuantumRuntime.krausWeight stepOp2
  simp [h]

/-- The Kraus weights of the change between two two-port runtimes, for a program within a query
budget `b`, by the index masses of the run against `G` on the inputs where the functions
differ. -/
theorem tsum_rpow_queryWeight2_le (I : L.Interp) (H G : Bool → X → Y)
    {x : QuantumComp L (qrom2Spec X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {b : Bool → ℕ} (hx : x.IsQueryBound b) :
    ∑' j, (twoRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOp2 G i r - stepOp2 H i r) x σ j ^
          (2⁻¹ : ℝ) ≤
      (4 * ((b false + b true : ℕ) : ℝ≥0∞) *
        (∑ k ∈ Finset.univ.filter (fun k ↦ H false k ≠ G false k), mass2 I G x σ false k +
          ∑ k ∈ Finset.univ.filter (fun k ↦ H true k ≠ G true k), mass2 I G x σ true k)) ^
        (2⁻¹ : ℝ) := by
  refine (QuantumRuntime.tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I
    (twoRuntime G) hx Finset.univ (fun i hi ↦ absurd (Finset.mem_univ i) hi) _).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hmass := (twoRuntime G).tsum_queryWeight_krausWeight_le_tsum_mul_indexMass I
    isCoherentIndex_block2 ((respectsIndex_stepOp2 G).sub (respectsIndex_stepOp2 H)) x hσ
  have hq : ((∑ i : (qrom2Spec X Y).Port, b i : ℕ) : ℝ≥0∞) = ((b false + b true : ℕ) : ℝ≥0∞) := by
    rw [Fintype.sum_bool, add_comm]
  rw [hq, mul_comm 4 _, mul_assoc]
  refine mul_le_mul' le_rfl (hmass.trans ?_)
  have hsig : ∀ f : (Σ _ : (qrom2Spec X Y).Port, X) → ℝ≥0∞,
      ∑' c, f c = ∑ k, f ⟨false, k⟩ + ∑ k, f ⟨true, k⟩ := by
    intro f
    rw [tsum_fintype, Fintype.sum_sigma, Fintype.sum_bool, add_comm]
  have hr : ∀ (i : Bool) (f : (qrom2Spec X Y).Result i → ℝ≥0∞), ∑' r, f r = f () := fun i f ↦ by
    rw [tsum_fintype]
    exact Fintype.sum_unique f
  rw [hsig, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.sum_filter, Finset.sum_filter]
  refine add_le_add (Finset.sum_le_sum fun k _ ↦ ?_) (Finset.sum_le_sum fun k _ ↦ ?_)
  · rw [hr]
    refine (mul_le_mul'
      (ofReal_l2_opNorm_sub_mul_inputBlock_le (H false) (G false) () () k) le_rfl).trans ?_
    split_ifs with hk
    · exact le_rfl
    · simp
  · rw [hr]
    refine (mul_le_mul'
      (ofReal_l2_opNorm_sub_mul_inputBlock_le (H true) (G true) () () k) le_rfl).trans ?_
    split_ifs with hk
    · exact le_rfl
    · simp

end Hybrid2

/-! ## A second-phase program as a `HybridModel` -/

/-- The functions on the two ports: `F` on port `false`, `H` on port `true`. -/
def ports (F H : X → Y) : Bool → X → Y := fun b ↦ if b then H else F

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
@[simp] theorem ports_false (F H : X → Y) : ports F H false = F := rfl

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y] in
@[simp] theorem ports_true (F H : X → Y) : ports F H true = H := rfl

/-- Budget of a program that only calls port `true`, at most `q` times. -/
def secondBudget (q : ℕ) : Bool → ℕ := fun b ↦ if b then q else 0

/-- Budget of a program that only calls port `false`, at most `q` times. -/
def firstBudget (q : ℕ) : Bool → ℕ := fun b ↦ if b then 0 else q

theorem sqrt_scale {a b m : ℝ≥0∞} (h : a ^ (2⁻¹ : ℝ) ≤ b ^ (2⁻¹ : ℝ) + m ^ (2⁻¹ : ℝ))
    (c : ℝ≥0∞) : (a * c) ^ (2⁻¹ : ℝ) ≤ (b * c) ^ (2⁻¹ : ℝ) + (m * c) ^ (2⁻¹ : ℝ) := by
  rw [sqrt_mul, sqrt_mul, sqrt_mul, ← add_mul]
  exact mul_le_mul' h le_rfl

theorem secondPort_err (I : L.Interp) (F H G : X → Y)
    {x : QuantumComp L (qrom2Spec X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {q : ℕ} (hx : x.IsQueryBound (secondBudget q)) :
    ∑' j, (twoRuntime (ports F G)).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOp2 (ports F G) i r - stepOp2 (ports F H) i r)
          x σ j ^ (2⁻¹ : ℝ) ≤
      (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k),
        mass2 I (ports F G) x σ true k) ^ (2⁻¹ : ℝ) := by
  have h := tsum_rpow_queryWeight2_le I (ports F H) (ports F G) hσ hx
  have e : (Finset.univ.filter fun k ↦ ports F H false k ≠ ports F G false k) = ∅ := by
    simp [ports]
  have hq : ((secondBudget q false + secondBudget q true : ℕ) : ℝ≥0∞) = q := by
    simp [secondBudget]
  rw [e, Finset.sum_empty, zero_add, hq] at h
  exact h

/-- The square-root hybrid bound in the function on port `true`, normalised by `c`. -/
theorem secondPort_hybrid (I : L.Interp) (F H G : X → Y)
    {x : QuantumComp L (qrom2Spec X Y) W A} {σ : Matrix (A × Unit) (A × Unit) ℂ}
    (hσ : σ.PosSemidef) {q : ℕ} (hx : x.IsQueryBound (secondBudget q))
    (E : (Σ u, W u) → Prop) (c : ℝ≥0∞) :
    (leafProb (twoRuntime (ports F H)) I x σ E * c) ^ (2⁻¹ : ℝ) ≤
        (leafProb (twoRuntime (ports F G)) I x σ E * c) ^ (2⁻¹ : ℝ) +
          (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k),
            mass2 I (ports F G) x σ true k * c) ^ (2⁻¹ : ℝ) ∧
      (leafProb (twoRuntime (ports F G)) I x σ E * c) ^ (2⁻¹ : ℝ) ≤
        (leafProb (twoRuntime (ports F H)) I x σ E * c) ^ (2⁻¹ : ℝ) +
          (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k),
            mass2 I (ports F G) x σ true k * c) ^ (2⁻¹ : ℝ) := by
  have e : 4 * (q : ℝ≥0∞) * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k),
        mass2 I (ports F G) x σ true k * c =
      4 * q * (∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k),
        mass2 I (ports F G) x σ true k) * c := by
    rw [← Finset.sum_mul, mul_assoc, mul_assoc, mul_assoc]
  rw [e]
  exact ⟨sqrt_scale ((twoRuntime_sqrt_le_kraus I (ports F H) (ports F G) x hσ E).trans
      (add_le_add le_rfl (secondPort_err I F H G hσ hx))) c,
    sqrt_scale ((twoRuntime_sqrt_le_kraus' I (ports F H) (ports F G) x hσ E).trans
      (add_le_add le_rfl (secondPort_err I F H G hσ hx))) c⟩

/-- A program that only calls port `true`, at most `q` times, run from the positive semidefinite
joint operator `σ` with port `false` answered by the fixed function `F`, is a `HybridModel` in
the function on port `true`.  Probabilities and masses are normalised by the trace of `σ`, so
that `ofReal (tr σ) * prob H E` is the unnormalised probability `leafProb`. -/
noncomputable def HybridModel.ofSecondPort (I : L.Interp) (F : X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (hσ : σ.PosSemidef) (q : ℕ) (hx : x.IsQueryBound (secondBudget q)) {Leaf : Type}
    (dec : (Σ u, W u) → Leaf) : HybridModel X Y Leaf q where
  prob H E := leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E (dec p)) *
    (ENNReal.ofReal σ.trace.re)⁻¹
  mass G k := mass2 I (ports F G) x σ true k * (ENNReal.ofReal σ.trace.re)⁻¹
  prob_mono H _ _ h := mul_le_mul' (leafProb_mono (R := twoRuntime (ports F H)) (I := I) x σ fun p ↦ h (dec p)) le_rfl
  prob_sum_le H out := by
    rw [← Finset.sum_mul]
    exact (mul_le_mul' (sum_leafProb_eq_le (R := twoRuntime (ports F H)) (I := I) x hσ fun p ↦ out (dec p)) le_rfl).trans
      (ENNReal.mul_inv_le_one _)
  prob_sub H out T := by
    rw [← Finset.sum_mul]
    exact mul_le_mul' (leafProb_mem_le_sum (R := twoRuntime (ports F H)) (I := I) x σ (fun p ↦ out (dec p)) T) le_rfl
  mass_sum_le G := by
    rw [← Finset.sum_mul]
    have h : ∑ k, mass2 I (ports F G) x σ true k ≤ q * ENNReal.ofReal σ.trace.re :=
      sum_mass2_le I (ports F G) hσ (hx true)
    refine (mul_le_mul' h le_rfl).trans ?_
    rw [mul_assoc]
    exact (mul_le_mul' le_rfl (ENNReal.mul_inv_le_one _)).trans (mul_one _).le
  hybrid H G E := (secondPort_hybrid I F H G hσ hx (fun p ↦ E (dec p))
    (ENNReal.ofReal σ.trace.re)⁻¹).1
  hybrid' H G E := (secondPort_hybrid I F H G hσ hx (fun p ↦ E (dec p))
    (ENNReal.ofReal σ.trace.re)⁻¹).2

/-- The unnormalised probability is the trace times the model's probability. -/
theorem HybridModel.ofSecondPort_prob (I : L.Interp) (F : X → Y)
    (x : QuantumComp L (qrom2Spec X Y) W A) (σ : Matrix (A × Unit) (A × Unit) ℂ)
    (hσ : σ.PosSemidef) (q : ℕ) (hx : x.IsQueryBound (secondBudget q)) {Leaf : Type}
    (dec : (Σ u, W u) → Leaf) (H : X → Y) (E : Leaf → Prop) :
    ENNReal.ofReal σ.trace.re * (HybridModel.ofSecondPort I F x σ hσ q hx dec).prob H E =
      leafProb (twoRuntime (ports F H)) I x σ (fun p ↦ E (dec p)) := by
  change ENNReal.ofReal σ.trace.re * (leafProb (twoRuntime (ports F H)) I x σ
    (fun p ↦ E (dec p)) * (ENNReal.ofReal σ.trace.re)⁻¹) = _
  by_cases h0 : ENNReal.ofReal σ.trace.re = 0
  · rw [h0, zero_mul]
    exact (le_antisymm ((leafProb_le (R := twoRuntime (ports F H)) (I := I) x hσ _).trans h0.le) zero_le).symm
  · rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel h0 ENNReal.ofReal_ne_top, mul_one]

end PQ.QROM
