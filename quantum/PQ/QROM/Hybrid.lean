import PQ.QROM.Defs
import PQ.QROM.Interface

/-!
# E1: the per-pair square-root hybrid bound for QROM programs

For a fixed quantum query program `x` (any VCVio `QuantumComp` over `qromSpec X Y`) making at most
`q` oracle calls on every path, and any two functions `H G : X → Y`,

`√P_H(E) ≤ √P_G(E) + √(4 q · ∑_{k : H k ≠ G k} mass_G(k))` and conversely,

where `mass_G(k) = qmass I G x ρ k` is the total query mass the run against `G` puts on the query
input `k`: the total index mass (`Quantum.QuantumRuntime.indexMass`) of the coherent index whose
blocks are the projections `|k⟩⟨k| ⊗ 1_Y` of the port register `X × Y`.  The masses add up to at
most `q`.

Everything is packaged as `HybridModel.ofProgram`, the only interface the game analyses use.
-/

open MeasureTheory ENNReal Quantum Matrix
open scoped Kronecker

universe u v w

namespace PQ.QROM

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-! ## The coherent index of the query input -/

/-- The projection `|k⟩⟨k| ⊗ 1_Y` of the port register `X × Y` onto the query input `k`. -/
noncomputable def inputBlock (X Y : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (i : (qromSpec X Y).Port) (k : X) :
    Matrix ((qromSpec X Y).In i) ((qromSpec X Y).In i) ℂ :=
  Matrix.diagonal fun p : X × Y ↦ if p.1 = k then (1 : ℂ) else 0

theorem inputBlock_conjTranspose (i : (qromSpec X Y).Port) (k : X) :
    (inputBlock X Y i k)ᴴ = inputBlock X Y i k :=
  Matrix.conjTranspose_diagonal_ite fun p : X × Y ↦ p.1 = k

theorem inputBlock_mul_self (i : (qromSpec X Y).Port) (k : X) :
    inputBlock X Y i k * inputBlock X Y i k = inputBlock X Y i k :=
  Matrix.diagonal_ite_mul_self fun p : X × Y ↦ p.1 = k

theorem inputBlock_mul_of_ne (i : (qromSpec X Y).Port) {a b : X} (hab : a ≠ b) :
    inputBlock X Y i b * inputBlock X Y i a = 0 := by
  unfold inputBlock
  rw [Matrix.diagonal_ite_mul_diagonal_ite]
  ext m m'
  by_cases h : m = m'
  · subst h
    have : ¬ (m.1 = b ∧ m.1 = a) := fun h ↦ hab (h.2.symm.trans h.1)
    simp [this]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem sum_inputBlock (i : (qromSpec X Y).Port) : ∑ k, inputBlock X Y i k = 1 := by
  unfold inputBlock
  ext m m'
  rw [Matrix.sum_apply]
  by_cases h : m = m'
  · subst h
    simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

/-- The projections onto the query inputs form a coherent index, on inputs and outputs. -/
theorem isCoherentIndex_inputBlock :
    Hybrid.IsCoherentIndex (spec := qromSpec X Y) (κ := fun _ ↦ X) (inputBlock X Y)
      (inputBlock X Y) where
  sum_eq_one := sum_inputBlock
  mul_self := inputBlock_mul_self
  conjTranspose_mul_of_ne i a b hab := by
    rw [inputBlock_conjTranspose]
    exact inputBlock_mul_of_ne i hab

theorem sum_conjTranspose_inputBlock_mul (i : (qromSpec X Y).Port) :
    ∑ k, (inputBlock X Y i k)ᴴ * inputBlock X Y i k = 1 :=
  (Finset.sum_congr rfl fun k _ ↦ by
    rw [inputBlock_conjTranspose, inputBlock_mul_self]).trans (sum_inputBlock i)

/-! ## The oracle unitary and the index -/

variable [AddCommGroup Y]

/-- The oracle unitary keeps the query input: it commutes with the projections. -/
theorem inputBlock_mul_oracleUnitary (G : X → Y) (i : (qromSpec X Y).Port) (k : X) :
    inputBlock X Y i k * (oracleUnitary G : Matrix (X × Y) (X × Y) ℂ) =
      oracleUnitary G * inputBlock X Y i k := by
  unfold inputBlock
  ext m m'
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, oracleUnitary_apply]
  by_cases h : m = (m'.1, m'.2 + G m'.1)
  · have h1 : m.1 = m'.1 := by rw [h]
    simp [h]
  · simp [h]

/-- On the block of a query input where two functions agree, their oracle unitaries agree. -/
theorem oracleUnitary_mul_inputBlock_congr {H G : X → Y} (i : (qromSpec X Y).Port) {k : X}
    (hk : H k = G k) :
    (oracleUnitary G : Matrix (X × Y) (X × Y) ℂ) * inputBlock X Y i k =
      oracleUnitary H * inputBlock X Y i k := by
  unfold inputBlock
  ext m m'
  rw [Matrix.mul_diagonal, Matrix.mul_diagonal, oracleUnitary_apply, oracleUnitary_apply]
  by_cases h : m'.1 = k
  · rw [h, hk]
  · simp [h]

/-- The Kraus operator of the step of the oracle runtime: `U_G ⊗ 1` on the port register and the
trivial private register. -/
noncomputable def stepOp (G : X → Y) (i : (qromSpec X Y).Port) (_ : (qromSpec X Y).Result i) :
    Matrix ((qromSpec X Y).Out i × Unit) ((qromSpec X Y).In i × Unit) ℂ :=
  (oracleUnitary G : Matrix (X × Y) (X × Y) ℂ) ⊗ₖ (1 : Matrix Unit Unit ℂ)

theorem step_branch_eq (G : X → Y) (i : (qromSpec X Y).Port) (r : (qromSpec X Y).Result i) :
    ((oracleQuery G).frame Unit).branch r = MatrixMap.conj (stepOp G i r) := by
  rw [DSubInstrument.branch_frame_apply, branch_oracleQuery_apply, MatrixMap.amplify_conj]
  rfl

theorem respectsIndex_stepOp (G : X → Y) :
    Hybrid.RespectsIndex (spec := qromSpec X Y) (κ := fun _ ↦ X) (inputBlock X Y)
      (inputBlock X Y) (D := Unit) (stepOp G) := fun i r k ↦ by
  unfold stepOp
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    inputBlock_mul_oracleUnitary, Matrix.mul_assoc, inputBlock_mul_self]
  simp

section Norm

open scoped Matrix.Norms.L2Operator

/-- A matrix whose Gram matrix is a projection has operator norm at most one. -/
theorem l2_opNorm_le_one_of_gram {n : Type*} [Fintype n] [DecidableEq n] {M N : Matrix n n ℂ}
    (hM : Mᴴ * M = N) (hN : Nᴴ * N = N) : ‖M‖ ≤ 1 := by
  have h1 : ‖N‖ = ‖N‖ * ‖N‖ := by
    conv_lhs => rw [← hN]
    exact CStarRing.norm_star_mul_self (x := N)
  have h2 : ‖M‖ * ‖M‖ = ‖N‖ := by
    rw [← hM]
    exact (CStarRing.norm_star_mul_self (x := M)).symm
  have h3 : ‖N‖ ≤ 1 := by
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg N]
  nlinarith [norm_nonneg M]

theorem l2_opNorm_stepOp_mul_inputBlock_le (G : X → Y) (i : (qromSpec X Y).Port)
    (r : (qromSpec X Y).Result i) (k : X) :
    ‖stepOp G i r * (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ))‖ ≤ 1 := by
  refine l2_opNorm_le_one_of_gram (N := inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ)) ?_ ?_
  · unfold stepOp
    rw [← Matrix.mul_kronecker_mul, Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
      Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ (oracleUnitary G),
      conjTranspose_oracleUnitary_mul_self, Matrix.one_mul, inputBlock_conjTranspose,
      inputBlock_mul_self]
    simp
  · rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, inputBlock_conjTranspose,
      inputBlock_mul_self]
    simp

/-- The change of the oracle on the block of a query input: at most `4`, and `0` where the
functions agree. -/
theorem ofReal_l2_opNorm_sub_mul_inputBlock_le (H G : X → Y) (i : (qromSpec X Y).Port)
    (r : (qromSpec X Y).Result i) (k : X) :
    ENNReal.ofReal (‖(stepOp G i r - stepOp H i r) *
        (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ))‖ ^ 2) ≤
      if H k ≠ G k then 4 else 0 := by
  split_ifs with hk
  · have h := norm_sub_le (stepOp G i r * (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ)))
      (stepOp H i r * (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ)))
    rw [← Matrix.sub_mul] at h
    have hG := l2_opNorm_stepOp_mul_inputBlock_le G i r k
    have hH := l2_opNorm_stepOp_mul_inputBlock_le H i r k
    have h4 : ‖(stepOp G i r - stepOp H i r) *
        (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ))‖ ^ 2 ≤ 4 := by
      nlinarith [norm_nonneg ((stepOp G i r - stepOp H i r) *
        (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ)))]
    calc _ ≤ ENNReal.ofReal 4 := ENNReal.ofReal_le_ofReal h4
      _ = 4 := by norm_num
  · rw [not_not] at hk
    have h0 : (stepOp G i r - stepOp H i r) *
        (inputBlock X Y i k ⊗ₖ (1 : Matrix Unit Unit ℂ)) = 0 := by
      unfold stepOp
      rw [Matrix.sub_mul, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
        oracleUnitary_mul_inputBlock_congr i hk, sub_self]
    rw [h0]
    simp

end Norm

/-! ## Query masses -/

variable {L : LocalSig.{u, v}} {W : QReg → Type w} {A : QReg}

/-- Total query mass of the run of `x` against `G` from `ρ` on the query input `k`: the sum over
the calls of the weight of the call's input in the block `|k⟩⟨k| ⊗ 1_Y` of the port register. -/
noncomputable def qmass (I : L.Interp) (G : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (k : X) : ℝ≥0∞ :=
  (additiveOracleRuntime G).indexMass I (κ := fun _ ↦ X) (inputBlock X Y) x
    (ρ.matrix ⊗ₖ (additiveOracleRuntime G).init.matrix) ⟨(), k⟩

theorem ofReal_trace_prod_init_le_one (G : X → Y) (ρ : SubState A) :
    ENNReal.ofReal (ρ.matrix ⊗ₖ (additiveOracleRuntime G).init.matrix).trace.re ≤ 1 := by
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (ρ.prod (additiveOracleRuntime G).init).trace_re_le_one

/-- At most `q` queries: the masses add up to at most `q`. -/
theorem sum_qmass_le (I : L.Interp) (G : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) {q : ℕ} (hx : QueryBounded x q) : ∑ k, qmass I G x ρ k ≤ q := by
  have h := (additiveOracleRuntime G).tsum_indexMass_eq_queryMass I (κ := fun _ ↦ X)
    (inputBlock X Y) () (sum_conjTranspose_inputBlock_mul ()) x
    (ρ.prod (additiveOracleRuntime G).init).posSemidef
  rw [tsum_fintype] at h
  refine (h.le.trans ((additiveOracleRuntime G).queryMass_le_of_isQueryBoundAt I (hx ())
    (ρ.prod (additiveOracleRuntime G).init).posSemidef)).trans ?_
  calc (q : ℝ≥0∞) * _ ≤ q * 1 := by
        gcongr
        exact ofReal_trace_prod_init_le_one G ρ
    _ = q := mul_one _

/-! ## The hybrid bound -/

section Hybrid

open scoped Matrix.Norms.L2Operator

/-- The error term of VCVio's index-mass hybrid for the pair `G, H`, bounded by the masses of the
run against `G` on the inputs where the functions differ. -/
theorem tsum_rpow_queryWeight_le (I : L.Interp) (H G : X → Y)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) {q : ℕ} (hx : QueryBounded x q) :
    ∑' j, (additiveOracleRuntime G).queryWeight I
        (QuantumRuntime.krausWeight fun i r ↦ stepOp G i r - stepOp H i r) x
        (ρ.matrix ⊗ₖ (additiveOracleRuntime G).init.matrix) j ^ (2⁻¹ : ℝ) ≤
      (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k), qmass I G x ρ k) ^ (2⁻¹ : ℝ) := by
  refine (QuantumRuntime.tsum_rpow_inv_two_queryWeight_le_of_isQueryBound I
    (additiveOracleRuntime G) hx Finset.univ (fun i hi ↦ absurd (Finset.mem_univ i) hi) _).trans ?_
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have hmass := (additiveOracleRuntime G).tsum_queryWeight_krausWeight_le_tsum_mul_indexMass I
    isCoherentIndex_inputBlock ((respectsIndex_stepOp G).sub (respectsIndex_stepOp H)) x
    (ρ.prod (additiveOracleRuntime G).init).posSemidef
  have hq : ((∑ _i : (qromSpec X Y).Port, q : ℕ) : ℝ≥0∞) = q := by simp
  rw [hq, mul_comm 4 (q : ℝ≥0∞), mul_assoc]
  refine mul_le_mul' le_rfl (hmass.trans ?_)
  have hsig : ∀ f : (Σ _ : (qromSpec X Y).Port, X) → ℝ≥0∞, ∑' c, f c = ∑ k, f ⟨(), k⟩ := by
    intro f
    rw [tsum_fintype]
    exact (Fintype.sum_equiv (Equiv.uniqueSigma fun _ : Unit ↦ X).symm _ _ fun k ↦ rfl).symm
  rw [hsig, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_le_sum fun k _ ↦ ?_
  have hr : ∀ f : (qromSpec X Y).Result () → ℝ≥0∞, ∑' r, f r = f () := fun f ↦ by
    rw [tsum_fintype]
    exact Fintype.sum_unique f
  rw [hr]
  refine (mul_le_mul' (ofReal_l2_opNorm_sub_mul_inputBlock_le H G () () k) le_rfl).trans ?_
  split_ifs with hk
  · exact le_rfl
  · simp

/-- **Square-root hybrid bound**, masses of the run against `G`. -/
theorem qprob_rpow_le (I : L.Interp) (H G : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) {q : ℕ} (hx : QueryBounded x q) (E : (Σ u, W u) → Prop) :
    qprob I H x ρ E ^ (2⁻¹ : ℝ) ≤ qprob I G x ρ E ^ (2⁻¹ : ℝ) +
      (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k), qmass I G x ρ k) ^ (2⁻¹ : ℝ) :=
  by
  have h := QuantumRuntime.rpow_inv_two_outcomeLawWith_le' I (D := QReg.of Unit)
    (s₀ := fun _ ↦ (oracleQuery G).frame Unit) (s₁ := fun _ ↦ (oracleQuery H).frame Unit)
    (U := stepOp G) (W := stepOp H) (SubState.basis ()) (step_branch_eq G)
    (step_branch_eq H) x ρ E (MeasurableSet.singleton True)
  have h' := tsum_rpow_queryWeight_le I H G x ρ hx
  unfold qprob
  dsimp only [additiveOracleRuntime] at h' ⊢
  exact h.trans (add_le_add le_rfl h')

/-- **Square-root hybrid bound**, converse direction, same masses (of the run against `G`). -/
theorem qprob_rpow_le' (I : L.Interp) (H G : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) {q : ℕ} (hx : QueryBounded x q) (E : (Σ u, W u) → Prop) :
    qprob I G x ρ E ^ (2⁻¹ : ℝ) ≤ qprob I H x ρ E ^ (2⁻¹ : ℝ) +
      (4 * q * ∑ k ∈ Finset.univ.filter (fun k ↦ H k ≠ G k), qmass I G x ρ k) ^ (2⁻¹ : ℝ) :=
  by
  have h := QuantumRuntime.rpow_inv_two_outcomeLawWith_le I (D := QReg.of Unit)
    (s₀ := fun _ ↦ (oracleQuery G).frame Unit) (s₁ := fun _ ↦ (oracleQuery H).frame Unit)
    (U := stepOp G) (W := stepOp H) (SubState.basis ()) (step_branch_eq G)
    (step_branch_eq H) x ρ E (MeasurableSet.singleton True)
  have h' := tsum_rpow_queryWeight_le I H G x ρ hx
  unfold qprob
  dsimp only [additiveOracleRuntime] at h' ⊢
  exact h.trans (add_le_add le_rfl h')

end Hybrid

/-! ## Monotonicity and total mass of `qprob` -/

theorem qprob_eq_tsum (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (E : (Σ u, W u) → Prop) :
    qprob I H x ρ E = ∑' p, ENNReal.ofReal
      ((additiveOracleRuntime H).jointPost I x ρ p).matrix.trace.re *
        Set.indicator {True} 1 (E p) :=
  (additiveOracleRuntime H).evalDistMap_apply I x ρ E (MeasurableSet.singleton True)

/-- Events are monotone. -/
theorem qprob_mono (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) {E E' : (Σ u, W u) → Prop} (h : ∀ p, E p → E' p) :
    qprob I H x ρ E ≤ qprob I H x ρ E' := by
  rw [qprob_eq_tsum, qprob_eq_tsum]
  refine tsum_le_tsum fun p ↦ mul_le_mul' le_rfl ?_
  by_cases hp : E p
  · simp [hp, h p hp]
  · simp [hp]

/-- The leaf weights of a run add up to at most one. -/
theorem tsum_jointPost_trace_le_one (I : L.Interp) (H : X → Y)
    (x : QuantumComp L (qromSpec X Y) W A) (ρ : SubState A) :
    ∑' p, ENNReal.ofReal ((additiveOracleRuntime H).jointPost I x ρ p).matrix.trace.re ≤ 1 :=
  (((additiveOracleRuntime H).run I x).isCPTNIFamily.tsum_ofReal_trace_re_le
    (ρ.prod (additiveOracleRuntime H).init).posSemidef).trans (ofReal_trace_prod_init_le_one H ρ)

/-- The events `out = k`, for any decoding `out` of the leaf, have total probability at most
one. -/
theorem sum_qprob_le_one (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (out : (Σ u, W u) → X) :
    ∑ k, qprob I H x ρ (fun p ↦ out p = k) ≤ 1 := by
  simp only [qprob_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine le_trans (le_of_eq (tsum_congr fun p ↦ ?_)) (tsum_jointPost_trace_le_one I H x ρ)
  rw [← Finset.mul_sum, Finset.sum_eq_single (out p)]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Finite subadditivity of the distribution of a classical decoding of the leaf. -/
theorem qprob_mem_le_sum (I : L.Interp) (H : X → Y) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (out : (Σ u, W u) → X) (T : Finset X) :
    qprob I H x ρ (fun p ↦ out p ∈ T) ≤ ∑ k ∈ T, qprob I H x ρ (fun p ↦ out p = k) := by
  simp only [qprob_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine tsum_le_tsum fun p ↦ ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul' le_rfl ?_
  by_cases h : out p ∈ T
  · rw [Finset.sum_eq_single_of_mem (out p) h]
    · simp [h]
    · intro k _ hk
      simp [Ne.symm hk]
  · simp [h]

/-! ## The interface -/

/-- Every quantum query program with at most `q` calls is a `HybridModel`.

The leaves `Σ u, W u` of a program live in `Type (max 1 w)` (`QReg : Type 1`), while
`HybridModel` takes its leaf type in `Type`; so the model is stated for an arbitrary classical
decoding `dec` of the leaf into a `Type`-valued `Leaf`.  Nothing is lost: an event
`E : (Σ u, W u) → Prop` is the event `id` of the decoding `dec := E` into `Prop`. -/
noncomputable def HybridModel.ofProgram (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q) {Leaf : Type} (dec : (Σ u, W u) → Leaf) :
    HybridModel X Y Leaf q where
  prob H E := qprob I H x ρ fun p ↦ E (dec p)
  mass G k := qmass I G x ρ k
  prob_mono H _ _ h := qprob_mono I H x ρ fun p ↦ h (dec p)
  prob_sum_le H out := sum_qprob_le_one I H x ρ fun p ↦ out (dec p)
  prob_sub H out T := qprob_mem_le_sum I H x ρ (fun p ↦ out (dec p)) T
  mass_sum_le G := sum_qmass_le I G x ρ hx
  hybrid H G E := qprob_rpow_le I H G x ρ hx fun p ↦ E (dec p)
  hybrid' H G E := qprob_rpow_le' I H G x ρ hx fun p ↦ E (dec p)

@[simp]
theorem HybridModel.ofProgram_prob (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q) {Leaf : Type} (dec : (Σ u, W u) → Leaf)
    (H : X → Y) (E : Leaf → Prop) :
    (HybridModel.ofProgram I x ρ q hx dec).prob H E = qprob I H x ρ fun p ↦ E (dec p) :=
  rfl

@[simp]
theorem HybridModel.ofProgram_mass (I : L.Interp) (x : QuantumComp L (qromSpec X Y) W A)
    (ρ : SubState A) (q : ℕ) (hx : QueryBounded x q) {Leaf : Type} (dec : (Σ u, W u) → Leaf)
    (G : X → Y) (k : X) :
    (HybridModel.ofProgram I x ρ q hx dec).mass G k = qmass I G x ρ k :=
  rfl

end PQ.QROM

#print axioms PQ.QROM.sum_qmass_le
#print axioms PQ.QROM.qprob_rpow_le
#print axioms PQ.QROM.qprob_rpow_le'
#print axioms PQ.QROM.qprob_mono
#print axioms PQ.QROM.sum_qprob_le_one
#print axioms PQ.QROM.HybridModel.ofProgram
