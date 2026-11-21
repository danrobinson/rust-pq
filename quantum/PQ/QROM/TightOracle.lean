import PQ.QROM.TightCore
import QuantumFoundations.Oracle.Unitary
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The standard oracle `U_H ⊗ 1` satisfies the interface of the tight bound

Non-vacuity of the pure-state model of `PQ/QROM/TightCore.lean`.  The register is
`(X × Y) × W` (query input, response, arbitrary finite workspace `W`), the Hilbert space is
`EuclideanSpace ℂ ((X × Y) × W)`, and the oracle of `H : X → Y` is the QuantumFoundations oracle
unitary `oracleUnitary H : |x, y⟩ ↦ |x, y + H x⟩` tensored with the identity on the workspace
(`stdOracle`, `stdOracle_O_eq`).  `stdOracle` is an `OracleInterface`; hence `tight_avg` and
`tight_view` are statements about the standard circuit model `U_q O_H U_{q-1} … O_H U_0 |ψ⟩` of
Boneh et al., with arbitrary unitaries (`QAlg.ofUnitaries`) and a computational-basis measurement
of an arbitrary predicate as final measurement (`measProj`, `norm_measProj_le`,
`norm_measProj_add_compl`; preceded by the arbitrary unitary `U_q` this is a general two-outcome
projective measurement).

## Relation to VCVio programs (`QuantumComp`) — honest statement

The model here is the *fixed-slot pure-state circuit model*: unitaries (more generally
contractions) interleaved with exactly `q` oracle calls on one fixed register, on a pure input,
with one final projective measurement.  `PQ/QROM/TightLink.lean` proves that for unitary steps
and a final computational-basis measurement the acceptance probability `acc` of this model
equals `qprob` of the VCVio program `QuantumComb.toComp` of the circuit
(`qprob_circuitProg_true`), and restates the tight bounds for those programs.  For arbitrary
adaptive / mixed-state `QuantumComp` programs the tight bounds are proved directly (without
representing the program as one `QAlg`) in `PQ/QROM/PurifyTight.lean` and
`PQ/QROM/PurifyInstances.lean`.
-/

open Finset Matrix Quantum
open scoped Kronecker

namespace PQ.QROM.Tight

set_option linter.unusedSectionVars false

variable {X Y W : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  [Fintype W] [DecidableEq W]

/-- The standard register: query input, response, workspace. -/
abbrev Reg (X Y W : Type) : Type := (X × Y) × W

/-- The oracle matrix `U_H ⊗ 1` on `(X × Y) × W`. -/
noncomputable def oracleMatrix (W : Type) [Fintype W] [DecidableEq W] (H : X → Y) :
    Matrix (Reg X Y W) (Reg X Y W) ℂ :=
  oracleUnitary H ⊗ₖ (1 : Matrix W W ℂ)

/-- The projection matrix onto "the query input is `k`". -/
noncomputable def inputProj (Y W : Type) [DecidableEq Y] [DecidableEq W] (k : X) : Matrix (Reg X Y W) (Reg X Y W) ℂ :=
  Matrix.diagonal fun i ↦ if i.1.1 = k then 1 else 0

theorem oracle_apply (H : X → Y) (φ : EuclideanSpace ℂ (Reg X Y W)) (i : Reg X Y W) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H) φ i = φ ((i.1.1, i.1.2 - H i.1.1), i.2) := by
  obtain ⟨⟨x, y⟩, u⟩ := i
  change (oracleMatrix W H *ᵥ φ.ofLp) ((x, y), u) = _
  rw [Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (((x, y - H x), u) : Reg X Y W)]
  · simp [oracleMatrix, oracleUnitary_apply]
  · rintro ⟨⟨x', y'⟩, u'⟩ _ hne
    simp only [oracleMatrix, Matrix.kroneckerMap_apply, oracleUnitary_apply, Matrix.one_apply]
    by_cases h1 : (x, y) = (x', y' + H x')
    · by_cases h2 : u = u'
      · exfalso
        apply hne
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h1
        subst h2
        simp
      · simp [h2]
    · simp [h1]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem inputProj_apply (k : X) (φ : EuclideanSpace ℂ (Reg X Y W)) (i : Reg X Y W) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) (inputProj Y W k) φ i = if i.1.1 = k then φ i else 0 := by
  change (inputProj Y W k *ᵥ φ.ofLp) i = _
  rw [inputProj, Matrix.mulVec_diagonal]
  split_ifs <;> simp

/-- The basis permutation underlying the inverse oracle. -/
def shiftEquiv (W : Type) (H : X → Y) : Reg X Y W ≃ Reg X Y W :=
  Equiv.prodCongr (oracleEquiv H).symm (Equiv.refl W)

theorem norm_oracle (H : X → Y) (φ : EuclideanSpace ℂ (Reg X Y W)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H) φ‖ = ‖φ‖ := by
  have h : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H) φ‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [oracle_apply]
    exact Equiv.sum_comp (shiftEquiv W H) fun i ↦ ‖φ i‖ ^ 2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem sum_inputProj (φ : EuclideanSpace ℂ (Reg X Y W)) :
    ∑ k, Matrix.toEuclideanCLM (𝕜 := ℂ) (inputProj Y W k) φ = φ := by
  ext i
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  simp only [inputProj_apply]
  change ∑ k, (if i.1.1 = k then φ i else 0) = φ i
  simp

/-- **The standard oracle `U_H ⊗ 1` is an oracle interface.** -/
noncomputable def stdOracle (X Y W : Type) [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    [AddCommGroup Y] [Fintype W] [DecidableEq W] :
    OracleInterface X Y (EuclideanSpace ℂ (Reg X Y W)) where
  P k := Matrix.toEuclideanCLM (𝕜 := ℂ) (inputProj Y W k)
  O H := Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H)
  O_le H φ := (norm_oracle H φ).le
  P_orth k l hkl φ ψ := by
    rw [PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [inputProj_apply, inputProj_apply]
    by_cases h1 : i.1.1 = k
    · have h2 : i.1.1 ≠ l := fun h ↦ hkl (h1.symm.trans h)
      simp [h2]
    · simp [h1]
  P_sum_le φ := by
    refine le_of_eq ?_
    simp only [EuclideanSpace.norm_sq_eq, inputProj_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i.1.1]
    · simp
    · intro k _ hk
      simp [hk.symm]
    · intro h
      exact absurd (Finset.mem_univ _) h
  diff_sum H G φ := by
    rw [Finset.sum_sub_distrib, ← map_sum, ← map_sum, sum_inputProj]
  «local» H G k hk φ := by
    ext i
    rw [oracle_apply, oracle_apply, inputProj_apply, inputProj_apply]
    by_cases h : i.1.1 = k
    · simp only [h, hk]
    · simp [h]
  diff_comm H G k φ := by
    ext i
    rw [inputProj_apply]
    change _ = Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H) _ i -
      Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W G) _ i
    change (if i.1.1 = k then Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H) φ i -
      Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W G) φ i else 0) = _
    rw [oracle_apply, oracle_apply, oracle_apply, oracle_apply, inputProj_apply, inputProj_apply]
    by_cases h : i.1.1 = k <;> simp [h]
  diff_le H G k φ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_oracle, norm_oracle]
    exact le_of_eq (by ring)

/-- The oracle of the interface is the QuantumFoundations oracle unitary tensored with the
identity, acting on vectors by matrix-vector multiplication (QuantumFoundations' `•ᵥ`, i.e.
`Matrix.toEuclideanLin`). -/
theorem stdOracle_O_eq (H : X → Y) (φ : EuclideanSpace ℂ (Reg X Y W)) :
    (stdOracle X Y W).O H φ =
      Matrix.toEuclideanLin (oracleUnitary H ⊗ₖ (1 : Matrix W W ℂ)) φ := rfl

/-- The oracle of the interface in coordinates: `|x, y, u⟩ ↦ |x, y + H x, u⟩`. -/
theorem stdOracle_O_apply (H : X → Y) (φ : EuclideanSpace ℂ (Reg X Y W)) (x : X) (y : Y) (u : W) :
    (stdOracle X Y W).O H φ ((x, y + H x), u) = φ ((x, y), u) := by
  change Matrix.toEuclideanCLM (𝕜 := ℂ) (oracleMatrix W H) φ _ = _
  rw [oracle_apply]
  simp

/-- The oracle of the interface is norm preserving. -/
theorem norm_stdOracle_O (H : X → Y) (φ : EuclideanSpace ℂ (Reg X Y W)) :
    ‖(stdOracle X Y W).O H φ‖ = ‖φ‖ := norm_oracle H φ

section Circuit

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A unitary matrix acts isometrically. -/
theorem norm_toEuclideanCLM_of_mem_unitaryGroup {U : Matrix n n ℂ}
    (hU : U ∈ Matrix.unitaryGroup n ℂ) (φ : EuclideanSpace ℂ n) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) U φ‖ = ‖φ‖ := by
  have h1 : star U * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
  have h2 : U * star U = 1 := Matrix.mem_unitaryGroup_iff.1 hU
  have hT : Matrix.toEuclideanCLM (𝕜 := ℂ) U ∈ unitary (EuclideanSpace ℂ n →L[ℂ] _) := by
    rw [Unitary.mem_iff, ← map_star, ← map_mul, ← map_mul, h1, h2, map_one]
    exact ⟨rfl, rfl⟩
  exact Unitary.norm_map ⟨_, hT⟩ φ

/-- A circuit with arbitrary unitary gates `U 0, U 1, …` and a normalised (or subnormalised)
initial vector is a `QAlg`. -/
noncomputable def QAlg.ofUnitaries (ψ : EuclideanSpace ℂ n) (hψ : ‖ψ‖ ≤ 1)
    (U : ℕ → Matrix n n ℂ) (hU : ∀ t, U t ∈ Matrix.unitaryGroup n ℂ) :
    QAlg (EuclideanSpace ℂ n) where
  init := ψ
  init_le := hψ
  U t := Matrix.toEuclideanCLM (𝕜 := ℂ) (U t)
  U_le t φ := (norm_toEuclideanCLM_of_mem_unitaryGroup (hU t) φ).le

/-- The projection onto the basis states satisfying `p`: the measurement operator of the outcome
"`p` holds" of a computational-basis measurement. -/
noncomputable def measProj (p : n → Prop) [DecidablePred p] :
    EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) (Matrix.diagonal fun i ↦ if p i then 1 else 0)

theorem measProj_apply (p : n → Prop) [DecidablePred p] (φ : EuclideanSpace ℂ n) (i : n) :
    measProj p φ i = if p i then φ i else 0 := by
  change ((Matrix.diagonal fun i ↦ if p i then (1 : ℂ) else 0) *ᵥ φ.ofLp) i = _
  rw [Matrix.mulVec_diagonal]
  split_ifs <;> simp

/-- A projective two-outcome measurement: the two outcome probabilities sum to `‖φ‖²`. -/
theorem norm_measProj_add_compl (p : n → Prop) [DecidablePred p] (φ : EuclideanSpace ℂ n) :
    ‖measProj p φ‖ ^ 2 + ‖measProj (fun i ↦ ¬ p i) φ‖ ^ 2 = ‖φ‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, measProj_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  by_cases h : p i <;> simp [h]

theorem norm_measProj_le (p : n → Prop) [DecidablePred p] (φ : EuclideanSpace ℂ n) :
    ‖measProj p φ‖ ≤ ‖φ‖ := by
  have h := norm_measProj_add_compl p φ
  exact le_of_sq_le_sq (by nlinarith [sq_nonneg ‖measProj (fun i ↦ ¬ p i) φ‖]) (norm_nonneg _)

/-- Acceptance probabilities of the circuit model are probabilities. -/
theorem acc_mem_Icc {X Y : Type} [Fintype X] (I : OracleInterface X Y (EuclideanSpace ℂ n))
    (A : QAlg (EuclideanSpace ℂ n)) (q : ℕ) (p : n → Prop) [DecidablePred p] (H : X → Y) :
    A.acc I q (measProj p) H ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨A.acc_nonneg I q _ H, A.acc_le_one I q _ (norm_measProj_le p) H⟩

end Circuit

end PQ.QROM.Tight

#print axioms PQ.QROM.Tight.stdOracle
#print axioms PQ.QROM.Tight.stdOracle_O_eq
#print axioms PQ.QROM.Tight.stdOracle_O_apply
#print axioms PQ.QROM.Tight.QAlg.ofUnitaries
#print axioms PQ.QROM.Tight.norm_measProj_add_compl
#print axioms PQ.QROM.Tight.acc_mem_Icc
