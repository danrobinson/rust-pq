import PQ.Interactive.EUFCMA

/-!
# Non-vacuity of the model

* `applyU`: every unitary on the workspace is an instrument node, and `measureBasis` is the
  computational-basis measurement, so the model contains all unitary circuits with measurement
  and classical control.
* One-qubit interference: Hadamard-then-measure gives each outcome with weight `1/2`;
  Hadamard-twice-then-measure gives outcome `0` with weight `1` (`qWeight_hMeasure`,
  `qWeight_hhMeasure`).  Both machines are `RationalBorn`.
* `rationalBorn_of_usesOnly`: machines built from instruments preserving Gaussian-rational
  matrices, started in a Gaussian-rational state, are `RationalBorn`.  Conjugation by a
  Gaussian-rational matrix (permutation gates, basis projectors) and by a scalar multiple `c • K`
  with `|c|²` rational (Hadamard gates) qualify.
* The quantum EUF-CMA game can be lost and won: against a scheme that rejects everything every
  quantum forger has advantage `0`; a one-qubit forger wins a toy scheme with probability exactly
  `1/2`, and with probability `0` after a second Hadamard.
-/

open OracleComp OracleSpec ENNReal Quantum MeasureTheory Matrix
open scoped ComplexOrder

namespace PQ.Interactive

variable {W : Type} [Fintype W] [DecidableEq W] {α β γ : Type}
variable {ι : Type} {spec : OracleSpec ι}

/-! ## Gates and measurements as instrument nodes -/

lemma sum_fin_one_kraus (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) :
    ∑ _i : Fin (0 + 1), Uᴴ * U = 1 := by
  simpa using hU

/-- The one-outcome instrument `ρ ↦ U ρ U†` of a unitary (more generally, an isometry). -/
noncomputable def unitaryInstr (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) :
    SubInstrument W W (Fin (0 + 1)) :=
  DSubInstrument.ofKraus (ι := Fin (0 + 1)) (B := fun _ ↦ W) (fun _ ↦ U) (sum_fin_one_kraus U hU)

lemma lossless_unitaryInstr (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) :
    (unitaryInstr U hU).Lossless :=
  DSubInstrument.lossless_ofKraus _ _

@[simp] lemma branch_unitaryInstr (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) (i : Fin (0 + 1))
    (ρ : Matrix W W ℂ) : (unitaryInstr U hU).branch i ρ = U * ρ * Uᴴ := by
  simp [unitaryInstr, MatrixMap.conj_apply]

/-- Index of the gate `U`. -/
@[reducible] noncomputable def unitaryIdx (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) : InstrIdx W :=
  ⟨0, unitaryInstr U hU, lossless_unitaryInstr U hU⟩

/-- **Every unitary is in the model**: the machine applying `U` to the workspace. -/
noncomputable def applyU (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) : QOC W spec (Fin (0 + 1)) :=
  liftM ((instrSpec W + spec).query (Sum.inl (unitaryIdx U hU)))

/-- Projector onto the basis state `w`. -/
def basisProj (w : W) : Matrix W W ℂ := Matrix.diagonal fun v ↦ if v = w then 1 else 0

omit [Fintype W] in
lemma basisProj_conjTranspose (w : W) : (basisProj w)ᴴ = basisProj w := by
  ext a b
  by_cases h : a = b <;> simp [basisProj, Matrix.conjTranspose_apply, h, eq_comm, apply_ite]

lemma basisProj_mul_self (w : W) : basisProj w * basisProj w = basisProj w := by
  simp [basisProj, Matrix.diagonal_mul_diagonal]

lemma sum_basisProj_kraus {n : ℕ} (e : Fin (n + 1) ≃ W) :
    ∑ i, (basisProj (e i))ᴴ * basisProj (e i) = 1 := by
  simp only [basisProj_conjTranspose, basisProj_mul_self]
  ext a b
  by_cases h : a = b
  · subst h
    simp only [basisProj, Matrix.sum_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq]
    rw [Finset.sum_eq_single (e.symm a) (fun i _ hi ↦ by
      have : a ≠ e i := by rintro rfl; exact hi (by simp)
      simp [this]) (by simp)]
    simp
  · simp [basisProj, Matrix.sum_apply, h]

/-- The computational-basis measurement, with outcomes labelled through `e : Fin (n+1) ≃ W`. -/
noncomputable def measureInstr {n : ℕ} (e : Fin (n + 1) ≃ W) : SubInstrument W W (Fin (n + 1)) :=
  DSubInstrument.ofKraus (ι := Fin (n + 1)) (B := fun _ ↦ W) (fun i ↦ basisProj (e i))
    (sum_basisProj_kraus e)

lemma lossless_measureInstr {n : ℕ} (e : Fin (n + 1) ≃ W) : (measureInstr e).Lossless :=
  DSubInstrument.lossless_ofKraus _ _

@[simp] lemma branch_measureInstr {n : ℕ} (e : Fin (n + 1) ≃ W) (i : Fin (n + 1))
    (ρ : Matrix W W ℂ) :
    (measureInstr e).branch i ρ = basisProj (e i) * ρ * basisProj (e i) := by
  simp [measureInstr, MatrixMap.conj_apply, basisProj_conjTranspose]

/-- Index of the computational-basis measurement. -/
@[reducible] noncomputable def measureIdx {n : ℕ} (e : Fin (n + 1) ≃ W) : InstrIdx W :=
  ⟨n, measureInstr e, lossless_measureInstr e⟩

/-- The machine measuring the workspace in the computational basis. -/
noncomputable def measureBasis {n : ℕ} (e : Fin (n + 1) ≃ W) : QOC W spec (Fin (n + 1)) :=
  liftM ((instrSpec W + spec).query (Sum.inl (measureIdx e)))

/-! ## One qubit: interference -/

/-- `1/√2`. -/
noncomputable def hadS : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

lemma hadS_mul_self : hadS * hadS = 1 / 2 := by
  unfold hadS
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

lemma star_hadS : star hadS = hadS := by
  unfold hadS
  rw [star_inv₀]
  simp

/-- The Hadamard matrix. -/
noncomputable def hadamard : Matrix (Fin 2) (Fin 2) ℂ := hadS • !![1, 1; 1, -1]

lemma hadamard_conjTranspose : hadamardᴴ = hadamard := by
  unfold hadamard
  rw [Matrix.conjTranspose_smul, star_hadS]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]

lemma hadamard_mul_self : hadamard * hadamard = 1 := by
  unfold hadamard
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hadS_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

lemma hadamard_unitary : hadamardᴴ * hadamard = 1 := by
  rw [hadamard_conjTranspose, hadamard_mul_self]

/-- The state `|0⟩⟨0|`. -/
def ket0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- The state `|+⟩⟨+|`. -/
noncomputable def ketPlus : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

lemma hadamard_ket0 : hadamard * ket0 * hadamardᴴ = ketPlus := by
  rw [hadamard_conjTranspose]
  unfold hadamard
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hadS_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ket0, ketPlus]

lemma hadamard_ketPlus : hadamard * ketPlus * hadamardᴴ = ket0 := by
  rw [← hadamard_ket0, hadamard_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hadamard_mul_self, Matrix.one_mul, Matrix.mul_assoc, hadamard_mul_self, Matrix.mul_one]

lemma posSemidef_ket0 : ket0.PosSemidef := by
  have : ket0 = (basisProj (0 : Fin 2))ᴴ * basisProj (0 : Fin 2) := by
    rw [basisProj_conjTranspose, basisProj_mul_self]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ket0, basisProj]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma trace_ket0 : ket0.trace = 1 := by
  simp [ket0, Matrix.trace_fin_two]

lemma trace_basisProj_mul (w : W) (ρ : Matrix W W ℂ) :
    (basisProj w * ρ * basisProj w).trace = ρ w w := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, basisProj_mul_self]
  simp [Matrix.trace, basisProj, Matrix.diagonal_mul]

/-- Hadamard, then measure. -/
noncomputable def hMeasure : QOC (Fin 2) spec (Fin 2) :=
  applyU hadamard hadamard_unitary >>= fun _ ↦ measureBasis (Equiv.refl (Fin 2))

/-- Hadamard twice, then measure. -/
noncomputable def hhMeasure : QOC (Fin 2) spec (Fin 2) :=
  applyU hadamard hadamard_unitary >>= fun _ ↦
    applyU hadamard hadamard_unitary >>= fun _ ↦ measureBasis (Equiv.refl (Fin 2))

lemma qWeight_measureBasis (p : Fin 2 → Prop) [DecidablePred p] (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    qWeight p (measureBasis (spec := unifSpec) (Equiv.refl (Fin 2))) ρ =
      (if p 0 then ENNReal.ofReal (ρ 0 0).re else 0) +
        (if p 1 then ENNReal.ofReal (ρ 1 1).re else 0) := by
  rw [← bind_pure (measureBasis _), measureBasis, qWeight_instr_bind]
  simp [measureIdx, Fin.sum_univ_two, trace_basisProj_mul]

lemma qWeight_applyU_bind (p : α → Prop) [DecidablePred p] (U : Matrix W W ℂ) (hU : Uᴴ * U = 1)
    (k : Fin (0 + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (applyU U hU >>= k) ρ = qWeight p (k 0) (U * ρ * Uᴴ) := by
  rw [applyU, qWeight_instr_bind]
  simp [unitaryIdx]

/-- **Hadamard then measure: each outcome has weight `1/2`.** -/
theorem qWeight_hMeasure (i : Fin 2) :
    qWeight (· = i) (hMeasure (spec := unifSpec)) ket0 = 1 / 2 := by
  rw [hMeasure, qWeight_applyU_bind, hadamard_ket0, qWeight_measureBasis]
  fin_cases i <;> simp [ketPlus]

/-- **Hadamard twice then measure: outcome `0` has weight `1`** (the amplitudes of `1` cancel:
interference). -/
theorem qWeight_hhMeasure_zero :
    qWeight (· = 0) (hhMeasure (spec := unifSpec)) ket0 = 1 := by
  rw [hhMeasure, qWeight_applyU_bind, qWeight_applyU_bind, hadamard_ket0, hadamard_ketPlus,
    qWeight_measureBasis]
  simp [ket0]

theorem qWeight_hhMeasure_one :
    qWeight (· = 1) (hhMeasure (spec := unifSpec)) ket0 = 0 := by
  rw [hhMeasure, qWeight_applyU_bind, qWeight_applyU_bind, hadamard_ket0, hadamard_ketPlus,
    qWeight_measureBasis]
  simp [ket0]

/-! ## A syntactic criterion for `RationalBorn`: Gaussian-rational circuits -/

/-- The Gaussian rationals `ℚ(i)` inside `ℂ`. -/
def gaussRat : Subring ℂ where
  carrier := {z | (∃ a : ℚ, z.re = a) ∧ ∃ b : ℚ, z.im = b}
  mul_mem' := by
    rintro z w ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨⟨a * c - b * d, by simp [ha, hb, hc, hd]⟩, ⟨a * d + b * c, by simp [ha, hb, hc, hd]⟩⟩
  one_mem' := ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩
  add_mem' := by
    rintro z w ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨c, hc⟩, ⟨d, hd⟩⟩
    exact ⟨⟨a + c, by simp [ha, hc]⟩, ⟨b + d, by simp [hb, hd]⟩⟩
  zero_mem' := ⟨⟨0, by simp⟩, ⟨0, by simp⟩⟩
  neg_mem' := by
    rintro z ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨-a, by simp [ha]⟩, ⟨-b, by simp [hb]⟩⟩

lemma star_mem_gaussRat {z : ℂ} (h : z ∈ gaussRat) : star z ∈ gaussRat := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := h
  exact ⟨⟨a, by simp [ha]⟩, ⟨-b, by simp [hb]⟩⟩

lemma ratCast_mem_gaussRat (q : ℚ) : (q : ℂ) ∈ gaussRat :=
  ⟨⟨q, by simp⟩, ⟨0, by simp⟩⟩

/-- A matrix with Gaussian-rational entries. -/
def GRMat (ρ : Matrix W W ℂ) : Prop := ∀ a b, ρ a b ∈ gaussRat

omit [DecidableEq W] in
lemma GRMat.mul {A B : Matrix W W ℂ} (hA : GRMat A) (hB : GRMat B) : GRMat (A * B) := fun a b ↦ by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ ↦ Subring.mul_mem _ (hA a c) (hB c b)

omit [Fintype W] [DecidableEq W] in
lemma GRMat.conjTranspose {A : Matrix W W ℂ} (hA : GRMat A) : GRMat Aᴴ := fun a b ↦ by
  rw [Matrix.conjTranspose_apply]
  exact star_mem_gaussRat (hA b a)

omit [Fintype W] [DecidableEq W] in
lemma GRMat.smul {A : Matrix W W ℂ} {c : ℂ} (hc : c ∈ gaussRat) (hA : GRMat A) :
    GRMat (c • A) := fun a b ↦ by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ hc (hA a b)

omit [DecidableEq W] in
lemma GRMat.trace_re {A : Matrix W W ℂ} (hA : GRMat A) : ∃ q : ℚ, A.trace.re = q :=
  (Subring.sum_mem gaussRat fun c _ ↦ hA c c).1

omit [Fintype W] in
lemma grMat_basisProj (w : W) : GRMat (basisProj w) := fun a b ↦ by
  unfold basisProj
  by_cases h : a = b
  · subst h
    rw [Matrix.diagonal_apply_eq]
    split_ifs
    exacts [Subring.one_mem _, Subring.zero_mem _]
  · rw [Matrix.diagonal_apply_ne _ h]
    exact Subring.zero_mem _

/-- The instrument maps Gaussian-rational matrices to Gaussian-rational matrices. -/
def GRIdx (j : InstrIdx W) : Prop := ∀ ρ, GRMat ρ → ∀ i, GRMat (j.2.1.branch i ρ)

/-- A unitary `c • K` with `K` Gaussian-rational and `|c|²` Gaussian-rational (e.g. a Hadamard
gate, `c = 1/√2`) preserves Gaussian-rational states. -/
lemma grIdx_unitaryIdx_smul (c : ℂ) (K : Matrix W W ℂ) (hc : c * star c ∈ gaussRat)
    (hK : GRMat K) (hU : (c • K)ᴴ * (c • K) = 1) : GRIdx (unitaryIdx (c • K) hU) := by
  intro ρ hρ i
  have : (unitaryIdx (c • K) hU).2.1.branch i ρ = (c * star c) • (K * ρ * Kᴴ) := by
    simp [unitaryIdx, Matrix.conjTranspose_smul, smul_smul, mul_comm]
  rw [this]
  exact ((hK.mul hρ).mul hK.conjTranspose).smul hc

/-- A Gaussian-rational unitary (permutation gates such as CNOT and Toffoli, Pauli gates, `S`)
preserves Gaussian-rational states. -/
lemma grIdx_unitaryIdx (U : Matrix W W ℂ) (hK : GRMat U) (hU : Uᴴ * U = 1) :
    GRIdx (unitaryIdx U hU) := by
  intro ρ hρ i
  have : (unitaryIdx U hU).2.1.branch i ρ = U * ρ * Uᴴ := by simp [unitaryIdx]
  rw [this]
  exact (hK.mul hρ).mul hK.conjTranspose

/-- The computational-basis measurement preserves Gaussian-rational states. -/
lemma grIdx_measureIdx {n : ℕ} (e : Fin (n + 1) ≃ W) : GRIdx (measureIdx e) := by
  intro ρ hρ i
  have : (measureIdx e).2.1.branch i ρ = basisProj (e i) * ρ * basisProj (e i) := by
    simp [measureIdx]
  rw [this]
  exact ((grMat_basisProj _).mul hρ).mul (grMat_basisProj _)

omit [Fintype W] [DecidableEq W] in
/-- Permutation matrices are Gaussian-rational. -/
lemma grMat_of_zero_one (U : Matrix W W ℂ) (h : ∀ a b, U a b = 0 ∨ U a b = 1) : GRMat U :=
  fun a b ↦ by
    rcases h a b with h | h <;> rw [h]
    exacts [Subring.zero_mem _, Subring.one_mem _]

/-- Every instrument node of the machine satisfies `P`. -/
def UsesOnly (P : InstrIdx W → Prop) (Q : QOC W spec α) : Prop :=
  OracleComp.construct (C := fun _ ↦ Prop) (fun _ ↦ True)
    (fun t _ ih ↦
      match t, ih with
      | .inl j, ih => P j ∧ ∀ i, ih i
      | .inr _, ih => ∀ u, ih u) Q

omit [DecidableEq W] in
@[simp] lemma usesOnly_pure (P : InstrIdx W → Prop) (a : α) :
    UsesOnly P (pure a : QOC W spec α) := trivial

omit [DecidableEq W] in
lemma usesOnly_instr_bind (P : InstrIdx W → Prop) (j : InstrIdx W)
    (k : Fin (j.1 + 1) → QOC W spec α) :
    UsesOnly P (liftM ((instrSpec W + spec).query (Sum.inl j)) >>= k) ↔
      P j ∧ ∀ i, UsesOnly P (k i) := Iff.rfl

omit [DecidableEq W] in
lemma usesOnly_query_bind (P : InstrIdx W → Prop) (t : spec.Domain)
    (k : spec.Range t → QOC W spec α) :
    UsesOnly P (liftM ((instrSpec W + spec).query (Sum.inr t)) >>= k) ↔
      ∀ u, UsesOnly P (k u) := Iff.rfl

omit [DecidableEq W] in
/-- The criterion is compositional. -/
lemma usesOnly_bind (P : InstrIdx W → Prop) (Q : QOC W spec α) (F : α → QOC W spec β)
    (hQ : UsesOnly P Q) (hF : ∀ a, UsesOnly P (F a)) : UsesOnly P (Q >>= F) := by
  induction Q using OracleComp.inductionOn with
  | pure a => simpa using hF a
  | query_bind t k ih =>
    rcases t with j | t
    · rw [usesOnly_instr_bind] at hQ
      rw [bind_assoc, usesOnly_instr_bind]
      exact ⟨hQ.1, fun i ↦ ih i (hQ.2 i)⟩
    · rw [usesOnly_query_bind] at hQ
      rw [bind_assoc, usesOnly_query_bind]
      exact fun u ↦ ih u (hQ u)

omit [DecidableEq W] in
/-- **Syntactic criterion.**  A machine all of whose instruments preserve Gaussian-rational
matrices, started in a Gaussian-rational state, has rational Born probabilities. -/
theorem rationalBorn_of_usesOnly (Q : QOC W spec α) (hQ : UsesOnly GRIdx Q) (ρ : Matrix W W ℂ)
    (hρ : GRMat ρ) : RationalBorn Q ρ := by
  induction Q using OracleComp.inductionOn generalizing ρ with
  | pure a => simp
  | query_bind t k ih =>
    rcases t with j | t
    · rw [usesOnly_instr_bind] at hQ
      rw [rationalBorn_instr_bind]
      refine ⟨fun _ i ↦ ?_, fun i ↦ ih i (hQ.2 i) _ (hQ.1 ρ hρ i)⟩
      obtain ⟨q₁, h₁⟩ := (hQ.1 ρ hρ i).trace_re
      obtain ⟨q₂, h₂⟩ := hρ.trace_re
      exact ⟨q₁ / q₂, by rw [h₁, h₂]; push_cast; rfl⟩
    · rw [usesOnly_query_bind] at hQ
      rw [rationalBorn_query_bind]
      exact fun u ↦ ih u (hQ u) ρ hρ

lemma grMat_ket0 : GRMat ket0 := grMat_of_zero_one _ fun a b ↦ by
  fin_cases a <;> fin_cases b <;> simp [ket0]

lemma grIdx_hadamard : GRIdx (unitaryIdx hadamard hadamard_unitary) := by
  refine grIdx_unitaryIdx_smul hadS !![1, 1; 1, -1] ?_ (fun a b ↦ ?_) hadamard_unitary
  · rw [star_hadS, hadS_mul_self]
    have := ratCast_mem_gaussRat (1 / 2)
    simpa using this
  · fin_cases a <;> fin_cases b <;> simp

lemma usesOnly_measureBasis {n : ℕ} (e : Fin (n + 1) ≃ W) :
    UsesOnly GRIdx (measureBasis (spec := spec) e) := by
  rw [← bind_pure (measureBasis e), measureBasis, usesOnly_instr_bind]
  exact ⟨grIdx_measureIdx e, fun _ ↦ usesOnly_pure _ _⟩

lemma usesOnly_hMeasure : UsesOnly GRIdx (hMeasure (spec := spec)) := by
  rw [hMeasure, applyU, usesOnly_instr_bind]
  exact ⟨grIdx_hadamard, fun _ ↦ usesOnly_measureBasis _⟩

lemma usesOnly_hhMeasure : UsesOnly GRIdx (hhMeasure (spec := spec)) := by
  rw [hhMeasure, applyU, usesOnly_instr_bind]
  refine ⟨grIdx_hadamard, fun _ ↦ ?_⟩
  rw [usesOnly_instr_bind]
  exact ⟨grIdx_hadamard, fun _ ↦ usesOnly_measureBasis _⟩

/-- Both interference machines have rational Born probabilities. -/
theorem rationalBorn_hMeasure : RationalBorn (hMeasure (spec := spec)) ket0 :=
  rationalBorn_of_usesOnly _ usesOnly_hMeasure _ grMat_ket0

theorem rationalBorn_hhMeasure : RationalBorn (hhMeasure (spec := spec)) ket0 :=
  rationalBorn_of_usesOnly _ usesOnly_hhMeasure _ grMat_ket0

/-! ## The quantum EUF-CMA game can be lost and won -/

section game

variable {M PK SK S : Type}

omit [DecidableEq W] in
/-- **The game can be lost.**  Against a scheme whose verification rejects everything, every
quantum forger (rational or not) has advantage `0`. -/
theorem qUnforgeableAdvantage_eq_zero_of_verify_false {sigAlg : SignatureAlg ProbComp M PK SK S}
    (hv : ∀ pk m s, sigAlg.verify pk m s = pure false) (Q : QForger W sigAlg) :
    qUnforgeableAdvantage Q = 0 := by
  unfold qUnforgeableAdvantage qUnforgeableExperiment qSigExperiment
  refine qWeight_bind_eq_zero _ _ _ (fun ks ρ ↦ qWeight_bind_eq_zero _ _ _ (fun r ρ' ↦ ?_) ρ) _
  simp [hv]

/-- A toy scheme on one-bit signatures: the signer always signs with `0`, the verifier accepts
exactly the signature `1`. -/
def bitScheme : SignatureAlg ProbComp Unit Unit Unit (Fin 2) where
  keygen := pure ((), ())
  sign _ _ _ := pure 0
  verify _ _ s := pure (decide (s = 1))

/-- The forger that prepares `|+⟩`, measures, and outputs the outcome as its signature. -/
noncomputable def hForger : QForger (Fin 2) bitScheme where
  main _ := hMeasure >>= fun b ↦ pure ((), b)
  ρ₀ := ket0
  posSemidef := posSemidef_ket0
  trace_eq_one := trace_ket0

/-- The forger that applies Hadamard twice before measuring. -/
noncomputable def hhForger : QForger (Fin 2) bitScheme where
  main _ := hhMeasure >>= fun b ↦ pure ((), b)
  ρ₀ := ket0
  posSemidef := posSemidef_ket0
  trace_eq_one := trace_ket0

/-- The forger that outputs the accepted signature without using its workspace. -/
noncomputable def oneForger : QForger (Fin 2) bitScheme where
  main _ := pure ((), 1)
  ρ₀ := ket0
  posSemidef := posSemidef_ket0
  trace_eq_one := trace_ket0

lemma close_applyU_bind {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp))
    (U : Matrix W W ℂ) (hU : Uᴴ * U = 1) (k : Fin (0 + 1) → QOC W spec α) (s : σ) :
    close impl (applyU U hU >>= k) s = applyU U hU >>= fun i ↦ close impl (k i) s :=
  close_instr_bind impl (unitaryIdx U hU) k s

lemma close_measureBasis_bind {σ : Type} (impl : QueryImpl spec (StateT σ ProbComp)) {n : ℕ}
    (e : Fin (n + 1) ≃ W) (k : Fin (n + 1) → QOC W spec α) (s : σ) :
    close impl (measureBasis e >>= k) s = measureBasis e >>= fun i ↦ close impl (k i) s :=
  close_instr_bind impl (measureIdx e) k s

lemma qWeight_measureBasis_bind (p : α → Prop) [DecidablePred p] {n : ℕ} (e : Fin (n + 1) ≃ W)
    (k : Fin (n + 1) → Closed W α) (ρ : Matrix W W ℂ) :
    qWeight p (measureBasis e >>= k) ρ =
      ∑ i, qWeight p (k i) (basisProj (e i) * ρ * basisProj (e i)) := by
  rw [measureBasis, qWeight_instr_bind]
  simp

/-- **The game can be won with probability exactly `1/2`** by the Hadamard forger. -/
theorem qUnforgeableAdvantage_hForger : qUnforgeableAdvantage hForger = 1 / 2 := by
  unfold qUnforgeableAdvantage qUnforgeableExperiment qSigExperiment
  simp only [bitScheme, hForger, hMeasure, liftU_pure, pure_bind, bind_assoc, close_applyU_bind,
    close_measureBasis_bind, close_pure, qWeight_applyU_bind, qWeight_measureBasis_bind,
    hadamard_ket0, qWeight_pure]
  simp [trace_basisProj_mul, ketPlus]

/-- **Interference in the game**: after a second Hadamard the same forger never wins. -/
theorem qUnforgeableAdvantage_hhForger : qUnforgeableAdvantage hhForger = 0 := by
  unfold qUnforgeableAdvantage qUnforgeableExperiment qSigExperiment
  simp only [bitScheme, hhForger, hhMeasure, liftU_pure, pure_bind, bind_assoc,
    close_applyU_bind, close_measureBasis_bind, close_pure, qWeight_applyU_bind,
    qWeight_measureBasis_bind, hadamard_ket0, hadamard_ketPlus, qWeight_pure]
  simp [trace_basisProj_mul, ket0]

/-- **The game can be won with probability `1`.** -/
theorem qUnforgeableAdvantage_oneForger : qUnforgeableAdvantage oneForger = 1 := by
  unfold qUnforgeableAdvantage qUnforgeableExperiment qSigExperiment
  simp [bitScheme, oneForger, trace_ket0]

/-- The Hadamard forger is covered by the lifting theorem: its classical strategy wins the
classical EUF-CMA game with the same probability `1/2`. -/
theorem unforgeableAdvantage_hForger_toClassical :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp hForger.toClassical = 1 / 2 := by
  rw [← qUnforgeableAdvantage_eq hForger fun _ ↦ ?_, qUnforgeableAdvantage_hForger]
  exact rationalBorn_of_usesOnly _ (usesOnly_bind _ _ _ usesOnly_hMeasure fun _ ↦ usesOnly_pure _ _)
    _ grMat_ket0

end game

end PQ.Interactive

open PQ.Interactive in
#print axioms qWeight_hMeasure
open PQ.Interactive in
#print axioms qWeight_hhMeasure_zero
open PQ.Interactive in
#print axioms rationalBorn_of_usesOnly
open PQ.Interactive in
#print axioms rationalBorn_hhMeasure
open PQ.Interactive in
#print axioms qUnforgeableAdvantage_eq_zero_of_verify_false
open PQ.Interactive in
#print axioms qUnforgeableAdvantage_hForger
open PQ.Interactive in
#print axioms qUnforgeableAdvantage_hhForger
open PQ.Interactive in
#print axioms unforgeableAdvantage_hForger_toClassical
