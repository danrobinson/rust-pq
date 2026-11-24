import Integration.SlhDsaCompressionDatabase

/-! Adaptive instruments on the coherent address and response/workspace registers.
Branch amplitudes keep their Born weights, so no conditioning or renormalization
is required at intermediate measurements. -/
namespace Reduction.Compression.Recording.Database.Adaptive
set_option linter.unusedSectionVars false

variable {X Y T V I J : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype I] [Fintype J] [DecidableEq T]

structure Instrument (X V J : Type) [Fintype X] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype J] where
  kraus : J → Work X V →ₗ[ℝ] Work X V
  complete : ∀ v, ∑ j, ‖kraus j v‖^2 = ‖v‖^2

noncomputable def branch (K : I → Instrument X V J) (ψ : I → Wave X Y V) :
    I × J → Wave X Y V := fun ij x d => (K ij.1).kraus ij.2 (WithLp.toLp 2 (fun x => ψ ij.1 x d)) x

private theorem branch_slice (K : I → Instrument X V J) (ψ : I → Wave X Y V) (i : I) (d : DB X Y) :
    ∑ j, ∑ x, ‖branch K ψ (i,j) x d‖^2 = ∑ x, ‖ψ i x d‖^2 := by
  simpa only [PiLp.norm_sq_eq_of_L2, branch] using
    (K i).complete (WithLp.toLp 2 (fun x => ψ i x d))

theorem branch_mass (K : I → Instrument X V J) (ψ : I → Wave X Y V) :
    ∑ ij, mass (branch K ψ ij) = ∑ i, mass (ψ i) := by
  simp only [Fintype.sum_prod_type, mass]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.sum_comm (f := fun x d => ‖branch K ψ (i,_) x d‖^2)]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x d => ‖ψ i x d‖^2)]
  exact Finset.sum_congr rfl fun d _ => branch_slice K ψ i d

theorem branch_bad (p : Y → T) (K : I → Instrument X V J) (ψ : I → Wave X Y V) :
    ∑ ij, badMass p (branch K ψ ij) = ∑ i, badMass p (ψ i) := by
  classical
  simp only [Fintype.sum_prod_type, badMass]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [Finset.sum_comm (f := fun x d => if Collision p d then ‖branch K ψ (i,_) x d‖^2 else 0)]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x d => if Collision p d then ‖ψ i x d‖^2 else 0)]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : Collision p d <;> simp [h,branch_slice]

theorem branch_sparse (K : I → Instrument X V J) (ψ : I → Wave X Y V)
    (t : ℕ) (hs : ∀ i, Sparse t (ψ i)) : ∀ ij, Sparse t (branch K ψ ij) := by
  intro ij x d h
  have z : (WithLp.toLp 2 (fun x => ψ ij.1 x d) : Work X V) = 0 := by
    ext j
    exact hs ij.1 j d h
  simp [branch,z]

private theorem mn (ψ : Wave X Y V) : 0 ≤ mass ψ :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
private theorem bn (p : Y → T) (ψ : Wave X Y V) : 0 ≤ badMass p ψ := by
  classical
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun d _ => by
    split <;> first | exact sq_nonneg _ | exact le_rfl

private theorem combined (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (O : I → X → Option Y → V ≃ₗᵢ[ℝ] V) (ψ : I → Wave X Y V) (t : ℕ)
    (hs : ∀ i, Sparse t (ψ i)) :
    Real.sqrt (∑ i, badMass p (call (O i) (ψ i))) ≤
      Real.sqrt (∑ i, badMass p (ψ i)) + 4 * Real.sqrt ((t : ℝ)/N) * Real.sqrt (∑ i, mass (ψ i)) := by
  let a := 4 * Real.sqrt ((t : ℝ)/N)
  have ha : 0 ≤ a := by unfold a; positivity
  have bm : 0 ≤ ∑ i, badMass p (ψ i) := Finset.sum_nonneg fun i _ => bn p _
  have sm : 0 ≤ ∑ i, mass (ψ i) := Finset.sum_nonneg fun i _ => mn _
  have hx : ∑ i, (1:ℝ) * (Real.sqrt (badMass p (ψ i)))^2 ≤ (Real.sqrt (∑ i, badMass p (ψ i)))^2 := by
    simp only [one_mul, Real.sq_sqrt (bn p _), Real.sq_sqrt bm, le_refl]
  have hy : ∑ i, (1:ℝ) * (a * Real.sqrt (mass (ψ i)))^2 ≤ (a * Real.sqrt (∑ i, mass (ψ i)))^2 := by
    simp only [one_mul,mul_pow,Real.sq_sqrt (mn _),Real.sq_sqrt sm,Finset.mul_sum,le_refl]
  have h := PQ.QROM.Purify.sum_mul_add_sq_le (fun _ : I => (1:ℝ))
    (fun i => Real.sqrt (badMass p (ψ i))) (fun i => a * Real.sqrt (mass (ψ i))) (fun _ => by norm_num)
    (Real.sqrt_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _)) hx hy
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _)))).mpr
  apply le_trans _ h
  refine Finset.sum_le_sum fun i _ => ?_
  have hi := call_bad_amplitude p N hN uniform (O i) (ψ i) t (hs i)
  change Real.sqrt _ ≤ Real.sqrt _ + a * Real.sqrt _ at hi
  have sq := (sq_le_sq₀ (Real.sqrt_nonneg _) (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _)))).mpr hi
  simpa only [one_mul,Real.sq_sqrt (bn p _)] using sq

noncomputable def step (K : I → Instrument X V J) (O : I × J → X → Option Y → V ≃ₗᵢ[ℝ] V)
    (ψ : I → Wave X Y V) (ij : I × J) := call (O ij) (branch K ψ ij)

theorem step_amp (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (K : I → Instrument X V J) (O : I × J → X → Option Y → V ≃ₗᵢ[ℝ] V)
    (ψ : I → Wave X Y V) (t : ℕ) (hs : ∀ i, Sparse t (ψ i)) :
    Real.sqrt (∑ ij, badMass p (step K O ψ ij)) ≤ Real.sqrt (∑ i, badMass p (ψ i)) +
      4 * Real.sqrt ((t : ℝ)/N) * Real.sqrt (∑ i, mass (ψ i)) := by
  simpa only [step, branch_bad,branch_mass] using combined p N hN uniform O (branch K ψ) t (branch_sparse K ψ t hs)

/-- A transcript gains an outcome at each step. Both the next measurement and
the public-port operation may depend on the entire existing transcript. -/
inductive Execution (η : X → V) : (t : ℕ) → {I : Type} → [Fintype I] → (I → Wave X Y V) → Prop
  | start : Execution η 0 (fun _ : Unit => emptyStart η)
  | next {t : ℕ} {I J : Type} [Fintype I] [Fintype J] {ψ : I → Wave X Y V}
      (prior : Execution η t ψ) (K : I → Instrument X V J) (O : I × J → X → Option Y → V ≃ₗᵢ[ℝ] V) :
      Execution η (t+1) (step K O ψ)

private theorem step_mass (K : I → Instrument X V J) (O : I × J → X → Option Y → V ≃ₗᵢ[ℝ] V)
    (ψ : I → Wave X Y V) : ∑ ij, mass (step K O ψ ij) = ∑ i, mass (ψ i) := by
  simpa only [step,call_mass] using branch_mass K ψ

private theorem invariant (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (η : X → V) (norm : ∑ x, ‖η x‖^2 = 1) {t : ℕ} {ψ : I → Wave X Y V} (exec : Execution η t ψ) :
    (∀ i, Sparse t (ψ i)) ∧ (∑ i, mass (ψ i)) = 1 ∧
      Real.sqrt (∑ i, badMass p (ψ i)) ≤ (t : ℝ) * (4 * Real.sqrt ((t : ℝ) / N)) := by
  induction exec with
  | start =>
    exact ⟨fun _ => empty_sparse η,by simp [empty_mass,norm],by simp [empty_badMass]⟩
  | @next t I J fi fj ψ prior K O ih =>
    obtain ⟨sparse,total,amp⟩ := ih
    refine ⟨fun ij => call_sparse _ _ t (branch_sparse K ψ t sparse ij),
      (step_mass K O ψ).trans total, ?_⟩
    have h := step_amp p N hN uniform K O ψ t sparse
    rw [total,Real.sqrt_one,mul_one] at h
    apply h.trans
    have mono : Real.sqrt ((t:ℝ)/N) ≤ Real.sqrt (((t:ℝ)+1)/N) :=
      Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hN.le)
    push_cast
    calc _ ≤ ((t:ℝ)+1) * (4 * Real.sqrt ((t:ℝ)/N)) := by linarith
         _ ≤ _ := by gcongr

/-- Unconditional collision probability summed across all observed transcripts,
including measurements with outcome-dependent subsequent operations. -/
theorem collision_bound (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T,
      (((Finset.univ.filter fun y => p y ∈ B).card : ℝ) / Fintype.card Y) ≤ (B.card : ℝ) / N)
    (η : X → V) (norm : ∑ x, ‖η x‖^2 = 1) (q : ℕ) (ψ : I → Wave X Y V) (exec : Execution η q ψ) :
    (∑ i, badMass p (ψ i)) ≤ 16 * (q : ℝ)^3 / N := by
  have amp := (invariant p N hN uniform η norm exec).2.2
  have sq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr amp
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => bn p _)] at sq
  apply sq.trans_eq
  rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
  ring

open MLink Ideal MIdeal.Sha512 in
theorem sha512_collision_bound (S : Sha2Set) (η : X → V) (norm : ∑ x, ‖η x‖^2 = 1)
    (q : ℕ) (ψ : I → Wave X Chain512 V) (exec : Execution η q ψ) :
    (∑ i, badMass (trunc S) (ψ i)) ≤ 16 * (q : ℝ)^3 / 2^(8*S.vp.params.n) :=
  collision_bound (trunc S) _ (by positivity) (fun B => (prefixCells_fraction S B).le) η norm q ψ exec

end Reduction.Compression.Recording.Database.Adaptive
#print axioms Reduction.Compression.Recording.Database.Adaptive.step_amp
#print axioms Reduction.Compression.Recording.Database.Adaptive.sha512_collision_bound
