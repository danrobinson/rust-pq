import Integration.SlhDsaCompressionReadout

namespace Reduction.Compression.Recording.Database
set_option linter.unusedSectionVars false
variable {X Y T V V' E : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup V'] [InnerProductSpace ℝ V']
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def splitAtWork (L : V ≃ₗᵢ[ℝ] Work X E) (v : DB X Y → V) : Wave X Y E :=
  fun x d => L (v d) x

noncomputable def joinAtWork (R : V' ≃ₗᵢ[ℝ] Work X E) (ψ : Wave X Y E) : DB X Y → V' :=
  fun d => R.symm (WithLp.toLp 2 (fun x => ψ x d))

/-- A concrete query with potentially different input and output workspace
types, both identified with the joint address/response/workspace register. -/
noncomputable def reindexCall (L : V ≃ₗᵢ[ℝ] Work X E) (R : V' ≃ₗᵢ[ℝ] Work X E)
    (O : X → Option Y → E ≃ₗᵢ[ℝ] E) (v : DB X Y → V) : DB X Y → V' :=
  joinAtWork R (call O (splitAtWork L v))

private theorem split_norm (L : V ≃ₗᵢ[ℝ] Work X E) (v : DB X Y → V) (d : DB X Y) :
    ∑ x, ‖splitAtWork L v x d‖^2 = ‖v d‖^2 := by
  exact (PiLp.norm_sq_eq_of_L2 _ (L (v d))).symm.trans (congrArg (fun z : ℝ => z^2) (L.norm_map (v d)))

theorem split_mass (L : V ≃ₗᵢ[ℝ] Work X E) (v : DB X Y → V) : mass (splitAtWork L v) = ∑ d, ‖v d‖^2 := by
  unfold mass
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => split_norm L v d

theorem split_bad (p : Y → T) (L : V ≃ₗᵢ[ℝ] Work X E) (v : DB X Y → V) :
    badMass p (splitAtWork L v) = sumWeight (Collision p) v := by
  classical
  unfold badMass sumWeight
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases h : Collision p d <;> simp [h,split_norm]

theorem split_join (R : V' ≃ₗᵢ[ℝ] Work X E) (ψ : Wave X Y E) :
    splitAtWork R (joinAtWork R ψ) = ψ := by funext x d; simp [splitAtWork,joinAtWork]

theorem reindexCall_mass (L : V ≃ₗᵢ[ℝ] Work X E) (R : V' ≃ₗᵢ[ℝ] Work X E)
    (O : X → Option Y → E ≃ₗᵢ[ℝ] E) (v : DB X Y → V) :
    ∑ d, ‖reindexCall L R O v d‖^2 = ∑ d, ‖v d‖^2 := by
  rw [← split_mass R, reindexCall, split_join, call_mass,split_mass]

theorem reindexCall_sparse (L : V ≃ₗᵢ[ℝ] Work X E) (R : V' ≃ₗᵢ[ℝ] Work X E)
    (O : X → Option Y → E ≃ₗᵢ[ℝ] E) (v : DB X Y → V) (t : ℕ)
    (hv : ∀ d, t < (occupied d).card → v d = 0) :
    ∀ d, t+1 < (occupied d).card → reindexCall L R O v d = 0 := by
  intro d hd
  have sp : Sparse t (splitAtWork L v) := fun x e he => by simp [splitAtWork,hv e he]
  have h := call_sparse O _ t sp
  have z : (WithLp.toLp 2 (fun x => call O (splitAtWork L v) x d) : Work X E) = 0 := by
    ext x
    exact h x d hd
  simp [reindexCall,joinAtWork,z]

theorem reindexCall_bad_amplitude [DecidableEq T] (p : Y → T) (N : ℝ) (hN : 0 < N)
    (uniform : ∀ B : Finset T, ((Finset.univ.filter fun y => p y ∈ B).card : ℝ) /
      Fintype.card Y ≤ (B.card : ℝ)/N)
    (L : V ≃ₗᵢ[ℝ] Work X E) (R : V' ≃ₗᵢ[ℝ] Work X E)
    (O : X → Option Y → E ≃ₗᵢ[ℝ] E) (v : DB X Y → V) (t : ℕ)
    (hv : ∀ d, t < (occupied d).card → v d = 0) :
    Real.sqrt (sumWeight (Collision p) (reindexCall L R O v)) ≤
      Real.sqrt (sumWeight (Collision p) v) + 4 * Real.sqrt ((t:ℝ)/N) * Real.sqrt (∑ d, ‖v d‖^2) := by
  have sp : Sparse t (splitAtWork L v) := fun x e he => by simp [splitAtWork,hv e he]
  rw [← split_bad p R, reindexCall,split_join,← split_bad p L,← split_mass L]
  exact call_bad_amplitude p N hN uniform O _ t sp

theorem tensor_reindexCall (L : V ≃ₗᵢ[ℝ] Work X E) (R : V' ≃ₗᵢ[ℝ] Work X E)
    (O : X → Option Y → E ≃ₗᵢ[ℝ] E) (v : DB X Y → V) (d : DB X Y) :
    tensor (reindexCall L R O v) d =
      R.symm (WithLp.toLp 2 (fun x => O x (d x) (L (tensor v d) x))) := by
  apply R.injective
  rw [R.apply_symm_apply]
  ext x
  change (R (∑ e : DB X Y, coeffDB d e • reindexCall L R O v e)) x = _
  rw [map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, reindexCall, joinAtWork,
    LinearIsometryEquiv.apply_symm_apply]
  change decode (call O (splitAtWork L v)) x d = O x (d x) (L (tensor v d) x)
  rw [decode_call]
  congr 1
  unfold decode tensor splitAtWork
  rw [map_sum]
  simp [WithLp.ofLp_sum]

end Reduction.Compression.Recording.Database
#print axioms Reduction.Compression.Recording.Database.tensor_reindexCall
#print axioms Reduction.Compression.Recording.Database.reindexCall_sparse
#print axioms Reduction.Compression.Recording.Database.reindexCall_bad_amplitude
