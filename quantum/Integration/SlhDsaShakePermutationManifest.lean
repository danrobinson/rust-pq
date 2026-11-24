import Integration.SlhDsaShakePermutationFix
import Integration.SlhDsaShakeXofRows

/-! Exact two-way permutation coupling for a fixed family of overwrite paths
with distinct terminal capacities. It uses the truthful fixed capacity masks,
so every public call uses the same whole permutation in either direction. -/
namespace Reduction.ShakePermutation.Manifest
open Classical Quantum Fix ShakeXof ENNReal

@[simp] theorem cap_shear (h : RateMask) (w : Words) : capOf (shear h w) = capOf w := cap_join ..
@[simp] theorem rate_shear (h : RateMask) (w : Words) : rateOf (shear h w) = rateXor (rateOf w) (h (capOf w)) := rate_join ..

theorem xor_comm (r s : Rate) : rateXor r s = rateXor s r := by
  funext i; exact UInt64.xor_comm ..

theorem cap_independent (π : Permutation) (h : RateMask) (p : List Rate) :
    capOf (overwrite (π.trans (shearEquiv h)) p) = capOf (overwrite π p) := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p r ih =>
    simp only [overwrite,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change capOf (shear h (π (join r (capOf (overwrite (π.trans (shearEquiv h)) p))))) = _
    rw [ih,cap_shear]
    rfl

theorem final_shear (π : Permutation) (h : RateMask) (p : List Rate) (ne : p ≠ []) :
    overwrite (π.trans (shearEquiv h)) p = shear h (overwrite π p) := by
  cases p using List.reverseRecOn with
  | nil => contradiction
  | append_singleton p r =>
    simp only [overwrite,List.foldl_append,List.foldl_cons,List.foldl_nil]
    change shear h (π (join r (capOf (overwrite (π.trans (shearEquiv h)) p)))) = _
    rw [cap_independent]
    rfl

variable {I : Type} (cap : I ↪ Capacity) (head : I → Rate)

def observe (h : RateMask) : I → Rate := fun i => rateXor (h (cap i)) (head i)

noncomputable def program (h : RateMask) (f : I → Rate) : RateMask :=
  fun z => (locate cap z).elim (h z) (fun i => rateXor (f i) (head i))

theorem observe_program (h : RateMask) (f : I → Rate) : observe cap head (program cap head h f) = f := by
  funext i; simp [observe,program,locate_emb]

theorem program_twice (h : RateMask) (f : I → Rate) :
    program cap head (program cap head h f) (observe cap head h) = h := by
  funext z
  cases e : locate cap z with
  | none => simp [program,e]
  | some i => simp [program,e,observe,located cap e]

variable [Fintype I] [DecidableEq I]

/-- Full joint distribution of the mask and its responses on the named
paths. In the rekeyed experiment the external f is uniform. -/
theorem joint_table (W : RateMask → (I → Rate) → ℝ≥0∞) :
    SetOracle.uniformMean (fun h => W h (observe cap head h)) =
      SetOracle.uniformMean (fun h => SetOracle.uniformMean (fun f => W (program cap head h f) f)) := by
  have inv : Function.Involutive (fun z : RateMask × (I → Rate) =>
      (program cap head z.1 z.2,observe cap head z.1)) := by
    rintro ⟨h,f⟩
    exact Prod.ext (program_twice cap head h f) (observe_program cap head h f)
  have eq := SetOracle.avg_resample (program cap head) (observe cap head) inv (fun h => W h (observe cap head h))
  simpa only [SetOracle.uniformMean,observe_program] using eq

/-- Equality for any experiment consuming the entire shared two-way
permutation and all manifest outputs together, including quantum experiments.
The manifest is fixed before sampling the rate mask. -/
theorem whole_port (π : Permutation) (paths : I → List Rate) (ne : ∀ i, paths i ≠ [])
    (distinct : Function.Injective (fun i => capOf (overwrite π (paths i))))
    (W : Permutation → (I → Rate) → ℝ≥0∞) :
    let c : I ↪ Capacity := ⟨_,distinct⟩
    let pre := fun i => rateOf (overwrite π (paths i))
    SetOracle.uniformMean (fun h => W (π.trans (shearEquiv h))
      (fun i => rateOf (overwrite (π.trans (shearEquiv h)) (paths i)))) =
    SetOracle.uniformMean (fun h => SetOracle.uniformMean (fun f : I → Rate =>
      W (π.trans (shearEquiv (program c pre h f))) f)) := by
  intro c pre
  have obs (h : RateMask) : (fun i => rateOf (overwrite (π.trans (shearEquiv h)) (paths i))) =
      observe c pre h := by
    funext i
    rw [final_shear _ _ _ (ne i),rate_shear]
    exact xor_comm _ _
  simp only [obs]
  exact joint_table c pre (fun h => W (π.trans (shearEquiv h)))

end Reduction.ShakePermutation.Manifest
#print axioms Reduction.ShakePermutation.Manifest.whole_port
