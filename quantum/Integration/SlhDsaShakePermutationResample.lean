import Integration.SlhDsaShakePermutationProgram
import Integration.SlhDsaSetClosed

namespace Reduction.ShakePermutation.Program
open Classical ENNReal
variable {J : Type} (a : J → Words)
def pair (π : Permutation) (t : J → Words) : Bool × J → Words
  | (false,j) => π (a j)
  | (true,j) => t j

noncomputable def resample (s : Permutation × (J → Words)) : Permutation × (J → Words) :=
  if ok : Function.Injective (pair a s.1 s.2) then
    (s.1.trans (exchange ⟨_,ok⟩),s.1 ∘ a)
  else s

private theorem exchange_flip (f : (Bool × J) ↪ Words) :
    exchange (flip.toEmbedding.trans f) = exchange f := by
  apply Equiv.ext
  intro w
  by_cases mem : w ∈ Set.range f
  · obtain ⟨⟨b,j⟩,rfl⟩ := mem
    have back : (flip.toEmbedding.trans f) (!b,j) = f (b,j) := by simp [flip]
    rw [← back,exchange_hit,back,exchange_hit]
    cases b <;> rfl
  · have out : w ∉ Set.range (flip.toEmbedding.trans f) := fun ⟨t,eq⟩ => mem ⟨flip t,eq⟩
    rw [exchange_miss _ _ out,exchange_miss _ _ mem]

theorem resample_involutive : Function.Involutive (resample a) := by
  rintro ⟨π,t⟩
  by_cases ok : Function.Injective (pair a π t)
  · let f : (Bool × J) ↪ Words := ⟨_,ok⟩
    let τ := π.trans (exchange f)
    have old (j : J) : τ (a j) = t j := exchange_hit f false j
    have stage : pair a τ (π ∘ a) = (flip.toEmbedding.trans f) := by
      funext b
      rcases b with ⟨b,j⟩
      cases b
      · exact old j
      · rfl
    have next : Function.Injective (pair a τ (π ∘ a)) := stage ▸ (flip.toEmbedding.trans f).injective
    have name : (⟨pair a τ (π ∘ a),next⟩ : (Bool × J) ↪ Words) = flip.toEmbedding.trans f :=
      DFunLike.ext _ _ (congrFun stage)
    have first : resample a (π,t) = (τ,π ∘ a) := by simp only [resample,dite_eq_left ok,τ,f]
    rw [first,resample,dite_eq_left next]
    apply Prod.ext
    · change τ.trans (exchange ⟨_,next⟩) = π
      rw [name,exchange_flip]
      exact Equiv.ext fun w => exchange_self f (π w)
    · exact funext old
  · have fixed : resample a (π,t) = (π,t) := by simp only [resample,dite_eq_right ok]
    rw [fixed,fixed]

/-- Exchange all designated outputs with an independent uniform table on
the collision-free branch. Leaving collision branches fixed makes this
an exact involution on the full sample space. -/
theorem resample_law [Fintype J] (W : Permutation → (J → Words) → ℝ≥0∞) :
    SetOracle.uniformMean (fun π => SetOracle.uniformMean (W π)) =
      SetOracle.uniformMean (fun π => SetOracle.uniformMean (fun t =>
        W (resample a (π,t)).1 (resample a (π,t)).2)) := by
  classical
  let e := Function.Involutive.toPerm _ (resample_involutive a)
  have h := Equiv.sum_comp e (fun s => unifW Permutation s.1 * (unifW (J → Words) s.2 * W s.1 s.2))
  have he (s) : e s = resample a s := rfl
  simp only [he] at h
  simpa only [SetOracle.uniformMean,Finset.mul_sum,Fintype.sum_prod_type,unifW] using h.symm

end Reduction.ShakePermutation.Program
#print axioms Reduction.ShakePermutation.Program.resample_law
