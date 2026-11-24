import Integration.SlhDsaShakePermutationMsgCondition

namespace Reduction.ShakePermutation.MsgTrajectory
open MLink SLHDSA Classical SetOracle ENNReal OracleComp OracleComp.PermutationConditioning
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
variable (S : Sha2Set)
attribute [local instance] singletonFintype

def probe (π : Permutation) (p : Port) := if p.1 then p.2 else π p.2

def hit (π σ : Permutation) (k : S.Node) (p : Port) :=
  let a := probe π p
  (SkFormat.split S (π.symm a)).1 = k ∨ ∃ j, σ (column S k j) = a

theorem outside_hit (π σ : Permutation) (k : S.Node) (p : Port) (clear : ¬hit S π σ k p) :
    oracle (programmed S k π σ) p = oracle π p := by
  let a := probe π p
  have old : a ∉ Set.range (imageTuple (column S k) π) := by
    rintro ⟨j,e⟩
    apply clear ∘ Or.inl
    change π (column S k j) = a at e
    change (SkFormat.split S (π.symm a)).1 = k
    rw [← e,Equiv.symm_apply_apply]
    exact congrArg Prod.fst ((SkFormat.split S).apply_symm_apply (k,j))
  have new : a ∉ Set.range (imageTuple (column S k) σ) :=
    fun ⟨j,e⟩ => clear (Or.inr ⟨j,e⟩)
  have fixed := Program.reassign_miss _ _ _ old new
  rcases p with ⟨d,w⟩
  cases d with
  | false => exact fixed
  | true => exact congrArg π.symm ((Equiv.symm_apply_eq (e:=Program.reassign _ _)).mpr fixed.symm)

def posterior (π : Permutation) (bs : List Rate) (r : S.Node) (x : S.Node → Words)
    (f : S.Node → Permutation → ℝ≥0∞) :=
  uniformMean (fun k : S.Node => uniformMean (fun t : SkFormat.Suffix S =>
    uniformMean (fun σ : Extensions [(x k,firstState S π bs r t)] => f k σ.val)))

private theorem add_avg {B : Type} [Fintype B] (f g : B → ℝ≥0∞) :
    uniformMean (fun b => f b+g b) = uniformMean f+uniformMean g := by
  simp only [uniformMean,mul_add,Finset.sum_add_distrib]

private theorem const_avg {B : Type} [Fintype B] [Nonempty B] (c : ℝ≥0∞) : uniformMean (fun _ : B => c) = c := by
  simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]

def exposure := 1/(Fintype.card S.Node : ℝ≥0∞) + (1/(Fintype.card (SkFormat.Suffix S) : ℝ≥0∞) +
    (Fintype.card (SkFormat.Suffix S) : ℝ≥0∞)*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞)))

/-- Posterior mass of both old and new images at an arbitrary coherent
public query address after the truncated challenge has been returned. -/
theorem exposure_bound (π : Permutation) (bs : List Rate) (r : S.Node) (x : S.Node → Words) (p : Port) :
    posterior S π bs r x (fun k σ => if hit S π σ k p then (1:ℝ≥0∞) else 0) ≤ exposure S := by
  classical
  let a := probe π p
  let owner := (SkFormat.split S (π.symm a)).1
  let old (k : S.Node) : ℝ≥0∞ := if owner = k then 1 else 0
  let D := 1/(Fintype.card (SkFormat.Suffix S):ℝ≥0∞) + Fintype.card (SkFormat.Suffix S)*(1/((Fintype.card Words-1:ℕ):ℝ≥0∞))
  let cost (k : S.Node) := uniformMean (fun t : SkFormat.Suffix S =>
    uniformMean (fun σ : Extensions [(x k,firstState S π bs r t)] => if hit S π σ.val k p then (1:ℝ≥0∞) else 0))
  have bound (k : S.Node) : cost k ≤ old k + D := by
    by_cases h : owner = k
    · rw [show old k = 1 by simp [old,h]]
      exact (ShakeXof.mean_le_const (fun t => by
        let s := firstState S π bs r t
        let _ : Nonempty (Extensions [(x k,s)]) := ⟨Equiv.swap (x k) s,by simp⟩
        apply ShakeXof.mean_le_const; intro σ; split <;> simp)).trans (le_self_add : (1:ℝ≥0∞) ≤ 1+D)
    · rw [show old k = 0 by simp [old,h],zero_add]
      have le := posterior_target S (column S k) π bs r (x k) a
      apply le_trans _ le
      apply Finset.sum_le_sum; intro t _
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum; intro σ _
      apply mul_le_mul' le_rfl
      dsimp only
      by_cases e : ∃ j, σ.val (column S k j) = a
      · simp only [ite_eq_left (show hit S π σ.val k p from Or.inr e),ite_eq_left e,le_rfl]
      · simp only [ite_eq_right (show ¬hit S π σ.val k p from fun z => z.elim h e),ite_eq_right e,le_rfl]
  have h := Finset.sum_le_sum (s:=Finset.univ) fun k _ => mul_le_mul' (le_rfl : unifW _ k ≤ _) (bound k)
  apply h.trans
  change uniformMean (fun k => old k + D) ≤ _
  rw [add_avg,const_avg]
  apply add_le_add _ le_rfl
  simp [old,uniformMean,unifW,mul_ite]

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.exposure_bound
