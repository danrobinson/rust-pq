import Integration.SlhDsaShakePermutationSkTargetBound
import Integration.SlhDsaShakePermutationColumnSwap
import Integration.SlhDsaShakePermutationSkMarginal

/-! Average a good-table hidden-key comparison to obtain the SK.PRF
real/ideal ensemble inequality, with the collision loss paid once. -/
namespace Reduction.ShakePermutation.SkCompare
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
open Classical MLink SLHDSA ENNReal SetOracle
open SkFormat
noncomputable section
private theorem avg_const {X : Type} [Fintype X] [Nonempty X] (b : ℝ≥0∞) :
    uniformMean (fun _ : X => b) = b := by
  simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]

private theorem avg_swap {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (f x)) = uniformMean (fun y => uniformMean (fun x => f x y)) := by
  simp only [uniformMean,Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => mul_left_comm ..

private theorem avg_pair {X Y : Type} [Fintype X] [Fintype Y] (f : X × Y → ℝ≥0∞) :
    uniformMean (fun x => uniformMean (fun y => f (x,y))) = uniformMean f := by
  simp only [uniformMean,Fintype.sum_prod_type,unifW,Finset.mul_sum,Fintype.card_prod,Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _)),mul_assoc]

private theorem avg_congr {A : Type} {i j : Fintype A} {f g : A → ℝ≥0∞}
    (h : ∀ a, f a = g a) : @uniformMean A i f = @uniformMean A j g := by
  cases Subsingleton.elim i j
  exact congrArg (@uniformMean A i) (funext h)

private theorem avg_mono {X : Type} [Fintype X] {f g : X → ℝ≥0∞} (h : ∀ x, f x ≤ g x) :
    uniformMean f ≤ uniformMean g := Finset.sum_le_sum fun x _ => mul_le_mul' le_rfl (h x)

private theorem avg_add {X : Type} [Fintype X] (f g : X → ℝ≥0∞) :
    uniformMean (fun x => f x + g x) = uniformMean f + uniformMean g := by
  simp only [uniformMean,mul_add,Finset.sum_add_distrib]

variable (S : Sha2Set)
abbrev Test := Permutation → (PublicRow S → S.Node) → ℝ≥0∞

def old (π : Permutation) (k : S.Node) (j : PublicRow S) := (split S (π (input S (k,j)))).1

private def rerun (B : Test S) (π : Permutation) (k : S.Node) (T : PublicRow S → Words) :=
  let π' := (Program.resample (fun j => input S (k,j)) (π,T)).1
  B π' (old S π' k)

private theorem exchange_mean (B : Test S) (k : S.Node) :
    uniformMean (fun π => B π (old S π k)) =
      uniformMean (fun π => uniformMean (fun w : Targets S =>
        rerun S B π k (fun j => target S w (k,j)))) := by
  let W := fun (π : Permutation) (_ : PublicRow S → Words) => B π (old S π k)
  have res := Program.resample_law (fun j => input S (k,j)) W
  simp only [W,avg_const] at res
  have single (π : Permutation) :
      uniformMean (fun T => rerun S B π k T) =
      uniformMean (fun w : Targets S => rerun S B π k (fun j => target S w (k,j))) := by
    let g := fun w : Targets S => rerun S B π k (fun j => target S w (k,j))
    exact (seed_marginal S k (fun _ T => rerun S B π k T)).symm.trans (avg_pair g)
  refine res.trans (avg_congr fun π => ?_)
  exact (avg_congr (fun _ => rfl)).trans (single π)

private theorem rerun_good (B : Test S) (π : Permutation) (w : Targets S) (k : S.Node)
    (ok : Function.Injective (Program.pair (input S) π (target S w))) :
    rerun S B π k (fun j => target S w (k,j)) =
      B (Program.changed π (Program.labelled (input S) π (target S w) ok) k) w.1 := by
  have keys : old S (Program.resample (fun j => input S (k,j)) (π,fun j => target S w (k,j))).1 k = w.1 := by
    funext j
    rw [old,Program.resampled_output (input S) π (target S w) ok k j,split_target]
  rw [rerun,keys,Program.resample_column (input S) π (target S w) ok k]

theorem compare (B : Test S) (bounded : ∀ π F, B π F ≤ 1) (loss : ℝ≥0∞)
    (good : ∀ (π : Permutation) (w : Targets S)
      (ok : Function.Injective (Program.pair (input S) π (target S w))),
      uniformMean (fun k => B (Program.changed π (Program.labelled (input S) π (target S w) ok) k) w.1) ≤
        B π w.1 + loss) :
    uniformMean (fun π => uniformMean (fun k => B π (old S π k))) ≤
      uniformMean (fun π => uniformMean (B π)) + loss + ((2:ℝ≥0∞)^55)⁻¹ := by
  let score := fun π (w : Targets S) k => rerun S B π k (fun j => target S w (k,j))
  let err := fun π (w : Targets S) => if Function.Injective (Program.pair (input S) π (target S w)) then (0:ℝ≥0∞) else 1
  have point (π : Permutation) (w : Targets S) :
      uniformMean (score π w) ≤ B π w.1 + loss + err π w := by
    by_cases ok : Function.Injective (Program.pair (input S) π (target S w))
    · simpa only [score,rerun_good S B π w _ ok,err,ite_eq_left ok,add_zero] using good π w ok
    · have hb : ∀ k, score π w k ≤ 1 := fun k => bounded _ _
      refine (avg_mono hb).trans ?_
      rw [avg_const]
      simp [err,ok]
  have avg (π : Permutation) : uniformMean (fun w => uniformMean (score π w)) ≤
      uniformMean (B π) + loss + ((2:ℝ≥0∞)^55)⁻¹ := by
    have marg : uniformMean (fun w : Targets S => B π w.1) = uniformMean (B π) := by
      rw [← avg_pair]
      simp only [avg_const]
    refine (avg_mono (point π)).trans ?_
    rw [avg_add,avg_add,marg,avg_const]
    exact add_le_add_right (target_failure S π).le _
  calc
    _ = uniformMean (fun k => uniformMean (fun π => B π (old S π k))) := avg_swap _
    _ = uniformMean (fun k => uniformMean (fun π => uniformMean (fun w => score π w k))) :=
      congrArg uniformMean (funext (exchange_mean S B))
    _ = uniformMean (fun π => uniformMean (fun w => uniformMean (score π w))) := by
      rw [avg_swap]
      exact congrArg uniformMean (funext fun π => avg_swap _)
    _ ≤ uniformMean (fun π => uniformMean (B π) + loss + ((2:ℝ≥0∞)^55)⁻¹) := avg_mono avg
    _ = _ := by rw [avg_add,avg_add,avg_const,avg_const]

end
end Reduction.ShakePermutation.SkCompare
#print axioms Reduction.ShakePermutation.SkCompare.compare
