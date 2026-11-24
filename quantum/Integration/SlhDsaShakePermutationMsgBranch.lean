import Integration.SlhDsaShakePermutationMsgRounds
import Integration.SlhDsaShakePermutationMsgPostMass

namespace Reduction.ShakePermutation.MsgTrajectory
open MLink SLHDSA SetOracle ENNReal Classical Quantum PQ.Interactive OracleComp
open scoped ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
attribute [local instance] singletonFintype
variable (S : Sha2Set) (π : Permutation) (d : S.Node × List SLHDSA.Byte)
variable {E : Type} [Fintype E] [DecidableEq E]
local notation "Work" => WS Port Words E
private theorem amono {B : Type} [Fintype B] {f g : B → ℝ≥0∞} (h : ∀ b, f b ≤ g b) :
    uniformMean f ≤ uniformMean g := Finset.sum_le_sum fun b _ => mul_le_mul' le_rfl (h b)
private theorem aconst {B : Type} [Fintype B] [Nonempty B] (c : ℝ≥0∞) :
    uniformMean (fun _ : B => c) = c := by simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
private theorem aplus {B : Type} [Fintype B] (f g : B → ℝ≥0∞) :
    uniformMean (fun b => f b+g b) = uniformMean f+uniformMean g := by simp only [uniformMean,mul_add,Finset.sum_add_distrib]
private theorem aright {B : Type} [Fintype B] (f : B → ℝ≥0∞) (c : ℝ≥0∞) :
    uniformMean (fun b => f b*c) = uniformMean f*c := by simp only [uniformMean,Finset.sum_mul,mul_assoc]
private theorem aswap {B C : Type} [Fintype B] [Fintype C] (f : B → C → ℝ≥0∞) :
    uniformMean (fun b => uniformMean (f b)) = uniformMean (fun c => uniformMean (fun b => f b c)) := by
  simp only [uniformMean,Finset.mul_sum]; rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_left_comm ..

set_option allowUnsafeReducibility true in
attribute [local irreducible] programmed oracle suffix

theorem challenge_branch (good : ¬Risk.exceptional π) (cap : d.2.length ≤ 65536)
    (M : S.Node → (Port → Words) → Closed Work Bool) (cost : ∀ r, PUE (spec:=unifSpec) cnt0 (M r) (2^41))
    (A : Matrix Work Work ℂ) (pos : A.PosSemidef) :
    uniformMean (fun σ : Permutation => uniformMean (fun k : S.Node =>
      let δ := programmed S k π σ
      qWeight (· = true) (M (MsgCost.roundValue S δ δ k d) (oracle δ)) A)) ≤
      uniformMean (fun r : S.Node => qWeight (· = true) (M r (oracle π)) A) +
        (((2:ℝ≥0∞)^116)⁻¹+((2:ℝ≥0∞)^41)⁻¹)*ENNReal.ofReal A.trace.re := by
  classical
  let t := ENNReal.ofReal A.trace.re
  let V (r : S.Node) (δ : Permutation) := qWeight (· = true) (M r (oracle δ)) A
  let bs := laterBlocks S d.1 d.2
  let x (k : S.Node) := join (firstBlock S k d.1 d.2) 0
  let val (s : Words) := (SkFormat.split S (suffix π bs s)).1
  let raw (k : S.Node) (σ : Permutation) := programmed S k π σ
  let real (k : S.Node) (σ : Permutation) := (primitives (lanes (raw k σ)) S.vp.params).PRFmsg k d.1 d.2
  have eq (k σ) : real k σ = MsgCost.roundValue S (raw k σ) (raw k σ) k d :=
    byte_prf S (raw k σ) k d.1 d.2 _ _ (split_blocks S k d.1 d.2)
  have per (k σ) : V (real k σ) (raw k σ) ≤ V (val (σ (x k))) (raw k σ) +
      (if real k σ ≠ val (σ (x k)) then (1:ℝ≥0∞) else 0)*t := by
    by_cases same : real k σ = val (σ (x k))
    · simp [same]
    · rw [ite_eq_left same,one_mul]
      exact (qWeight_le_trace _ _ pos).trans le_add_self
  have honest (k) :
      uniformMean (fun σ => V (real k σ) (raw k σ)) ≤ uniformMean (fun σ => V (val (σ (x k))) (raw k σ)) +
        ((2:ℝ≥0∞)^116)⁻¹*t := by
    apply (amono (per k)).trans
    rw [aplus,aright]
    exact add_le_add le_rfl (mul_le_mul' (honest_gap S π good k d.1 d.2 cap) le_rfl)
  let action (k : S.Node) (r : S.Node) := uniformMean (fun tail : SkFormat.Suffix S =>
    uniformMean (fun σ : OracleComp.PermutationConditioning.Extensions [(x k,firstState S π bs r tail)] =>
      V r (raw k σ.val)))
  have changeLaw (k) : uniformMean (fun σ => V (val (σ (x k))) (raw k σ)) = uniformMean (action k) :=
    conditioned_output S π bs (x k) (fun r σ => V r (raw k σ))
  have post (r : S.Node) : uniformMean (fun k => action k r) ≤ V r π + ((2:ℝ≥0∞)^41)⁻¹*t := by
    rw [mul_comm _ t]
    exact post_mass S π bs r x (M r) (cost r) A pos
  rw [aswap]
  change uniformMean (fun k => uniformMean (fun σ => V (MsgCost.roundValue S (raw k σ) (raw k σ) k d) (raw k σ))) ≤ _
  simp_rw [← eq]
  apply (amono honest).trans
  simp_rw [changeLaw]
  rw [aplus,aconst,aswap]
  apply (add_le_add (amono post) le_rfl).trans
  rw [aplus,aconst,add_mul]
  exact (show ∀ a b c : ℝ≥0∞, (a+b)+c ≤ a+(c+b) from fun a b c => by rw [add_assoc,add_comm b c]) _ _ _

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.challenge_branch
