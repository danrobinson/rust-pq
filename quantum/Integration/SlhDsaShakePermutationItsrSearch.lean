import Integration.SlhDsaShakePermutationItsrLog
import Integration.SlhDsaShakePermutationItsrNumbers
import Integration.SlhDsaShakePermutationSparseTransfer

/-! Native quantum pair search for arbitrary bounded SHAKE messages. Both
the hashing verifier and the public coherent two-way port use the same
uniform ideal permutation. -/
namespace Reduction.ShakePermutation.ItsrLabel
open Classical MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle
open scoped ComplexOrder
noncomputable section
set_option exponentiation.threshold 2048
set_option maxRecDepth 12000
set_option maxHeartbeats 1500000

theorem salt_mean (f : Permutation → ℝ≥0∞) : uniformMean f =
    uniformMean (fun π : Permutation => uniformMean (fun H : Table => f (perm π H))) := by
  rw [Classic.mean_comm]
  have law (H : Table) : uniformMean (fun π => f (perm π H)) = uniformMean f := uniform_salted _ _ _ f
  simp only [law,Classic.avg_const]

theorem uniform_price (B : ℝ≥0∞) (v : Permutation → ℝ≥0∞) (lim : ∀ π, v π ≤ 1)
    (fit : ∀ π, ¬irregular π → ¬Pairs.exceptional π → v π ≤ B) :
    uniformMean v ≤ B + ((2:ℝ≥0∞)^699)⁻¹ + ((2:ℝ≥0∞)^1000)⁻¹ := by
  let u := fun π : Permutation => if irregular π then (1:ℝ≥0∞) else 0
  let w := fun π : Permutation => if Pairs.exceptional π then (1:ℝ≥0∞) else 0
  have hb₁ : uniformMean u ≤ ((2:ℝ≥0∞)^699)⁻¹ := SparsePort.rate irregular _ (by
    simpa only [Nat.card_eq_fintype_card,Nat.mul_comm] using irregular_probability)
  have hb₂ : uniformMean w ≤ ((2:ℝ≥0∞)^1000)⁻¹ := SparsePort.rate Pairs.exceptional _ (by
    simpa only [Nat.card_eq_fintype_card,Nat.mul_comm] using Pairs.exceptional_probability)
  have point (π) : v π ≤ B + u π + w π := by
    by_cases i : irregular π
    · exact (lim π).trans (le_trans (le_add_left (by simp [u,i] : (1:ℝ≥0∞) ≤ u π)) (le_add_right le_rfl))
    by_cases e : Pairs.exceptional π
    · exact (lim π).trans (le_add_left (by simp [w,e] : (1:ℝ≥0∞) ≤ w π))
    simpa only [u,w,ite_eq_right i,ite_eq_right e,add_zero] using fit π i e
  exact (Classic.mean_mono point).trans (by
    rw [Classic.mean_add,Classic.mean_add,Classic.avg_const]
    exact add_le_add (add_le_add le_rfl hb₁) hb₂)

theorem search (S : Sha2Set) {N Q L : ℕ} (cap : Completion.blockCap N ≤ L)
    {E : Type} [Fintype E] [DecidableEq E] (M : (Port → Words) → Closed (WS Port Words E) (Pair N))
    (hm : PUE (spec := unifSpec) cnt0 M Q) (ρ : Matrix (WS Port Words E) (WS Port Words E) ℂ)
    (pos : ρ.PosSemidef) (tr : ρ.trace = 1) :
    uniformMean (fun π => qWeight (win S π) (M (oracle π)) ρ) ≤
      ENNReal.ofReal (price S (16*Q+6*L) (6*L)) + ((2:ℝ≥0∞)^699)⁻¹ + ((2:ℝ≥0∞)^1000)⁻¹ := by
  rw [salt_mean]
  apply uniform_price
  · intro π
    exact (Classic.mean_mono (fun H : Table => qWeight_le_one _ _ pos tr)).trans_eq (Classic.avg_const (U := Table) 1)
  · exact fun π hp he => fixed_search S π L hp he cap M hm ρ pos tr

theorem search_benchmark (S : Sha2Set) {N : ℕ} (cap : Completion.blockCap N ≤ 483)
    {E : Type} [Fintype E] [DecidableEq E] (M : (Port → Words) → Closed (WS Port Words E) (Pair N))
    (hm : PUE (spec := unifSpec) cnt0 M (2^41)) (ρ : Matrix (WS Port Words E) (WS Port Words E) ℂ)
    (pos : ρ.PosSemidef) (tr : ρ.trace = 1) :
    uniformMean (fun π => qWeight (win S π) (M (oracle π)) ρ) ≤ ((2:ℝ≥0∞)^81)⁻¹ := by
  have h := search S cap M hm ρ pos tr
  have price := ENNReal.ofReal_le_ofReal (price_small S
    (show 16*(2^41)+6*483 ≤ 2^46 by decide +kernel) (show 6*483 ≤ 2^12 by decide +kernel))
  apply (h.trans (add_le_add (add_le_add price le_rfl) le_rfl)).trans
  rw [ENNReal.ofReal_inv_of_pos (by positivity),ENNReal.ofReal_pow (by norm_num),ENNReal.ofReal_ofNat]
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num

end
end Reduction.ShakePermutation.ItsrLabel
#print axioms Reduction.ShakePermutation.ItsrLabel.search_benchmark
