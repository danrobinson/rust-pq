import Integration.SlhDsaShakePermutationItsrSignature
import Integration.SlhDsaShakePermutationLongSelectSignature

namespace Reduction.ShakePermutation.Long
open Classical MLink SLHDSA SLHDSA.Security OracleComp OracleSpec PQ.Interactive Quantum ENNReal SetOracle
set_option exponentiation.threshold 2048
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)

theorem arity_of_regular (g : Permutation → ℝ≥0∞) (one : ∀ π, g π ≤ 1)
    (regular : ∀ π, ¬irregular π → ¬Pairs.exceptional π →
      uniformMean (fun H : ItsrLabel.Table => g (ItsrLabel.perm π H)) ≤ ((2:ℝ≥0∞)^28)⁻¹ + ((2:ℝ≥0∞)^97)⁻¹) :
    uniformMean g ≤ ((2:ℝ≥0∞)^27)⁻¹ := by
  rw [ItsrLabel.salt_mean g]
  have h := ItsrLabel.uniform_price _ _ (fun π =>
    (Classic.mean_mono (fun H : ItsrLabel.Table => one (ItsrLabel.perm π H))).trans_eq (Classic.avg_const 1)) regular
  apply h.trans
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  norm_num

open SparsePort TweakableHash
variable (ar : ℕ)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
attribute [local irreducible] arityTargets tcrTargets Select.choice Phase.erase Select.prog
local notation "N" => ShakeApi.rawCap S 67 65536
local notation "T₀" => (fun _ : ShakeApi.Input N => (default : Bytes S.vp.params.m))
local notation "A" => Memo.selection S ar seeds F
local notation "M" => fun H st pk => Memo.machine S N rand F T₀ ar st pk H

theorem arity_of_inner (ha : ar ≤ 67)
    (inner : ∀ pk π, ¬irregular π → ¬Pairs.exceptional π →
      uniformMean (fun H : ItsrLabel.Table => tcrInner (ArityGame.adversary S ar seeds A M (ItsrLabel.perm π H)) pk)
        ≤ ((2:ℝ≥0∞)^28)⁻¹+((2:ℝ≥0∞)^97)⁻¹) :
    arityTerm S rand seeds F ar ≤ ((2:ℝ≥0∞)^27)⁻¹ := by
  unfold arityTerm
  simp_rw [Memo.cap_advantage S ar rand seeds F _ ha]
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * tcrInner (ArityGame.adversary S ar seeds A M π) pk) ≤ _
  rw [ShakeXof.mean_seed]
  have bound pk := arity_of_regular (fun π => tcrInner (ArityGame.adversary S ar seeds A M π) pk)
    (fun π => qWeight_le_one _ _ (A).posSemidef (A).trace_eq_one) (inner pk)
  calc
    _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * ((2:ℝ≥0∞)^27)⁻¹ :=
      tsum_le_tsum fun pk => mul_le_mul' le_rfl (bound pk)
    _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * _ := ENNReal.tsum_mul_right
    _ ≤ _ := (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le

/-- Concrete accounting for both long hash reductions at the native benchmark. -/
theorem compose (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk))
    (long : ∀ ar, ar ≤ 67 → arityTerm S rand seeds F ar ≤ ((2:ℝ≥0∞)^27)⁻¹) :
    let bound := ((2:ℝ≥0∞)^18)⁻¹ + ((2:ℝ≥0∞)^25)⁻¹
    strongAdvantage S rand seeds F ≤ bound ∧ advantage S rand seeds F ≤ bound := by
  have h := three_remaining_precise S rand seeds F c msg hq hs hc
  have m := signature_itsr S rand seeds F c msg hq hs hc
  have l := long S.vp.params.len (by cases S <;> decide +kernel)
  have k := long S.vp.params.k (by cases S <;> decide +kernel)
  have total := add_le_add (add_le_add (add_le_add m l) k) (le_refl (((2:ℝ≥0∞)^18)⁻¹+((2:ℝ≥0∞)^29)⁻¹))
  have price : ((2:ℝ≥0∞)^81)⁻¹+((2:ℝ≥0∞)^27)⁻¹+((2:ℝ≥0∞)^27)⁻¹+(((2:ℝ≥0∞)^18)⁻¹+((2:ℝ≥0∞)^29)⁻¹)
      ≤ ((2:ℝ≥0∞)^18)⁻¹+((2:ℝ≥0∞)^25)⁻¹ := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
    norm_num
  exact ⟨h.1.trans (total.trans price), h.2.trans (total.trans price)⟩

end Reduction.ShakePermutation.Long
#print axioms Reduction.ShakePermutation.Long.arity_of_regular
#print axioms Reduction.ShakePermutation.Long.compose
