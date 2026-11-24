import Integration.SlhDsaShakePermutationPosteriorGame

namespace Reduction.ShakePermutation.MsgTrajectory
open Classical MLink SLHDSA SetOracle ENNReal OracleComp OracleComp.PermutationConditioning Classic Quantum PQ.Interactive
open scoped Kronecker ComplexOrder
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
set_option exponentiation.threshold 2048
attribute [local instance] singletonFintype
abbrev Fixed := Extensions ([(0,0)] : EdgeTrace Words)
local instance : Nonempty Fixed := ⟨Equiv.refl _,by simp⟩

private def move (x s : Words) (σ : Permutation) :=
  ((Equiv.swap (0 : Words) x).trans σ).trans (Equiv.swap (0 : Words) s)

private theorem move_self (x s : Words) (σ : Permutation) : move x s (move x s σ) = σ := by
  ext w
  simp [move]

def frame (x s : Words) : Fixed ≃ Extensions [(x,s)] where
  toFun σ := ⟨move x s σ.val,by
    rintro e h
    obtain rfl : e = (x,s) := by simpa using h
    simp only [move,Equiv.trans_apply,Equiv.swap_apply_right,show σ.val 0 = 0 from σ.property (0,0) (by simp),Equiv.swap_apply_left]⟩
  invFun τ := ⟨move x s τ.val,by
    rintro e h
    obtain rfl : e = (0,0) := by simpa using h
    simp only [move,Equiv.trans_apply,Equiv.swap_apply_left,show τ.val x = s from τ.property (x,s) (by simp),Equiv.swap_apply_right]⟩
  left_inv σ := Subtype.ext (move_self _ _ _)
  right_inv τ := Subtype.ext (move_self _ _ _)

variable (S : Sha2Set) (π : Permutation) (bs : List Rate) (r : S.Node) (x : S.Node → Words)
abbrev Sample := S.Node × (SkFormat.Suffix S × Fixed)

def draw (v : Sample S) : Permutation := (frame (x v.1) (firstState S π bs r v.2.1) v.2.2).val

theorem sample_mean (f : S.Node → Permutation → ℝ≥0∞) :
    uniformMean (fun v : Sample S => f v.1 (draw S π bs r x v)) = posterior S π bs r x f := by
  rw [Classic.mean_prod]
  apply congrArg uniformMean; funext k
  rw [Classic.mean_prod]
  apply congrArg uniformMean; funext t
  exact mean_equiv (frame (x k) (firstState S π bs r t)) (fun τ => f k τ.val)

private theorem numeric (a b c : ℕ) (pa : 0 < a) (pb : 0 < b) (pc : 0 < c)
    (h : 1/(a:ℝ) + (1/(b:ℝ)+(b:ℝ)*(1/(c:ℝ))) ≤ ((2:ℝ)^126)⁻¹) :
    1/(a:ℝ≥0∞) + (1/(b:ℝ≥0∞)+(b:ℝ≥0∞)*(1/(c:ℝ≥0∞))) ≤ ((2:ℝ≥0∞)^126)⁻¹ := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simpa (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_one,ENNReal.toReal_natCast,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using h

private theorem exposure_small : exposure S ≤ ((2:ℝ≥0∞)^126)⁻¹ := by
  have w : Fintype.card Words = 2^1600 := by
    change Fintype.card (Fin 25 → UInt64) = _
    rw [Fintype.card_fun,Fintype.card_fin,← FinEnum.card_eq_fintypeCard,FinEnum.card_UInt64]
    decide +kernel
  have n : Fintype.card S.Node = 2^(8*S.vp.params.n) := by
    change Fintype.card (Bytes _) = _
    rw [card_bytes',pow_mul]; rfl
  have bits : 8*S.vp.params.n = 128 ∨ 8*S.vp.params.n = 192 ∨ 8*S.vp.params.n = 256 := by cases S <;> decide
  unfold exposure; rw [w,n,SkFormat.card_suffix]
  rcases bits with h|h|h <;> rw [h] <;>
    apply numeric <;> norm_num

set_option allowUnsafeReducibility true in
attribute [local irreducible] programmed hit draw posterior oracle


variable {E : Type} [Fintype E] [DecidableEq E]
/-- Postchallenge quantum test. The message, revealed digest and the entire
public reference permutation are fixed. Both directions and an arbitrary
quantum workspace are allowed. -/
theorem post_game (M : (Port → Words) → Closed (WS Port Words E) Bool)
    (q : ℕ) (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((Port × Words) × E)) :
    let test := fun δ => qWeight (· = true) (M (oracle δ)) (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    posterior S π bs r x (fun k σ => test (programmed S k π σ)) ≤ test π +
      ENNReal.ofReal (8*(q:ℝ)^2*((2:ℝ)^126)⁻¹) := by
  classical
  dsimp only
  rw [← sample_mean S π bs r x]
  let δ (v : Sample S) := draw S π bs r x v
  let bad (v : Sample S) (p : Port) := hit S π (δ v) v.1 p
  have risk (p : Port) : uniformMean (fun v => if bad v p then (1:ℝ≥0∞) else 0) ≤ ((2:ℝ≥0∞)^126)⁻¹ := by
    exact (sample_mean S π bs r x (fun k σ => if hit S π σ k p then (1:ℝ≥0∞) else 0)).le.trans
      ((exposure_bound S π bs r x p).trans (exposure_small S))
  have h := Program.average_game (oracle π) (fun v => oracle (programmed S v.1 π (δ v))) bad _ (by finiteness)
    risk (fun v p => outside_hit S π (δ v) v.1 p) M q hq ρ
  simpa only [ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat] using h

end
end Reduction.ShakePermutation.MsgTrajectory
#print axioms Reduction.ShakePermutation.MsgTrajectory.post_game
