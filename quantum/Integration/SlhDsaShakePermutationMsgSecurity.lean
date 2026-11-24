import Integration.SlhDsaShakePermutationMsgNativeSwitch
import Integration.SlhDsaShakePermutationMsgBranch

namespace Reduction.ShakePermutation.MsgCost
open Classical MLink SLHDSA SLHDSA.Security Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle QMsg ShakeApi MsgSplit MsgTrajectory
open scoped ComplexOrder
noncomputable section
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
set_option allowUnsafeReducibility true in
attribute [local irreducible] programmed oracle
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1800000
variable (S : Sha2Set) (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)
    {E : Type} [Fintype E] [DecidableEq E] (F : PortForger Port Words E)
local notation "N" => rawCap S 67 65536
local notation "Work" => WS Port Words E
local notation "D" => S.Node × List SLHDSA.Byte
local notation "Stages" => FamilyStage Port Words E D S.Node Bool (2^41)
local notation "P" => native S N rand seeds F
local notation "P₀" => fun π : Permutation => ShakeApi.primitives S (extend (SkCost.table S N (oracle π)))
private def ε : ℝ≥0∞ := ((2:ℝ≥0∞)^116)⁻¹+((2:ℝ≥0∞)^41)⁻¹

private theorem avg_const {B : Type} [Fintype B] [Nonempty B] (c : ℝ≥0∞) :
    uniformMean (fun _ : B => c) = c := by simp only [uniformMean,← Finset.sum_mul,sum_unifW,one_mul]
private theorem avg_add {B : Type} [Fintype B] (g h : B → ℝ≥0∞) :
    uniformMean (fun i => g i + h i) = uniformMean g + uniformMean h := by
  simp only [uniformMean,mul_add,Finset.sum_add_distrib]
private theorem avg_mono {B : Type} [Fintype B] {g h : B → ℝ≥0∞} (step : ∀ i, g i ≤ h i) :
    uniformMean g ≤ uniformMean h := Finset.sum_le_sum fun i _ => mul_le_mul' le_rfl (step i)

private theorem branch (π : Permutation) (good : ¬Risk.exceptional π)
    (s : Stages) (valid : validStage S 65536 s) (M : Matrix Work Work ℂ) (pos : M.PosSemidef) :
    uniformMean (fun σ => uniformMean (fun k => qWeight (· = true) (real_post S (programmed S k π σ) k s) M)) ≤
      qWeight (· = true) (ideal_post S (oracle π) s) M + ε*ENNReal.ofReal M.trace.re := by
  rcases s with b | ⟨d,post⟩
  · change uniformMean (fun _ : Permutation => uniformMean (fun _ : S.Node => qWeight (· = true) (pure b : Closed Work Bool) M)) ≤ _
    rw [avg_const,avg_const]; exact le_self_add
  · let val (π : Permutation) (k : S.Node) := (primitives (lanes π) S.vp.params).PRFmsg k d.1 d.2
    have eq (π k) : val π k = roundValue S π π k d := byte_prf S π k d.1 d.2 _ _ (split_blocks S k d.1 d.2)
    change uniformMean (fun σ : Permutation => uniformMean (fun k : S.Node =>
      qWeight (· = true) (post.val (val (programmed S k π σ) k) (oracle (programmed S k π σ))) M)) ≤
        qWeight (· = true) (liftU ($ᵗ S.Node) >>= fun r => post.val r (oracle π)) M + _
    simp only [eq,qWeight_liftU_uniform_bind]
    simpa only [uniformMean,unifW,Finset.mul_sum,ε] using challenge_branch S π d good valid post.val post.property M pos

private theorem good_game (pre : Closed Work Stages) (valid : AllQueries (fun _ => True) (validStage S 65536) pre)
    (π : Permutation) (good : ¬Risk.exceptional π) (M : Matrix Work Work ℂ) (pos : M.PosSemidef) :
    uniformMean (fun σ => uniformMean (fun k => qWeight (· = true) (pre >>= real_post S (programmed S k π σ) k) M)) ≤
      qWeight (· = true) (pre >>= ideal_post S (oracle π)) M + ε*ENNReal.ofReal M.trace.re := by
  have step (s) (v : validStage S (E:=E) 65536 s) (A : Matrix Work Work ℂ) (h : A.PosSemidef) := branch S π good s v A h
  have h := MsgEffect.under_two_draws pre _ valid
    (fun σ k => real_post S (programmed S k π σ) k)
    (fun (_ : Unit) (_ : Unit) => ideal_post S (oracle π)) ε
    (fun s v A h => by simpa only [avg_const] using step s v A h) M pos
  simpa only [avg_const] using h

/-- Pseudorandomness of the message randomizer in the actual one-signature
SUF reduction with a shared, coherently accessible two-way permutation. -/
def messageFee (S : Sha2Set) : ℝ≥0∞ := ((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ + ((2:ℝ≥0∞)^40)⁻¹

theorem messageFee_le (S : Sha2Set) : messageFee S ≤ ((2:ℝ≥0∞)^18)⁻¹ := by
  unfold messageFee
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  have size : S.vp.params.n = 16 ∨ S.vp.params.n = 24 ∨ S.vp.params.n = 32 := by cases S <;> decide
  rcases size with h|h|h <;> norm_num [MsgEffect.prefixBits,h]

theorem signature_component_width (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun π => qPrfRealPr (msgPrf S.vp ((P₀) π)) (P (oracle π)) F.ρ₀) ≤
      uniformMean (fun π => qPrfIdealPr (P (oracle π)) F.ρ₀) + messageFee S := by
  classical
  obtain ⟨pre,limit,valid,exactCut⟩ := signature_cut S N rand seeds F c hc le_rfl hq hs
  rw [msg] at valid
  have start := native_real_prefix S rand seeds F pre limit exactCut valid hs F.ρ₀ F.posSemidef (by simp [F.trace_eq_one])
  let real (π : Permutation) := uniformMean (fun σ => uniformMean (fun k =>
    qWeight (· = true) (pre (oracle π) >>= real_post S (programmed S k π σ) k) F.ρ₀))
  let ideal (π : Permutation) := qPrfIdealPr (P (oracle π)) F.ρ₀
  let bad (π : Permutation) : ℝ≥0∞ := if Risk.exceptional π then 1 else 0
  have per (π) : real π ≤ (ideal π+ε)+bad π := by
    by_cases e : Risk.exceptional π
    · have h : real π ≤ 1 := ShakeXof.mean_le_const fun σ => ShakeXof.mean_le_const fun k =>
        qWeight_le_one _ _ F.posSemidef F.trace_eq_one
      exact h.trans ((le_add_self : (1:ℝ≥0∞) ≤ (ideal π+ε)+1).trans_eq (by simp [bad,e]))
    · have h := good_game S (pre (oracle π)) (valid _) π e F.ρ₀ F.posSemidef
      rw [← native_ideal_prefix S rand seeds F pre exactCut hs π] at h
      simpa only [real,ideal,bad,ite_eq_right e,add_zero,F.trace_eq_one,Complex.one_re,ENNReal.ofReal_one,mul_one] using h
  have avg := avg_mono per
  rw [avg_add,avg_add,avg_const] at avg
  have num : (ε+((2:ℝ≥0∞)^512)⁻¹)+((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ ≤ messageFee S := by
    apply (ENNReal.toReal_le_toReal (by unfold ε; finiteness) (by unfold messageFee; finiteness)).mp
    unfold ε messageFee
    simp (disch := finiteness) only [ENNReal.toReal_add,ENNReal.toReal_inv,ENNReal.toReal_pow,ENNReal.toReal_ofNat]
    linarith [show ((2:ℝ)^116)⁻¹+((2:ℝ)^41)⁻¹+((2:ℝ)^512)⁻¹ ≤ ((2:ℝ)^40)⁻¹ by norm_num]
  apply start.trans
  have exc : uniformMean bad ≤ ((2:ℝ≥0∞)^512)⁻¹ := Risk.exceptional_risk
  change uniformMean real + _ ≤ uniformMean ideal + _
  calc
    _ ≤ ((uniformMean ideal+ε)+((2:ℝ≥0∞)^512)⁻¹)+((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹ := add_le_add (avg.trans (add_le_add le_rfl exc)) le_rfl
    _ = uniformMean ideal + ((ε+((2:ℝ≥0∞)^512)⁻¹)+((2:ℝ≥0∞)^(MsgEffect.prefixBits S))⁻¹) := by simp only [add_assoc]
    _ ≤ _ := add_le_add le_rfl num

theorem signature_component (c : Caps) (msg : c.ml = 65536)
    (hq : ∀ pk, CountBound isPort (F.main pk) (2^40)) (hs : ∀ pk, CountBound isSign (F.main pk) 1)
    (hc : ∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) :
    uniformMean (fun π => qPrfRealPr (msgPrf S.vp ((P₀) π)) (P (oracle π)) F.ρ₀) ≤
      uniformMean (fun π => qPrfIdealPr (P (oracle π)) F.ρ₀) + ((2:ℝ≥0∞)^18)⁻¹ := by
  apply (signature_component_width S rand seeds F c msg hq hs hc).trans
  apply add_le_add le_rfl
  exact messageFee_le S

end
end Reduction.ShakePermutation.MsgCost
#print axioms Reduction.ShakePermutation.MsgCost.signature_component
