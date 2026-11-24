import Integration.SlhDsaShakePermutationSparseDecision
import Integration.SlhDsaShakePermutationSparseFors

namespace Reduction.ShakePermutation.SparsePort.ForsDecision
open SetOracle Classical PQ.Interactive PQ.QROM Quantum ENNReal MLink SLHDSA OracleSpec OracleComp TweakableHash
noncomputable section
set_option maxRecDepth 12000
set_option exponentiation.threshold 2048
set_option maxHeartbeats 1800000
variable (S : Sha2Set) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
abbrev DBase := SM_DT_DSPR_SourceFinalValidity.Problem.standalone (Fors.Base S seeds).th (openPreTargets S.vp)
variable (A : QDsprFV_Adversary (Fors.Work (E := E)) (DBase S seeds))
variable (guess : (Port → Words) → A.State → S.Node → Closed (Fors.Work (E := E)) (ℕ × Bool))
def game (f : S.Node → Bytes 32 → S.Node → S.Node) :=
  SM_DT_DSPR_SourceFinalValidity.Problem.standalone (fvWithEval (Fors.Base S seeds) f).th (openPreTargets S.vp)
def player (H : Port → Words) (f : S.Node → Bytes 32 → S.Node → S.Node) :
    QDsprFV_Adversary (Fors.Work (E := E)) (game S seeds f) where
  State := A.State
  choose := A.choose
  guess := guess H
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one
variable (pk : S.Node)
abbrev Row := Fors.Row S
local notation "a" => Fors.address S pk
local notation "e" => SkFormat.split S
local notation "b" => ((default,default) : Row S)
variable (π : Permutation) (s : Row S → SkFormat.Suffix S)
local notation "H" => simulatedPort e a π s b
local notation "th" => fun R => Fors.eval S pk (H R) R
private theorem spe (R : Row S → S.Node) (tm : Row S) :
    SecondPreimageExists (game S seeds (th R)).th pk tm.1 tm.2 ↔ fvSPE R tm := by
  unfold SecondPreimageExists fvSPE
  change (∃ y, tm.2 ≠ y ∧ Fors.eval S pk (H R) R pk tm.1 tm.2 = Fors.eval S pk (H R) R pk tm.1 y) ↔ _
  simp only [Fors.eval,ite_true,Prod.mk.eta]
private noncomputable def winS (R : Row S → S.Node)
    (r : A.State × SM_DT_TCR_SourceFinalValidity.State (Bytes 32) S.Node) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (SecondPreimageExists (game S seeds (th R)).th
      pk tm.1 tm.2 ↔ jb.2 = true))

private noncomputable def winP (R : Row S → S.Node)
    (r : A.State × SM_DT_TCR_SourceFinalValidity.State (Bytes 32) S.Node) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (SecondPreimageExists (game S seeds (th R)).th
      pk tm.1 tm.2))

private theorem winS_eq (R : Row S → S.Node) r jb :
    winS S seeds A pk π s R r jb = pure (decide (fvDsprS r.2.challenges r.2.valid R jb)) := by
  unfold winS
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprS,h]
  | some tm =>
    simp only
    congr 1
    simp only [spe S seeds pk π s R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprS,h,hv]

private theorem winP_eq (R : Row S → S.Node) r jb :
    winP S seeds A pk π s R r jb = pure (decide (fvDsprP r.2.challenges r.2.valid R jb)) := by
  unfold winP
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprP,h]
  | some tm =>
    simp only
    congr 1
    simp only [spe S seeds pk π s R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprP,h,hv]


def gap (q : ℕ) := ENNReal.ofReal (168*((12*q : ℕ):ℝ)^2 / Fintype.card S.Node)
theorem ideal (q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun G => guess G st pk) q) :
    uniformMean (fun R => dsprFvSuccInner (player S seeds A guess (H R) (th R)) pk) ≤
      uniformMean (fun R => dsprFvSPInner (player S seeds A guess (H R) (th R)) pk) + gap S q := by
  have hcard : 2 ≤ Fintype.card S.Node := by rw [card_bytes']; cases S <;> decide
  have key := dsprFv_row_avg_le (Fors.Base S seeds) pk th (fun R t m => ite_eq_left rfl)
    A.choose (fun R st => guess (H R) st pk) A.ρ₀ (12*q)
    (fun st => row_model e a b π s _ q A.ρ₀ A.posSemidef A.trace_eq_one (hq st)) hcard le_rfl
    (winS S seeds A pk π s) (winP S seeds A pk π s) (winS_eq S seeds A pk π s) (winP_eq S seeds A pk π s)
  refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
  · refine Finset.sum_congr rfl fun R _ => congrArg (unifW _ R * ·) ?_
    unfold dsprFvSuccInner winS
    qtcr_kernel_rfl
  · refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun R _ => congrArg (unifW _ R * ·) ?_) rfl
    unfold dsprFvSPInner winP
    qtcr_kernel_rfl

def loss (q : ℕ) := gap S q + (switchLoss + switchLoss)
theorem fixed (q : ℕ) (hq : ∀ st, PUE (spec := unifSpec) cnt0 (fun G => guess G st pk) q) :
    uniformMean (fun τ => dsprFvSuccInner (player S seeds A guess (oracle τ)
      (fun p t m => (primitives (lanes τ) S.vp.params).Thash p t [m])) pk) ≤
    uniformMean (fun τ => dsprFvSPInner (player S seeds A guess (oracle τ)
      (fun p t m => (primitives (lanes τ) S.vp.params).Thash p t [m])) pk) + loss S q := by
  let P := fun G F => player S seeds A guess G (Fors.eval S pk G F)
  let W := fun G F => dsprFvSuccInner (P G F) pk
  let V := fun G F => dsprFvSPInner (P G F) pk
  have fit := (Fintype.card_le_of_embedding (Fors.singleton S)).trans (Arity.row_bits S 1 (by decide))
  have suffix : 2^1344 ≤ Fintype.card (SkFormat.Suffix S) := by rw [SkFormat.card_suffix]; cases S <;> decide +kernel
  have fwd := score_transfer e a b W fit suffix (fun _ _ => qWeight_le_one _ _ A.posSemidef A.trace_eq_one)
  have rev := score_reverse e a b V fit suffix (fun _ _ => qWeight_le_one _ _ A.posSemidef A.trace_eq_one)
  have mid : simulatedMean e a b W ≤ simulatedMean e a b V + gap S q := by
    apply avg_shift
    intro τ
    exact avg_shift _ _ _ (fun t => ideal S seeds A guess pk τ t q hq)
  have step := fwd.trans (add_le_add (mid.trans (add_le_add rev le_rfl)) le_rfl)
  let native := fun τ => player S seeds A guess (oracle τ) (fun p t m => (primitives (lanes τ) S.vp.params).Thash p t [m])
  have ss : exactMean e a W = uniformMean (fun τ => dsprFvSuccInner (native τ) pk) :=
    congrArg uniformMean (funext fun τ => congrArg (fun f => dsprFvSuccInner (player S seeds A guess (oracle τ) f) pk) (Fors.exact_eval S pk τ))
  have sp : exactMean e a V = uniformMean (fun τ => dsprFvSPInner (native τ) pk) :=
    congrArg uniformMean (funext fun τ => congrArg (fun f => dsprFvSPInner (player S seeds A guess (oracle τ) f) pk) (Fors.exact_eval S pk τ))
  rw [ss,sp] at step
  exact step.trans_eq (by unfold loss; rw [add_assoc,add_assoc,add_left_comm switchLoss (gap S q)])

theorem bound (q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun G => guess G st pk) q) :
    let native := fun τ => player S seeds A guess (oracle τ) (fun p t m => (primitives (lanes τ) S.vp.params).Thash p t [m])
    uniformMean (fun τ => qDsprFV_Success (native τ)) ≤
      uniformMean (fun τ => qDsprFV_SPProbability (native τ)) + loss S q := by
  dsimp only
  let native := fun τ => player S seeds A guess (oracle τ) (fun p t m => (primitives (lanes τ) S.vp.params).Thash p t [m])
  let u := fun τ pk => dsprFvSuccInner (native τ) pk
  let v := fun τ pk => dsprFvSPInner (native τ) pk
  simp only [qDsprFV_Success_eq_tsum,qDsprFV_SPProbability_eq_tsum]
  change uniformMean (fun τ => ∑' pk, PQ.Interactive.prob seeds (· = pk) * u τ pk) ≤
    uniformMean (fun τ => ∑' pk, PQ.Interactive.prob seeds (· = pk) * v τ pk) + loss S q
  rw [ShakeXof.mean_seed,ShakeXof.mean_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * (uniformMean (fun τ => v τ pk) + loss S q) :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (fixed S seeds A guess pk q (fun st => hq st pk))
       _ = _ + (∑' pk, PQ.Interactive.prob seeds (· = pk)) * loss S q := by
          simp only [mul_add]; rw [tsum_add,ENNReal.tsum_mul_right]
       _ ≤ _ := add_le_add le_rfl ((mul_le_mul' (tsum_prob_eq_le_one seeds) le_rfl).trans (one_mul _).le)

theorem benchmark_loss (q : ℕ) (hq : q ≤ 2^41) : loss S q ≤ ((2:ℝ≥0∞)^31)⁻¹ := by
  have d : 2^128 ≤ Fintype.card S.Node := by change _ ≤ Fintype.card (Bytes _); rw [card_bytes']; cases S <;> decide +kernel
  have hg : gap S q ≤ ENNReal.ofReal (168*(12*(2^41:ℝ))^2/2^128) := by
    apply ENNReal.ofReal_le_ofReal
    push_cast
    gcongr
    · exact_mod_cast hq
    · exact_mod_cast d
  apply (add_le_add hg (le_refl (switchLoss + switchLoss))).trans
  apply (ENNReal.toReal_le_toReal (by unfold switchLoss; finiteness) (by finiteness)).mp
  unfold switchLoss
  simp (disch := first | finiteness | positivity) only [ENNReal.toReal_add,ENNReal.toReal_ofReal,ENNReal.toReal_inv,
    ENNReal.toReal_pow,ENNReal.toReal_ofNat]
  norm_num

end
end Reduction.ShakePermutation.SparsePort.ForsDecision
#print axioms Reduction.ShakePermutation.SparsePort.ForsDecision.bound
#print axioms Reduction.ShakePermutation.SparsePort.ForsDecision.benchmark_loss
