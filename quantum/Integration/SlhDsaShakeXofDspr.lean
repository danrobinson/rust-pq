import Integration.SlhDsaShakeXofFors
import Integration.SlhDsaSetForsMach

set_option maxRecDepth 8192
namespace Reduction.ShakeXof
open MLink Ideal SLHDSA OracleComp OracleSpec PQ.Interactive PQ.QROM Quantum ENNReal TweakableHash
variable (S : Sha2Set) {N : ℕ} (cap : FitsSingleton S (N := N))

def dsprProblem (g : ShakeApi.RawTable S N) (seeds : ProbComp S.Node) :
    SM_DT_DSPR_SourceFinalValidity.Problem Empty S.Node (Bytes 32) S.Node S.Node :=
  .standalone (forsProblem S g seeds).th (openPreTargets S.vp)

theorem dsprProblem_eq (g : ShakeApi.RawTable S N) (seeds : ProbComp S.Node) :
    dsprProblem S g seeds = forsDsprProblem S.vp (ShakeApi.primitives S (ShakeApi.extend g)) seeds := rfl

variable {W : Type} [Fintype W] (seeds : ProbComp S.Node)
  (A : QDsprFV_Adversary W (SM_DT_DSPR_SourceFinalValidity.Problem.standalone
    (baseProblem S seeds).th (openPreTargets S.vp)))
  (guess : ShakeApi.RawTable S N → A.State → S.Node → Closed W (ℕ × Bool))

def dsprAdversary (g : ShakeApi.RawTable S N) : QDsprFV_Adversary W (dsprProblem S g seeds) where
  State := A.State
  choose := A.choose
  guess := guess g
  ρ₀ := A.ρ₀
  posSemidef := A.posSemidef
  trace_eq_one := A.trace_eq_one

private theorem eval_replaced (g : ShakeApi.RawTable S N) (pk : S.Node) (R : SingletonRow S) (t : Bytes 32) (m : S.Node) :
    (forsProblem S (replaceSingleton S cap pk g R) seeds).th.eval pk t m = R (t,m) :=
  replacedF S cap g pk R t m

private theorem spe (g : ShakeApi.RawTable S N) (pk : S.Node) (R : SingletonRow S) (tm : Bytes 32 × S.Node) :
    SecondPreimageExists (dsprProblem S (replaceSingleton S cap pk g R) seeds).th pk tm.1 tm.2 ↔ fvSPE R tm := by
  unfold SecondPreimageExists fvSPE
  change (∃ y, tm.2 ≠ y ∧ (forsProblem S (replaceSingleton S cap pk g R) seeds).th.eval pk tm.1 tm.2 =
    (forsProblem S (replaceSingleton S cap pk g R) seeds).th.eval pk tm.1 y) ↔ _
  simp only [eval_replaced]

private noncomputable def winS (g : ShakeApi.RawTable S N) (pk : S.Node) (R : SingletonRow S)
    (r : A.State × SM_DT_TCR_SourceFinalValidity.State (Bytes 32) S.Node) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (SecondPreimageExists (dsprProblem S (replaceSingleton S cap pk g R) seeds).th
      pk tm.1 tm.2 ↔ jb.2 = true))

private noncomputable def winP (g : ShakeApi.RawTable S N) (pk : S.Node) (R : SingletonRow S)
    (r : A.State × SM_DT_TCR_SourceFinalValidity.State (Bytes 32) S.Node) (jb : ℕ × Bool) : ProbComp Bool :=
  match r.2.challenges[jb.1]? with
  | none => pure false
  | some tm => pure (r.2.valid && decide (SecondPreimageExists (dsprProblem S (replaceSingleton S cap pk g R) seeds).th
      pk tm.1 tm.2))

open Classical in
private theorem winS_eq (g : ShakeApi.RawTable S N) (pk : S.Node) (R : SingletonRow S) r jb :
    winS S cap seeds A g pk R r jb = pure (decide (fvDsprS r.2.challenges r.2.valid R jb)) := by
  unfold winS
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprS,h]
  | some tm =>
    simp only
    congr 1
    simp only [spe S cap seeds g pk R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprS,h,hv]

open Classical in
private theorem winP_eq (g : ShakeApi.RawTable S N) (pk : S.Node) (R : SingletonRow S) r jb :
    winP S cap seeds A g pk R r jb = pure (decide (fvDsprP r.2.challenges r.2.valid R jb)) := by
  unfold winP
  cases h : r.2.challenges[jb.1]? with
  | none => simp [fvDsprP,h]
  | some tm =>
    simp only
    congr 1
    simp only [spe S cap seeds g pk R tm]
    by_cases hv : r.2.valid = true <;> simp [fvDsprP,h,hv]

include cap in
theorem dspr_fixed (pk : S.Node) (q : ℕ)
    (model : ∀ s : A.State, ∃ Mo : HybridModel (ShakeApi.Input N) (Bytes S.vp.params.m) (ℕ × Bool) q,
      Mo.Additive ∧ Rows.RowsBound (fun H E => (Mo.prob H E).toReal) q ∧
      ∀ g : ShakeApi.RawTable S N, ∀ Ev : ℕ × Bool → Prop, ∀ [DecidablePred Ev],
        Mo.prob g Ev = qWeight Ev (guess g s pk) A.ρ₀) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * dsprFvSuccInner (dsprAdversary S seeds A guess g) pk) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * dsprFvSPInner (dsprAdversary S seeds A guess g) pk) +
      ENNReal.ofReal (168*(q:ℝ)^2 / Fintype.card S.Node) := by
  let eps := ENNReal.ofReal (168*(q:ℝ)^2 / Fintype.card S.Node)
  have step (g : ShakeApi.RawTable S N) :
      (∑ R : SingletonRow S, unifW _ R * dsprFvSuccInner (dsprAdversary S seeds A guess (replaceSingleton S cap pk g R)) pk) ≤
      (∑ R : SingletonRow S, unifW _ R * dsprFvSPInner (dsprAdversary S seeds A guess (replaceSingleton S cap pk g R)) pk) + eps := by
    have hm (s : A.State) : ∃ Mo : HybridModel (Bytes 32 × S.Node) S.Node (ℕ × Bool) q,
        Mo.Additive ∧ Rows.RowsBound (fun H E => (Mo.prob H E).toReal) q ∧
        ∀ R (Ev : ℕ × Bool → Prop) [DecidablePred Ev], Mo.prob R Ev =
          qWeight Ev (guess (replaceSingleton S cap pk g R) s pk) A.ρ₀ := by
      obtain ⟨M,ha,hr,hM⟩ := model s
      refine ⟨M.pullback (singletonEmbedding S cap pk) (fun R => (replaceSingleton S cap pk g R)) (different_at (singletonEmbedding S cap pk) g),
        ha.pullback _ _ _, RowsBound.pullback (singletonEmbedding S cap pk) (fun R => (replaceSingleton S cap pk g R)) (different_at (singletonEmbedding S cap pk) g) (fun H E => (M.prob H E).toReal) hr, ?_⟩
      intro R Ev _
      rw [HybridModel.pullback_prob,hM]
    have hcard : 2 ≤ Fintype.card S.Node := by rw [card_bytes']; cases S <;> decide
    have key := dsprFv_row_avg_le (forsProblem S g seeds) pk (fun R => (forsProblem S (replaceSingleton S cap pk g R) seeds).th.eval)
      (eval_replaced S cap seeds g pk) A.choose (fun R s => guess (replaceSingleton S cap pk g R) s pk)
      A.ρ₀ q hm hcard le_rfl (winS S cap seeds A g pk) (winP S cap seeds A g pk) (winS_eq S cap seeds A g pk) (winP_eq S cap seeds A g pk)
    refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
    · refine Finset.sum_congr rfl fun R _ => congrArg (unifW _ R * ·) ?_
      unfold dsprFvSuccInner winS
      qtcr_kernel_rfl
    · refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun R _ => congrArg (unifW _ R * ·) ?_) rfl
      unfold dsprFvSPInner winP
      qtcr_kernel_rfl
  rw [average_singleton S cap pk (fun g => dsprFvSuccInner (dsprAdversary S seeds A guess g) pk),
      average_singleton S cap pk (fun g => dsprFvSPInner (dsprAdversary S seeds A guess g) pk)]
  calc _ ≤ ∑ g : ShakeApi.RawTable S N, unifW _ g * (_ + eps) := Finset.sum_le_sum fun g _ => mul_le_mul' le_rfl (step g)
       _ = _ := by simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_unifW, one_mul]; rfl

include cap in
/-- Both the success and baseline probabilities use the same shared tables. -/
theorem dspr_bound (q : ℕ)
    (model : ∀ (pk : S.Node) (s : A.State), ∃ Mo : HybridModel (ShakeApi.Input N) (Bytes S.vp.params.m) (ℕ × Bool) q,
      Mo.Additive ∧ Rows.RowsBound (fun H E => (Mo.prob H E).toReal) q ∧
      ∀ g : ShakeApi.RawTable S N, ∀ Ev : ℕ × Bool → Prop, ∀ [DecidablePred Ev],
        Mo.prob g Ev = qWeight Ev (guess g s pk) A.ρ₀) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qDsprFV_Success (dsprAdversary S seeds A guess g)) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qDsprFV_SPProbability (dsprAdversary S seeds A guess g)) +
      ENNReal.ofReal (168*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  let eps := ENNReal.ofReal (168*(q:ℝ)^2 / Fintype.card S.Node)
  have num : eps = ENNReal.ofReal (168*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
    dsimp only [eps]; rw [card_bytes',pow_mul]; norm_num
  let a := fun g pk => dsprFvSuccInner (dsprAdversary S seeds A guess g) pk
  let b := fun g pk => dsprFvSPInner (dsprAdversary S seeds A guess g) pk
  simp only [qDsprFV_Success_eq_tsum, qDsprFV_SPProbability_eq_tsum]
  rw [← num]
  change (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * a g pk) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * b g pk) + eps
  have swap (f : ShakeApi.RawTable S N → S.Node → ℝ≥0∞) :
      (∑ g : ShakeApi.RawTable S N, unifW _ g * ∑' pk, PQ.Interactive.prob seeds (· = pk) * f g pk) =
      ∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : ShakeApi.RawTable S N, unifW _ g * f g pk := by
    simp only [tsum_fintype, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [swap a, swap b]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * ((∑ g : ShakeApi.RawTable S N, unifW _ g * b g pk) + eps) :=
          tsum_le_tsum fun pk => mul_le_mul' le_rfl (dspr_fixed S cap seeds A guess pk q (model pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk) * ∑ g : ShakeApi.RawTable S N, unifW _ g * b g pk) + (∑' pk, PQ.Interactive.prob seeds (· = pk)) * eps := by simp only [mul_add]; rw [tsum_add, ENNReal.tsum_mul_right]
       _ ≤ _ := add_le_add le_rfl ((mul_le_mul' (tsum_prob_eq_le_one seeds) le_rfl).trans (one_mul eps).le)

include cap in
theorem fors_dspr_port {E : Type} [Fintype E] [DecidableEq E]
    (adv : QDsprFV_Adversary (Work S N E) (SM_DT_DSPR_SourceFinalValidity.Problem.standalone
      (baseProblem S seeds).th (openPreTargets S.vp)))
    (machine : ShakeApi.RawTable S N → adv.State → S.Node → Closed (Work S N E) (ℕ × Bool))
    (q : ℕ) (hq : ∀ st pk, PUE (spec := unifSpec) cnt0 (fun H => machine H st pk) q) :
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qDsprFV_Success (dsprAdversary S seeds adv machine g)) ≤
    (∑ g : ShakeApi.RawTable S N, unifW _ g * qDsprFV_SPProbability (dsprAdversary S seeds adv machine g)) +
      ENNReal.ofReal (168*(q:ℝ)^2 / 2^(8*S.vp.params.n)) := by
  classical
  apply dspr_bound S cap seeds adv machine q
  intro pk st
  obtain ⟨ρ,hρ⟩ := exists_subState (A := (ShakeApi.Input N × Bytes S.vp.params.m) × E) adv.ρ₀ adv.posSemidef adv.trace_eq_one
  obtain ⟨x,hx,hxe⟩ := (hq st pk).exists_prog_qprob
  refine ⟨HybridModel.ofProgram LocalSig.Interp.instruments x ρ q hx Sigma.snd,
    HybridModel.ofProgram_additive _ x ρ _ hx Sigma.snd, Rows.ofProgram_rowsBound _ x ρ _ hx Sigma.snd, ?_⟩
  intro g Ev _
  exact (hxe Ev g ρ).trans (by rw [hρ])
end Reduction.ShakeXof

#print axioms Reduction.ShakeXof.dsprProblem_eq
#print axioms Reduction.ShakeXof.fors_dspr_port
