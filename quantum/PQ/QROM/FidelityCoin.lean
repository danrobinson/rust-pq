import PQ.QROM.Fidelity

/-!
# Fidelity of the exact SM-DT-TCR game: classical adversaries with a uniform coin

Extension of `PQ/QROM/Fidelity.lean` to randomised classical adversaries whose private
randomness is a uniform element `ω` of a finite type `Ω`, drawn at the start of the first phase.

* `FidCoinAdv Ω Sd Tw Msg Y`: `choose : Ω → OracleComp (hash + (challenge + collection)) State`,
  `forge : State → Sd → OracleComp hash (ℕ × Msg)` (`choose ω` may put `ω` into the state).
* `FidCoinAdv.honest cap A Th : SM_DT_TCR_Adversary (fidProblem cap Th)`: VCVio's adversary
  whose `choose` samples `ω ← $ᵗ Ω` with its private uniform randomness (`unifSpec`) and then
  runs `A.choose ω` with hash queries answered by `Th`.
* `fidCoinEmb n A.choose`: the embedding into the exact game: a uniform coin (the local
  instrument `SubInstrument.uniform Ω`), then the embedding `fidEmb` of `A.choose ω`.

`fid_coin_tcrExp_eq`: `tcrExp (embedding) = avg_Th SM_DT_TCR_Advantage (A.honest cap Th)`.
`fid_coin_tcr_classical_le`: the bound of `tcr_exact_le` for VCVio's advantage of such
adversaries, averaged over the random hash.

Not covered: coins sampled adaptively during the first phase with an unbounded total number of
coins, and coins of `forge`.
-/

open OracleComp OracleSpec TweakableHash ENNReal Quantum Matrix
open scoped Kronecker ComplexOrder

set_option linter.unusedSectionVars false

namespace PQ.QROM

variable {Y : Type} [Fintype Y] [DecidableEq Y] [AddCommGroup Y]
  {Sd Tw Msg Ω : Type} [Fintype Sd] [DecidableEq Sd] [Fintype Tw] [DecidableEq Tw] [Fintype Msg]
  [DecidableEq Msg] [SampleableType Sd] [Fintype Ω] [Nonempty Ω] [SampleableType Ω]

/-- A classical two-phase adversary with a uniform coin `ω : Ω` drawn at the start. -/
structure FidCoinAdv (Ω Sd Tw Msg Y : Type) where
  /-- Private state carried from `choose` to `forge`. -/
  State : Type
  /-- The first phase, for the coin `ω`. -/
  choose : Ω → OracleComp (fidSpec Sd Tw Msg Y) State
  /-- The second phase. -/
  forge : State → Sd → OracleComp (fidHashSpec Sd Tw Msg Y) (ℕ × Msg)

/-- The deterministic adversary for the coin `ω`. -/
def FidCoinAdv.at (A : FidCoinAdv Ω Sd Tw Msg Y) (ω : Ω) : FidAdv Sd Tw Msg Y :=
  ⟨A.State, A.choose ω, A.forge⟩

/-- VCVio's adversary: sample the coin with the private uniform randomness, then run the
classical adversary with hash queries answered by `Th`. -/
noncomputable def FidCoinAdv.honest (cap : ℕ) (A : FidCoinAdv Ω Sd Tw Msg Y)
    (Th : Dom Sd Tw Msg → Y) : SM_DT_TCR_Adversary (fidProblem cap Th) where
  State := A.State
  choose := do
    let ω ← (liftM ($ᵗ Ω : ProbComp Ω) : OracleComp (unifSpec +
      (SM_DT_TCR_challengeSpec Tw Msg Y + collectionSpec (fidProblem cap Th).thColl)) Ω)
    simulateQ (fidInst cap Th) (A.choose ω)
  forge st P := simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.forge st P)

/-- The embedding: a uniform coin, then the embedding of `choose ω`. -/
noncomputable def fidCoinEmb {State : Type} (choose : Ω → OracleComp (fidSpec Sd Tw Msg Y) State) :
    (n : ℕ) → FidIAdv Sd Tw Msg Y State n (QReg.of Unit)
  | 0 => fidBind (W := FidOut State) (QComp.act (SubInstrument.uniform Ω (QReg.of Unit)))
      fun ω ↦ fidEmb 0 (choose ω)
  | n + 1 => fidBind (W := FidLeaf Sd Tw Msg Y State n)
      (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) fun ω ↦ fidEmb (n + 1) (choose ω)

theorem fidCoin_flat {State St : Type} {W₂ : QReg → Type}
    (choose : Ω → OracleComp (fidSpec Sd Tw Msg Y) State)
    (ch : (Tw × Msg) ⊕ (Tw × Msg) → St → Option Y × St)
    (K : ∀ u, FidOut State u → St →
      QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) W₂ u) (n : ℕ) (s : St) :
    IAdv.flat ch K n s (fidCoinEmb choose n) =
      fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) fun ω ↦
        IAdv.flat ch K n s (fidEmb n (choose ω)) := by
  cases n with
  | zero => exact fidBind_bind _ (fun ω ↦ fidEmb 0 (choose ω)) _
  | succ n => exact fidBind_bind _ (fun ω ↦ fidEmb (n + 1) (choose ω)) _

/-- The uniform coin, run beside any runtime: each branch scales by `1/|Ω|`. -/
theorem fidCoin_branch (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y)) (ω : Ω) :
    (R.run₂ .instruments (QComp.act (spec := qrom2Spec (Dom Sd Tw Msg) Y)
      (SubInstrument.uniform Ω (QReg.of Unit)))).branch ω =
      ((Fintype.card Ω : ℂ)⁻¹) • LinearMap.id := by
  rw [QuantumRuntime.run₂_act, SubInstrument.bind_pure, DSubInstrument.branch_frame_apply]
  refine LinearMap.ext fun ρ ↦ ?_
  ext x x'
  simp [SubInstrument.branch_uniform_apply]

/-- **The coin averages**: the probability of an event after a uniform coin is the average over
the coin of the probabilities of the event for the continuations. -/
theorem fidCoin_leafProb {W : QReg → Type} (R : QuantumRuntime (qrom2Spec (Dom Sd Tw Msg) Y))
    (k : Ω → QuantumComp LocalSig.instruments.{0} (qrom2Spec (Dom Sd Tw Msg) Y) W (QReg.of Unit))
    {σ : Matrix (QReg.of Unit × R.D) (QReg.of Unit × R.D) ℂ} (hσ : σ.PosSemidef)
    (E : (Σ u, W u) → Prop) :
    leafProb R .instruments
        (fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) k) σ E =
      avg fun ω ↦ leafProb R .instruments (k ω) σ E := by
  unfold leafProb avg
  have hb : ∀ c, ENNReal.ofReal ((R.run .instruments
      (fidBind (QComp.act (SubInstrument.uniform Ω (QReg.of Unit))) k)).branch c σ).trace.re =
      ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ *
        ENNReal.ofReal ((R.run .instruments (k ω)).branch c σ).trace.re := fun c ↦ by
    have h := fid_run_fidBind R LocalSig.Interp.instruments.{0}
      (QComp.act (spec := qrom2Spec (Dom Sd Tw Msg) Y) (SubInstrument.uniform Ω (QReg.of Unit)))
      k c σ
    have hω : ∀ ω : Ω, (R.run .instruments (k ω)).branch c
        ((R.run₂ .instruments (QComp.act (spec := qrom2Spec (Dom Sd Tw Msg) Y)
          (SubInstrument.uniform Ω (QReg.of Unit)))).branch ω σ) =
        ((Fintype.card Ω : ℂ)⁻¹) • (R.run .instruments (k ω)).branch c σ := fun ω ↦
      (congrArg ((R.run .instruments (k ω)).branch c)
        (LinearMap.congr_fun (fidCoin_branch R ω) σ)).trans (by
          rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul])
    refine (congrArg (fun M ↦ ENNReal.ofReal (Matrix.trace M).re)
      (h.trans ((tsum_fintype _).trans (Finset.sum_congr rfl fun ω _ ↦ hω ω)))).trans ?_
    rw [Matrix.trace_sum, Complex.re_sum, ENNReal.ofReal_sum_of_nonneg]
    · refine Finset.sum_congr rfl fun ω _ ↦ ?_
      rw [Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos
          (by exact_mod_cast Fintype.card_pos), ENNReal.ofReal_natCast]
    · intro ω _
      rw [Matrix.trace_smul, smul_eq_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_inv,
        Complex.re_ofReal_mul]
      exact mul_nonneg (by positivity)
        (Complex.nonneg_iff.1
          ((R.run .instruments (k ω)).posSemidef_branch_apply c hσ).trace_nonneg).1
  simp only [hb, Finset.sum_mul]
  rw [Summable.tsum_finsetSum fun _ _ ↦ CompleteLattice.summable]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [← ENNReal.tsum_mul_left]
  exact tsum_congr fun c ↦ mul_assoc _ _ _

/-- The exact game on the coin embedding is the average over the coin of the exact game on
the embeddings of the deterministic adversaries. -/
theorem fid_coin_tcrExp_avg (cap : ℕ) (A : FidCoinAdv Ω Sd Tw Msg Y) (n : ℕ) :
    tcrExp .instruments (A := QReg.of Unit) (SubState.basis ()) cap n (fidCoinEmb A.choose n)
        (fidPh2 A.forge) =
      avg fun ω : Ω ↦ tcrExp .instruments (A := QReg.of Unit) (SubState.basis ()) cap n
        (fidEmb n (A.choose ω)) (fidPh2 A.forge) := by
  unfold tcrExp twoPhaseExp
  have h : ∀ (P : Sd) (Th : Dom Sd Tw Msg → Y),
      realProb .instruments (A := QReg.of Unit) (SubState.basis ()) (tcrCh cap) tcrInit n
        (fidCoinEmb A.choose n) (fidPh2 A.forge) tcrWin P Th =
      avg fun ω : Ω ↦ realProb .instruments (A := QReg.of Unit) (SubState.basis ()) (tcrCh cap)
        tcrInit n (fidEmb n (A.choose ω)) (fidPh2 A.forge) tcrWin P Th := fun P Th ↦ by
    unfold realProb composite
    rw [fidCoin_flat]
    exact fidCoin_leafProb _ _ (joint_posSemidef _) _
  simp only [h]
  rw [avg_congr fun P ↦ avg_comm _, avg_comm]

theorem fidCoin_run_lift {α : Type} (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (P : Sd) (oa : ProbComp α)
    (s : SM_DT_TCR_State Tw Msg) :
    (simulateQ (SM_DT_TCR_oracles (fidProblem cap Th) P)
      (liftM oa : OracleComp (unifSpec +
      (SM_DT_TCR_challengeSpec Tw Msg Y + collectionSpec (fidProblem cap Th).thColl)) α)).run s =
      oa >>= fun a ↦ pure (a, s) := by
  unfold SM_DT_TCR_oracles
  rw [QueryImpl.simulateQ_add_liftM_left]
  simp

/-- The rest of VCVio's experiment after the seed `P` and the coin `ω` are drawn. -/
noncomputable def fidCoinRest (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidCoinAdv Ω Sd Tw Msg Y)
    (P : Sd) (ω : Ω) : ProbComp Bool := do
  let (st, qsChal, _) ← (simulateQ (SM_DT_TCR_oracles (fidProblem cap Th) P)
    (simulateQ (fidInst cap Th) (A.choose ω))).run ([], [])
  let (j, m) ← simulateQ (fun q ↦ (pure (Th q) : ProbComp Y)) (A.forge st P)
  match qsChal[j]? with
  | none => return false
  | some (t, mj) => return decide (m ≠ mj ∧
      (fidProblem cap Th).th.eval P t m = (fidProblem cap Th).th.eval P t mj)

/-- VCVio's advantage of the coin adversary is the average over the coin of the advantages of
the deterministic adversaries. -/
theorem fid_coin_advantage (cap : ℕ) (Th : Dom Sd Tw Msg → Y) (A : FidCoinAdv Ω Sd Tw Msg Y) :
    SM_DT_TCR_Advantage (A.honest cap Th) =
      avg fun ω : Ω ↦ SM_DT_TCR_Advantage ((A.at ω).honest cap Th) := by
  have h1 : SM_DT_TCR_Experiment (A.honest cap Th) =
      (do let P ← $ᵗ Sd; let ω ← $ᵗ Ω; fidCoinRest cap Th A P ω : ProbComp Bool) := by
    unfold SM_DT_TCR_Experiment
    refine bind_congr (m := ProbComp) fun P ↦ ?_
    simp only [FidCoinAdv.honest]
    rw [simulateQ_bind, StateT.run_bind, fidCoin_run_lift]
    simp only [bind_assoc, pure_bind]
    rfl
  have h2 : ∀ ω, SM_DT_TCR_Experiment ((A.at ω).honest cap Th) =
      (do let P ← $ᵗ Sd; fidCoinRest cap Th A P ω : ProbComp Bool) := fun ω ↦ rfl
  unfold SM_DT_TCR_Advantage avg
  simp only [h2]
  rw [h1]
  simp only [← prEvent_eq_evalDist_singleton, prEvent_bind_eq_sum_fintype,
    SampleableType.prEvent_uniformSample_eq_singleton, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω _ ↦ Finset.sum_congr rfl fun P _ ↦ mul_left_comm _ _ _

/-- **Fidelity of the exact SM-DT-TCR game, classical adversaries with a uniform coin.** -/
theorem fid_coin_tcrExp_eq (cap : ℕ) (A : FidCoinAdv Ω Sd Tw Msg Y) (n : ℕ)
    (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n) :
    tcrExp .instruments (A := QReg.of Unit) (SubState.basis ()) cap n (fidCoinEmb A.choose n)
        (fidPh2 A.forge) =
      avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_TCR_Advantage (A.honest cap Th) := by
  rw [fid_coin_tcrExp_avg]
  simp only [fid_coin_advantage]
  rw [avg_comm]
  exact avg_congr fun ω ↦ fid_tcrExp_eq cap (A.at ω) n (hb ω)

theorem fid_coin_emb_isQueryBound {State : Type}
    (choose : Ω → OracleComp (fidSpec Sd Tw Msg Y) State) (n q : ℕ)
    (hq : ∀ ω, IsQueryBoundP (choose ω) fidIsHash q) :
    IAdv.IsQueryBound n (fidCoinEmb choose n) (firstBudget q) := by
  intro St ch s
  rw [fidCoin_flat]
  exact (fidBind_isQueryBound (b₁ := 0) (QComp.isQueryBound_act _ _)
    fun ω ↦ fid_emb_isQueryBound n (choose ω) q (hq ω) St ch s).mono (zero_add _).le

/-- **`tcr_exact_le` as a bound on VCVio's SM-DT-TCR advantage** of classical adversaries with
a uniform coin, averaged over the uniformly random tweakable hash. -/
theorem fid_coin_tcr_classical_le [Inhabited Tw] (cap : ℕ) (A : FidCoinAdv Ω Sd Tw Msg Y)
    (n q₁ q₂ : ℕ) (hb : ∀ ω, IsQueryBoundP (A.choose ω) fidIsReq n)
    (h1 : ∀ ω, IsQueryBoundP (A.choose ω) fidIsHash q₁)
    (h2 : ∀ st P, IsTotalQueryBound (A.forge st P) q₂) :
    (avg fun Th : Dom Sd Tw Msg → Y ↦ SM_DT_TCR_Advantage (A.honest cap Th)) ≤
      (((2 * (q₂ : ℝ≥0∞) + 1) ^ 2 / (Fintype.card Y : ℝ≥0∞)) ^ (2⁻¹ : ℝ) +
        2 * q₁ * ((Fintype.card Sd : ℝ≥0∞)⁻¹) ^ (2⁻¹ : ℝ)) ^ 2 := by
  rw [← fid_coin_tcrExp_eq cap A n hb]
  exact tcr_exact_le (fid_coin_emb_isQueryBound A.choose n q₁ h1)
    (fid_ph2_isQueryBound A.forge q₂ h2)

end PQ.QROM

#print axioms PQ.QROM.fidCoin_leafProb
#print axioms PQ.QROM.fid_coin_tcrExp_avg
#print axioms PQ.QROM.fid_coin_advantage
#print axioms PQ.QROM.fid_coin_tcrExp_eq
#print axioms PQ.QROM.fid_coin_tcr_classical_le
