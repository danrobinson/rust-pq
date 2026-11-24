import Integration.SlhDsaShakePermutationLongSelectGoals

/-! Eliminating the complete adaptive first phase of long-arity target collision resistance. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic SparsePort OracleSpec OracleComp SLHDSA MLink TweakableHash PQ.Interactive Quantum SetOracle ENNReal PermutationConditioning
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
local instance extFT {B : Type} [Fintype B] [DecidableEq B] (t : EdgeTrace B) : Fintype (Extensions t) := inferInstance
variable (S : Sha2Set) (ar : ℕ) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (A : QSM_DT_TCR_Adversary (ArityGame.Work E) (ArityGame.Base S ar seeds))
variable (forge : (Port → Words) → A.State → S.Node → Closed (ArityGame.Work E) (ℕ × Arity.Msg S ar))

def hits (dest : List Rate → Option S.Node) (π : Permutation) (p : List Rate) : Prop :=
  dest p = some (SkFormat.split S (Fix.ordinary π p)).1

private theorem monotone {X : Type} [Fintype X] {v w : X → ℝ≥0∞} (h : ∀ x, v x ≤ w x) : uniformMean v ≤ uniformMean w :=
  Finset.sum_le_sum (fun x _ => mul_le_mul' le_rfl (h x))

theorem fixed (pk : S.Node) (ar_bound : ar ≤ 67) (Q : ℕ) (b : ℝ≥0∞)
    (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) Q)
    (residual : ∀ (t : Trace) (_ : Nonempty (Extensions t)) (dest : List Rate → Option S.Node)
      (p : (ℕ × Arity.Msg S ar) → List Rate) (st : A.State),
      t.length ≤ Q → ¬bad (SkFormat.split S) dest t → (∀ jm, (p jm).length ≤ 17) →
      uniformMean (fun π : Extensions t => qWeight (fun jm => hits S dest π.val (p jm))
        (forge (oracle π.val) st pk) A.ρ₀) ≤ b) :
    uniformMean (fun π => tcrInner (ArityGame.adversary S ar seeds A forge π) pk) ≤ b + Q*forestPenalty Rate Words Q := by
  let P := Select.prog S ar pk A.choose ([],[])
  let W (π : Permutation) := ArityGame.test S ar seeds A forge pk (oracle π) (row S pk ar π)
  have native (π : Permutation) : tcrInner (ArityGame.adversary S ar seeds A forge π) pk = eager π (W π) (simulateQ port P) :=
    (ArityGame.run_actual S ar seeds A forge pk π _ (fun d m => (row_native S pk ar π (d,m)).symm)).trans (eager_port P π (W π)).symm
  simp_rw [native]
  have bound := forest_posterior W (simulateQ port P) (fun π z => qWeight_le_one _ _ A.posSemidef A.trace_eq_one) Q (port_cost P Q count)
  apply bound.trans (add_le_add _ le_rfl)
  change forest wordSplit 0 (terminal W) (record (simulateQ port P) []) [] ≤ b
  apply forest_le P [] _ (selection_all S pk ar A.choose ([],[]) [] [] (ledger_empty S pk ar)) Q count
  intro r t h len
  obtain ⟨log,ok⟩ := h
  by_cases comp : Nonempty (Extensions t)
  · let dest := goal S pk ar (targetMap S pk ar r.2.1 t)
    let paths := path S pk ar r.2.1
    apply le_trans _ (residual t comp dest paths r.1 (by simpa using len) (safe S pk ar ok) (path_length S pk ar ar_bound _))
    unfold terminal
    apply monotone
    intro π
    exact qWeight_mono (p:=PQ.Interactive.tcrWin r.2.1 (row S pk ar π.val)) (q:=fun jm => hits S dest π.val (paths jm))
      (fun jm win => winner S pk ar ok π jm win) (forge (oracle π.val) r.1 pk) A.ρ₀
  · have := not_nonempty_iff.mp comp; simp [terminal,uniformMean]

theorem total (ar_bound : ar ≤ 67) (Q : ℕ) (b : ℝ≥0∞)
    (count : ∀ pk, CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) Q)
    (residual : ∀ pk (t : Trace) (_ : Nonempty (Extensions t)) (dest : List Rate → Option S.Node)
      (p : (ℕ × Arity.Msg S ar) → List Rate) (st : A.State),
      t.length ≤ Q → ¬bad (SkFormat.split S) dest t → (∀ jm, (p jm).length ≤ 17) →
      uniformMean (fun π : Extensions t => qWeight (fun jm => hits S dest π.val (p jm))
        (forge (oracle π.val) st pk) A.ρ₀) ≤ b) :
    uniformMean (fun π => qSM_DT_TCR_Advantage (ArityGame.adversary S ar seeds A forge π)) ≤ b + Q*forestPenalty Rate Words Q := by
  simp only [qSM_DT_TCR_Advantage_eq_tsum]
  change uniformMean (fun π => ∑' pk, PQ.Interactive.prob seeds (· = pk) * tcrInner (ArityGame.adversary S ar seeds A forge π) pk) ≤ _
  rw [ShakeXof.mean_seed]
  calc _ ≤ ∑' pk, PQ.Interactive.prob seeds (· = pk) * (b + Q*forestPenalty Rate Words Q) :=
        tsum_le_tsum fun pk => mul_le_mul' le_rfl (fixed S ar seeds A forge pk ar_bound Q b (count pk) (residual pk))
       _ = (∑' pk, PQ.Interactive.prob seeds (· = pk)) * (b + Q*forestPenalty Rate Words Q) := ENNReal.tsum_mul_right
       _ ≤ _ := (mul_le_mul' (tsum_prob_eq_le_one _) le_rfl).trans (one_mul _).le
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.fixed
