import Integration.SlhDsaShakePermutationLongBankHistory
import Integration.SlhDsaShakePermutationLongBankBudget
import Integration.SlhDsaShakePermutationLongTarget
import Integration.SlhDsaShakePermutationLongTargetEndpoint

/-! Applying the pinned-bank quantum search bound after the native adaptive collection phase. -/
namespace Reduction.ShakePermutation.Long.BankRun
open Classical SparsePort MLink SLHDSA Quantum OracleSpec OracleComp PQ.Interactive ENNReal SetOracle ItsrLabel
open scoped ComplexOrder
noncomputable section
open Tails
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000
variable (S : Sha2Set) (ar : ℕ) (seeds : ProbComp S.Node) {E : Type} [Fintype E] [DecidableEq E]
variable (A : QSM_DT_TCR_Adversary (ArityGame.Work E) (ArityGame.Base S ar seeds))
variable (forge : (Port → Words) → A.State → S.Node → Closed (ArityGame.Work E) (ℕ × Arity.Msg S ar))

def TargetReady (pk : S.Node) (π : Permutation) := ∀ (H : Table) (h : Select.History S ar) D log,
  Recorded S pk ar π H h D log → Graph.Good (layout π) (masks D false) (masks D true) →
  ∃ go : Target.Goal S, Target.label S π 17 go D = true ∧ ∀ F, Pins D F → ∀ jm,
    PQ.Interactive.tcrWin h.1 (SelectTrace.row S pk ar (perm π F)) jm → Target.hit S (perm π F) go (SelectTrace.path S pk ar h.1 jm)

private theorem path_ne (pk : S.Node) (l : List (Arity.Row S ar)) (jm : ℕ × Arity.Msg S ar) :
    SelectTrace.path S pk ar l jm ≠ [] := by
  intro e; have he := congrArg List.length e
  simp only [SelectTrace.path,blocks,messageBlocks_length,List.length_nil] at he; omega

theorem conditioned_of_step (pk : S.Node) (π : Permutation) (hp : ¬irregular π) (he : ¬Pairs.exceptional π)
    (h : ar ≤ 67) (q : ℕ) (hq : q ≤ 2^100)
    (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase (Select.prog S ar pk A.choose ([],[]))) q)
    (post : ∀ st, PUE (spec:=unifSpec) cnt0 (fun H => forge H st pk) (2^41)) (witness : TargetReady S ar pk π)
    (δ : ℝ≥0∞) (risk : ∀ D : Bank, D.size ≤ 3*2^100 → Graph.Good (layout π) (masks D false) (masks D true) →
      ∀ x, D x=none → uniformMean (fun v : Words => Classic.hit (¬Graph.Good (layout π)
        (masks (Function.update D x (some v)) false) (masks (Function.update D x (some v)) true))) ≤ δ) :
    uniformMean (fun H : Table => tcrInner (ArityGame.adversary S ar seeds A forge (perm π H)) pk) ≤
      ((2:ℝ≥0∞)^28)⁻¹ + ((3*q:ℕ):ℝ≥0∞)*δ := by
  let P := Select.prog S ar pk A.choose ([],[])
  let W (H : Table) : A.State × Select.History S ar → ℝ≥0∞ :=
    ArityGame.test S ar seeds A forge pk (oracle (perm π H)) (SelectTrace.row S pk ar (perm π H))
  let D₀ : Bank := fun _ => none
  have native (H : Table) : tcrInner (ArityGame.adversary S ar seeds A forge (perm π H)) pk =
      eval (Classic.fill D₀ H) (W (Classic.fill D₀ H)) (simulateQ (impl π) P) :=
    (ArityGame.run_actual S ar seeds A forge pk (perm π H) _ (fun d m => (SelectTrace.row_native S pk ar (perm π H) (d,m)).symm)).trans
      (eval_impl π H P (W H)).symm
  simp_rw [native]
  rw [posterior W (simulateQ (impl π) P) D₀]
  have charged := impl_cost π P q count
  let q₀ := 3 * 2^100
  have size0 : D₀.size=0 := by change (Finset.univ.filter (fun _ : Addr => (none : Option Words).isSome)).card = 0; simp
  let R (z : A.State × Select.History S ar) D := ∀ H, Pins D H → ∃ log, Recorded S pk ar π H z.2 D log
  let terminal (r : A.State × Select.History S ar) (D : Bank) := uniformMean (fun H => W (Classic.fill D H) r)
  have leaf (r : A.State × Select.History S ar) (D : Bank) (hist : R r D) (good : Graph.Good (layout π) (masks D false) (masks D true)) (size : D.size ≤ q₀) :
      terminal r D ≤ ((2:ℝ≥0∞)^28)⁻¹ := by
    obtain ⟨log,ok⟩ := hist (Classic.fill D default) (fill_pins D _)
    obtain ⟨go,clean,win⟩ := witness _ _ _ _ ok good
    have s := Target.fixed_search_benchmark S π hp he D (size.trans (by decide +kernel)) go clean
      (fun H => forge H r.1 pk) (post r.1) A.ρ₀ A.posSemidef A.trace_eq_one (SelectTrace.path S pk ar r.2.1)
      (path_ne S ar pk _) (SelectTrace.path_length S pk ar h _)
    apply le_trans _ s
    apply Classic.mean_mono
    intro H
    exact qWeight_mono (p:=PQ.Interactive.tcrWin r.2.1 (SelectTrace.row S pk ar (perm π (Classic.fill D H))))
      (q:=fun jm => Target.hit S (perm π (Classic.fill D H)) go (SelectTrace.path S pk ar r.2.1 jm))
      (win _ (fill_pins D H)) (forge (oracle (perm π (Classic.fill D H))) r.1 pk) A.ρ₀
  have bound := budget (simulateQ (impl π) P) D₀ q₀ (3*q) charged (by rw [size0,Nat.zero_add]; exact Nat.mul_le_mul_left _ hq)
    (fun d => Graph.Good (layout π) (masks d false) (masks d true)) (Graph.good_empty _) R (selection_all S pk ar π A.choose) terminal
    (fun r D => ShakeXof.mean_le_const (fun H => qWeight_le_one _ _ A.posSemidef A.trace_eq_one)) _ _ leaf risk
  exact bound
end
end Reduction.ShakePermutation.Long.BankRun
#print axioms Reduction.ShakePermutation.Long.BankRun.conditioned_of_step
