import Integration.SlhDsaShakePermutationClassicalForestBound
import Integration.SlhDsaShakeXofTcr

/-! A classical forward-query transcript cannot revisit the root capacity
as a permutation output in the collision-free forest. This is the phase-one
condition needed to isolate the tweak of each formatted first block. -/
namespace Reduction.ShakePermutation.SparsePort.Trace
open Classical Classic OracleComp OracleSpec PQ.Interactive SetOracle ENNReal
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 1000000
abbrev Fwd := unifSpec + (Words →ₒ Words)

def monitor (bad : Words → Prop) [DecidablePred bad] {α : Type} (p : OracleComp Fwd α) :
    OracleComp (TwoWay Words) Bool :=
  OracleComp.construct (C := fun _ => OracleComp (TwoWay Words) Bool) (fun _ => pure false)
    (fun i _ k => match i with
      | .inl n => (TwoWay Words).query (.inl n) >>= k
      | .inr x => (TwoWay Words).query (.inr (false,x)) >>= fun r =>
        if bad r then pure true else k r) p

def zeroCap (w : Words) := capOf w = 0

private theorem cost {α : Type} (p : OracleComp Fwd α) (bad : Words → Prop) [DecidablePred bad]
    (q : ℕ) (count : CountBound (fun i => i.isRight = true) p q) :
    CountBound (fun i => i.isRight = true) (monitor bad p) q := by
  induction p using OracleComp.inductionOn generalizing q with
  | pure => trivial
  | query_bind i k ih =>
    rw [countBound_query_bind] at count
    cases i with
    | inl n => exact (countBound_query_bind ..).mpr (fun r => ih r _ (count r))
    | inr x =>
      apply (countBound_query_bind ..).mpr
      exact ⟨count.1,fun r => by split <;> first | trivial | exact ih r _ (count.2 r)⟩

def clear (t : EdgeTrace Words) := ∀ p ∈ t, ¬zeroCap p.2

private theorem forest_query {α : Type} (ev : α → ℝ≥0∞) (x : Words)
    (k : Words → OracleComp (TwoWay Words) α) (t : EdgeTrace Words) :
    forest wordSplit 0 ev (((TwoWay Words).query (.inr (false,x))) >>= k) t =
      forestStep wordSplit 0 t false x (fun y t' => forest wordSplit 0 ev (k y) t') := rfl

private theorem monitor_step {α : Type} (x : Words) (k : Words → OracleComp Fwd α) :
    monitor zeroCap (Fwd.query (.inr x) >>= k) =
      (liftM ((TwoWay Words).query (.inr (false,x))) : OracleComp (TwoWay Words) Words) >>= (fun y => if zeroCap y then pure true else monitor zeroCap (k y)) := rfl

private theorem forest_clear {α : Type} (p : OracleComp Fwd α) (t : EdgeTrace Words) (ok : clear t) :
    forest wordSplit 0 (fun b => if b then 1 else 0) (monitor zeroCap p) t = 0 := by
  induction p using OracleComp.inductionOn generalizing t with
  | pure => rfl
  | query_bind i k ih =>
    rcases i with n|x
    · change uniformMean (fun r => forest wordSplit 0 _ (monitor zeroCap (k r)) t) = _
      simp only [ih _ t ok,uniformMean,mul_zero,Finset.sum_const_zero]
    · rw [monitor_step,forest_query]
      unfold forestStep
      split
      · rename_i hx
        have ne := ok (x,hx.choose) (by simpa only [orient,Bool.false_eq_true,ite_false] using hx.choose_spec)
        change ¬zeroCap hx.choose at ne
        simp only [ite_eq_right ne]
        exact ih _ t ok
      · let T := {z : PermutationConditioning.UnusedOutputs (orient false t) //
            (wordSplit z.val).2 ∉ forbidden wordSplit 0 t x}
        have fresh (y : T) : ¬zeroCap y.val.val := by
          intro h
          exact y.property (Finset.mem_insert.mpr (Or.inl h))
        have ok' (y : T) : clear (edge false x y.val.val :: t) := by
          intro z mem
          rcases List.mem_cons.mp mem with rfl|mem
          · exact fresh y
          · exact ok z mem
        change uniformMean (fun y : T => forest wordSplit 0 _
          (if zeroCap y.val.val then pure true else monitor zeroCap (k y.val.val)) _) = 0
        simp only [ite_eq_right (fresh _),ih _ _ (ok' _),uniformMean,mul_zero,Finset.sum_const_zero]

/-- The estimate is for the entire classical phase-one algorithm and
allows adaptive queries to the forward permutation. -/
theorem root_risk {α : Type} (p : OracleComp Fwd α) (Q : ℕ)
    (count : CountBound (fun i => i.isRight = true) p Q) :
    uniformMean (fun π : Permutation => eager π (fun b => if b then 1 else 0) (monitor zeroCap p)) ≤
      Q * forestPenalty Rate Words Q := by
  let ev : Bool → ℝ≥0∞ := fun b => if b then 1 else 0
  have h := lazy_forest wordSplit 0 ev (fun b => by cases b <;> simp [ev]) (monitor zeroCap p)
    Q Q (cost p zeroCap Q count) [] (by simp) ⟨⟨Equiv.refl _,by simp⟩⟩
  rw [← eager_lazy] at h
  simpa only [ev,forest_clear p [] (by simp [clear]),zero_add] using h

end
end Reduction.ShakePermutation.SparsePort.Trace
#print axioms Reduction.ShakePermutation.SparsePort.Trace.root_risk
