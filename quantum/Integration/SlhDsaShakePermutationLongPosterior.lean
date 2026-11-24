import Integration.SlhDsaShakeXofTcr
import Integration.SlhDsaShakePermutationLongResidual
import Integration.SlhDsaShakePermutationClassicalForestBound

/-! The posterior shared permutation after an adaptive classical prefix,
with a completely arbitrary quantum continuation evaluated at that same
permutation. The trace is recorded only once for repeated edges. -/
namespace Reduction.ShakePermutation.Long
open Classical Classic OracleSpec OracleComp PermutationConditioning SetOracle PQ.Interactive ENNReal
noncomputable section
variable {A Z : Type} [Fintype A] [DecidableEq A]

def record (p : OracleComp (TwoWay A) Z) : EdgeTrace A → OracleComp (TwoWay A) (Z × EdgeTrace A) :=
  OracleComp.construct (C := fun _ => EdgeTrace A → OracleComp (TwoWay A) (Z × EdgeTrace A))
    (fun z t => pure (z,t)) (fun i _ k t => match i with
    | .inl n => (TwoWay A).query (.inl n) >>= fun r => k r t
    | .inr (d,x) => (TwoWay A).query (.inr (d,x)) >>= fun y =>
      k y (if old t d x then t else edge d x y::t)) p

def terminal (W : Equiv.Perm A → Z → ℝ≥0∞) (v : Z × EdgeTrace A) :=
  uniformMean (fun π : Extensions v.2 => W π.val v.1)

private theorem swap {B C : Type} [Fintype B] [Fintype C] (f : B → C → ℝ≥0∞) :
    uniformMean (fun b => uniformMean (f b)) = uniformMean (fun c => uniformMean (fun b => f b c)) := by
  unfold uniformMean
  simp only [Finset.mul_sum]; rw [Finset.sum_comm]; simp only [mul_left_comm]

theorem posterior (W : Equiv.Perm A → Z → ℝ≥0∞) (p : OracleComp (TwoWay A) Z)
    (t : EdgeTrace A) (ok : Nonempty (Extensions t)) :
    uniformMean (fun π : Extensions t => eager π.val (W π.val) p) =
      lazyRun (terminal W) (record p t) t := by
  induction p using OracleComp.inductionOn generalizing t with
  | pure z => rfl
  | query_bind i k ih =>
    rcases i with n|⟨d,x⟩
    · change uniformMean (fun π : Extensions t => uniformMean (fun u => eager π.val (W π.val) (k u))) =
        uniformMean (fun u => lazyRun (terminal W) (record (k u) t) t)
      rw [swap]; exact congrArg uniformMean (funext (fun u => ih u t ok))
    · change uniformMean (fun π : Extensions t => eager π.val (W π.val) (k (call π.val d x))) =
        step t d x (fun y t' => lazyRun (terminal W) (record (k y) (if old t d x then t else edge d x y::t)) t')
      rw [conditional_step t d x ok (fun y π => eager π (W π) (k y))]
      refine (step_congr t d x ok (fun y t' ht => ih y t' ht)).trans ?_
      unfold step
      split <;> rfl

theorem posterior_empty (W : Equiv.Perm A → Z → ℝ≥0∞) (p : OracleComp (TwoWay A) Z) :
    uniformMean (fun π => eager π (W π) p) = lazyRun (terminal W) (record p []) [] := by
  let e : Equiv.Perm A ≃ Extensions [] := ⟨fun π => ⟨π,by simp⟩,Subtype.val,fun _ => rfl,fun _ => rfl⟩
  exact (mean_equiv e (fun π => eager π.val (W π.val) p)).trans (posterior W p [] ⟨e (Equiv.refl _)⟩)

omit [Fintype A] [DecidableEq A] in
theorem record_cost (p : OracleComp (TwoWay A) Z) (Q : ℕ) (t : EdgeTrace A)
    (h : CountBound (fun i => i.isRight = true) p Q) :
    CountBound (fun i => i.isRight = true) (record p t) Q := by
  induction p using OracleComp.inductionOn generalizing Q t with
  | pure => trivial
  | query_bind i k ih =>
    rw [countBound_query_bind] at h
    rcases i with n|⟨d,x⟩
    · exact fun u => ih u Q t (h u)
    · exact ⟨h.1,fun u => ih u (Q-1) _ (h.2 u)⟩

private theorem terminal_le (W : Equiv.Perm A → Z → ℝ≥0∞) (h : ∀ π z, W π z ≤ 1)
    (v : Z × EdgeTrace A) : terminal W v ≤ 1 := by
  unfold terminal
  by_cases hn : Nonempty (Extensions v.2)
  · have := hn; exact ShakeXof.mean_le_const (fun π => h π.val v.1)
  · have := not_nonempty_iff.mp hn; simp [uniformMean]

theorem forest_posterior (W : Permutation → Z → ℝ≥0∞) (p : OracleComp (TwoWay Words) Z)
    (bounded : ∀ π z, W π z ≤ 1) (Q : ℕ) (cost : CountBound (fun i => i.isRight = true) p Q) :
    uniformMean (fun π => eager π (W π) p) ≤ forest wordSplit 0 (terminal W) (record p []) [] +
      Q * forestPenalty Rate Words Q := by
  rw [posterior_empty]
  apply lazy_forest wordSplit 0 _ _ _ Q Q (record_cost p Q [] cost) [] (by simp) ⟨⟨Equiv.refl _,by simp⟩⟩
  exact terminal_le W bounded

end
end Reduction.ShakePermutation.Long
#print axioms Reduction.ShakePermutation.Long.forest_posterior
