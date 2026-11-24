import Integration.SlhDsaShakePermutationLongGoals
import Integration.SlhDsaShakePermutationLongPosterior

/-! Forest-supported executions of the tagged, forward-only selection program. -/
namespace Reduction.ShakePermutation.Long.SelectTrace
open Classical Classic SparsePort SparsePort.Phase OracleSpec OracleComp PQ.Interactive SetOracle ENNReal
noncomputable section
set_option maxRecDepth 8192
variable {D Z T : Type}
abbrev Trace := EdgeTrace Words

def port : QueryImpl (Tagged T) (OracleComp (TwoWay Words))
  | .inl n => liftM ((TwoWay Words).query (.inl n))
  | .inr (_,x) => liftM ((TwoWay Words).query (.inr (false,x)))

inductive Move (t : Trace) (x : Words) : Words → Trace → Prop
  | replay {y} : (x,y) ∈ t → Move t x y t
  | fresh {y} : ¬old t false x → isolated t x y → Move t x y ((x,y)::t)

def all (p : OracleComp (Tagged T) Z) (t : Trace) (post : Z → Trace → Prop) : Prop :=
  OracleComp.construct (C:=fun _ => Trace → Prop) (fun z t => post z t) (fun i _ k t => match i with
  | .inl _ => ∀ r, k r t
  | .inr (_,x) => ∀ y t', Move t x y t' → k y t') p t

theorem bind (p : OracleComp (Tagged T) D) (k : D → OracleComp (Tagged T) Z) (t : Trace)
    (post : Z → Trace → Prop) (mid : D → Trace → Prop) (first : all p t mid)
    (next : ∀ d tr, mid d tr → all (k d) tr post) : all (p >>= k) t post := by
  induction p using OracleComp.inductionOn generalizing t with
  | pure x => simpa only [pure_bind] using next x t first
  | query_bind i f ih =>
    rw [bind_assoc]
    rcases i with n|⟨d,x⟩
    · exact fun v => ih v t (first v)
    · exact fun y u h => ih y u (first y u h)

private theorem mean_le {B : Type} [Fintype B] (f : B → ℝ≥0∞) (b : ℝ≥0∞) (h : ∀ a, f a ≤ b) : uniformMean f ≤ b := by
  by_cases he : Nonempty B
  · have := he; exact ShakeXof.mean_le_const h
  · have := not_nonempty_iff.mp he; simp [uniformMean]

theorem forest_le (p : OracleComp (Tagged T) Z) (t : Trace) (post : Z → Trace → Prop) (ok : all p t post)
    (Q : ℕ) (count : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase p) Q)
    (W : Z × Trace → ℝ≥0∞) (b : ℝ≥0∞) (hw : ∀ z u, post z u → u.length ≤ t.length+Q → W (z,u) ≤ b) :
    forest wordSplit 0 W (record (simulateQ port p) t) t ≤ b := by
  induction p using OracleComp.inductionOn generalizing t Q with
  | pure z => exact hw z t ok (by omega)
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query] at count ⊢
    rcases i with n|⟨d,x⟩
    · change uniformMean (fun r : Fin (n+1) => forest wordSplit 0 W (record (simulateQ port (k r)) t) t) ≤ b
      apply mean_le
      intro r
      exact ih r t (ok r) Q (count r) hw
    · change forestStep wordSplit 0 t false x (fun y u => forest wordSplit 0 W (record (simulateQ port (k y))
        (if old t false x then t else edge false x y :: t)) u) ≤ b
      unfold forestStep
      split
      next h =>
        exact ih h.choose t (ok _ _ (.replay h.choose_spec)) (Q-1) (count.2 _) (fun z u hz hl => hw z u hz (by omega))
      next h =>
        apply mean_le
        intro y
        exact ih y.val.val ((x,y.val.val)::t) (ok _ _ (.fresh h y.property)) (Q-1) (count.2 _) (fun z u hz hl => hw z u hz (by have := count.1; simp only [List.length_cons] at hl; omega))

theorem port_cost (p : OracleComp (Tagged T) Z) (Q : ℕ)
    (h : CountBound (fun i => i.isRight = true) (simulateQ Phase.erase p) Q) :
    CountBound (fun i => i.isRight = true) (simulateQ port p) Q := by
  induction p using OracleComp.inductionOn generalizing Q with
  | pure => trivial
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query] at h ⊢
    rcases i with n|⟨d,x⟩
    · exact fun r => ih r Q (h r)
    · exact ⟨h.1,fun y => ih y _ (h.2 y)⟩

theorem eager_port (p : OracleComp (Tagged T) Z) (π : Permutation) (W : Z → ℝ≥0∞) :
    eager π W (simulateQ port p) = Phase.run (fun _ => π) W p := by
  induction p using OracleComp.inductionOn with
  | pure z => rfl
  | query_bind i k ih =>
    simp only [simulateQ_bind,simulateQ_spec_query]
    rcases i with n|⟨d,x⟩
    · exact congrArg uniformMean (funext ih)
    · exact ih _
end
end Reduction.ShakePermutation.Long.SelectTrace
#print axioms Reduction.ShakePermutation.Long.SelectTrace.forest_le
