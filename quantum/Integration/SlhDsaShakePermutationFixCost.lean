import Integration.SlhDsaShakePermutationFix
import PQ.Interactive.QromBridgeEval

namespace Reduction.ShakePermutation.Fix
open OracleComp OracleSpec PQ.Interactive
variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [AddCommGroup Y]

/-- An answer table can use a bounded public oracle on short strings and a
private table outside this cap. Each short prefix costs at most one read. -/
theorem fix_cost (f : (X → Y) → List Rate → Rate) (L : ℕ)
    (h : ∀ s, EvalCost (fun H => pure (f H s)) (if s.length ≤ L then 1 else 0)) (xs : List Rate) :
    EvalCost (fun H => pure (fix (f H) xs)) (min (xs.length-1) L) := by
  induction xs using List.reverseRecOn with
  | nil => simpa using (EvalCost.const (X := X) (Y := Y) (pure ([] : List Rate)))
  | append_singleton xs x ih =>
    by_cases zero : xs = []
    · subst xs
      simpa [fix,maskNext] using (EvalCost.const (X := X) (Y := Y) (pure [x]))
    let step (p : List Rate) (H : X → Y) :=
      if p.length = xs.length then (pure (p ++ [rateXor x (f H p)]) : ProbComp (List Rate))
      else pure []
    have readCost (p : List Rate) : EvalCost (step p) (if xs.length ≤ L then 1 else 0) := by
      by_cases size : p.length = xs.length
      · have e := (h p).map (fun r => p ++ [rateXor x r])
        simpa only [step,ite_eq_left size,size,ite_true,map_pure] using e
      · simpa only [step,ite_eq_right size] using (EvalCost.const (X := X) (Y := Y) (pure ([] : List Rate))).mono
          (Nat.zero_le (if xs.length ≤ L then 1 else 0))
    have e := EvalCost.bind ih readCost
    have prog : (fun H => pure (fix (f H) xs) >>= fun p => step p H) =
        (fun H => (pure (fix (f H) (xs ++ [x])) : ProbComp _)) := by
      funext H
      simp [step,maskNext,zero]
    rw [prog] at e
    refine e.mono ?_
    have hlen : 0 < xs.length := List.length_pos_iff.mpr zero
    simp only [List.length_append,List.length_cons,List.length_nil]
    split <;> omega

/-- One answer on an arbitrarily long tail requires at most L+1 public reads.
Every later prefix can be evaluated with the private completion. -/
theorem transform_cost (f : (X → Y) → List Rate → Rate) (L : ℕ)
    (h : ∀ s, EvalCost (fun H => pure (f H s)) (if s.length ≤ L then 1 else 0)) (xs : List Rate) :
    EvalCost (fun H => pure (transform (f H) xs)) (L+1) := by
  have e := EvalCost.bind (fix_cost f L h xs) (fun s => (h s).mono (show (if s.length ≤ L then 1 else 0) ≤ 1 by split <;> decide))
  simpa only [pure_bind,transform] using e.mono (Nat.add_le_add_right (Nat.min_le_right _ _) 1)

end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.transform_cost
