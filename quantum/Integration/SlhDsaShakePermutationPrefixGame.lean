import Integration.SlhDsaShakePermutationColumnGame
import Integration.SlhDsaShakePermutationFix

namespace Reduction.ShakePermutation.Fix
open Quantum PQ.Interactive PQ.QROM ENNReal Classical
open scoped Kronecker ComplexOrder

private theorem fix_first (f : List Rate → Rate) (p : List Rate) : (fix f p).head? = p.head? := by
  induction p using List.reverseRecOn with
  | nil => rfl
  | append_singleton p x ih =>
    rw [fix_append]
    cases p with
    | nil => rfl
    | cons a t =>
      cases h : fix f (a::t) with
      | nil => simp [h] at ih
      | cons b s => simpa [h] using ih

/-- If two tables agree on all rows with a given first block, correction of
paths starting with that block uses identical answers at every step. -/
theorem fix_on_prefix (f g : List Rate → Rate) (a : Rate)
    (agree : ∀ xs, xs.head? = some a → f xs = g xs) (p : List Rate) (hp : p.head? = some a) :
    fix f p = fix g p := by
  induction p using List.reverseRecOn with
  | nil => simp at hp
  | append_singleton p x ih =>
    by_cases empty : p = []
    · subst p; rfl
    · have head : p.head? = some a := by cases p <;> simp_all
      simp only [fix_append,ih head]
      simp [maskNext,agree _ ((fix_first g p).trans head)]

variable {I E : Type} [Nonempty I] [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- Changing a hidden key's entire first-block slice of the table costs
one hidden-column search bound for a corrected-path oracle, independently
of the length of its paths. This covers tests querying that oracle directly. -/
theorem prefix_game {T : ℕ} (tag : Option Rate → Option I)
    (f : List Rate → Rate) (g : I → List Rate → Rate)
    (keep : ∀ i p, tag p.head? ≠ some i → g i p = f p)
    (M : (Domain T → Rate) → Closed (WS (Domain T) Rate E) Bool) (q : ℕ)
    (hq : PUE (spec:=unifSpec) cnt0 M q) (ρ : SubState ((Domain T × Rate) × E)) :
    let test := fun t => qWeight (· = true) (M (fun p => transform t (List.ofFn p.2)))
      (ρ.matrix ⊗ₖ (SubState.basis ()).matrix)
    SetOracle.uniformMean (fun i => test (g i)) ≤ test f + ENNReal.ofReal (8*(q:ℝ)^2/Fintype.card I) := by
  dsimp only
  apply Program.fiber_game _ _ (fun p => tag (List.ofFn p.2).head?) _ M q hq ρ
  intro i p other
  let xs := List.ofFn p.2
  change transform (g i) xs = transform f xs
  change tag xs.head? ≠ some i at other
  cases h : xs.head? with
  | none =>
    have e := List.head?_eq_none_iff.mp h
    simpa [transform,e] using keep i xs other
  | some a =>
    have eq : ∀ l : List Rate, l.head? = some a → g i l = f l :=
      fun l hl => keep i l (by simpa only [hl,← h] using other)
    rw [transform,transform,fix_on_prefix _ _ _ eq xs h,eq _ ((fix_first f xs).trans h)]

end Reduction.ShakePermutation.Fix
#print axioms Reduction.ShakePermutation.Fix.prefix_game
