import Parallel.LastFinisher

namespace ParallelFused.LastFinisher
open ParallelCached

/-- Exact values already present at the last increment, including sparse tables. -/
theorem cell_at_last {S V : Type} [DecidableEq S] {jobs : List (List (S × V))} {i active done cells}
    (history : History jobs i active done cells) (last : done.length=jobs.length) (s : S) (v : V) :
    cells s=some v ↔ (s,v) ∈ jobs.flatten := by
  rw [←Tickets.allWrites jobs]
  simpa only [List.mem_flatMap,List.mem_range] using ParallelCached.joined (reducer_cells history last) s v

/-- Work weights can change the order of ties. Every ordering with the same
ticket writes gives the same populated and unpopulated cells at reduction. -/
theorem reordered_cells {S V : Type} [DecidableEq S] {jobs reordered : List (List (S × V))}
    (perm : jobs.Perm reordered) {i₁ active₁ done₁ cells₁ i₂ active₂ done₂ cells₂}
    (left : History jobs i₁ active₁ done₁ cells₁) (last₁ : done₁.length=jobs.length)
    (right : History reordered i₂ active₂ done₂ cells₂) (last₂ : done₂.length=reordered.length) :
    cells₁=cells₂ := by
  have pair : jobs.flatten.Perm reordered.flatten := by
    simpa only [List.flatMap_id] using perm.flatMap_right id
  funext s
  have eq (v : V) : cells₁ s=some v ↔ cells₂ s=some v :=
    (cell_at_last left last₁ s v).trans (pair.mem_iff.trans (cell_at_last right last₂ s v).symm)
  cases h₁ : cells₁ s with
  | some v => exact ((eq v).mp h₁).symm
  | none =>
    cases h₂ : cells₂ s with
    | none => rfl
    | some v => simp [h₁] at *; exact False.elim ((eq v) h₂)

end ParallelFused.LastFinisher
