import Parallel.SigningSlots

namespace ParallelFused.Schedules
open ParallelCached

/-- The writes of the sorted phase-one tickets. Cells may be sparse because the
last finisher reserves and fills the remaining FORS direct slots itself. -/
structure Completion {S V : Type} [DecidableEq S] (jobs : List (List (S × V))) where
  workers : Nat
  state : Tickets.State S V
  positive : 0 < workers
  reachable : Tickets.Reach jobs workers state
  stopped : ¬ ∃ next, Tickets.Step jobs state next

theorem sameCells {S V : Type} [DecidableEq S] {jobs : List (List (S × V))}
    (unique : (jobs.flatten.map Prod.fst).Nodup) (left right : Completion jobs) :
    left.state.cells = right.state.cells :=
  interleavings (Tickets.maximal_join left.reachable left.positive unique left.stopped).2.2
    (Tickets.maximal_join right.reachable right.positive unique right.stopped).2.2

/-- Instantiate a physical slot certificate with arbitrary bytes at each slot. -/
theorem valued_unique (jobs : List (List Nat)) (value : Nat → V) (h : jobs.flatten.Nodup) :
    ((Tickets.valued jobs value).flatten.map Prod.fst).Nodup := by
  suffices eq : (Tickets.valued jobs value).flatten.map Prod.fst = jobs.flatten by rwa [eq]
  clear h
  induction jobs with
  | nil => rfl
  | cons first rest ih =>
    simp only [Tickets.valued,List.map_cons,List.flatten_cons,List.map_append,List.map_map] at *
    simpa [Function.comp_def] using congrArg (first ++ ·) ih

/-- The last finisher reduces the first ledger and constructs the phase-two
signing inputs. A successful reference execution transfers to any normal
interleaving and positive worker count in both phases, including the final
assembly's reads of the reduced phase-one data. -/
theorem signature_independent {S V T W A : Type} [DecidableEq S] [DecidableEq T]
    {jobs : List (List (S × V))} (unique : (jobs.flatten.map Prod.fst).Nodup)
    (next : (S → Option V) → List (List (T × W)))
    (assemble : (S → Option V) → (T → Option W) → A)
    (ref actual : Completion jobs)
    (nextUnique : ((next ref.state.cells).flatten.map Prod.fst).Nodup)
    (ref2 : Completion (next ref.state.cells)) (actual2 : Completion (next actual.state.cells))
    (expected : A) (correct : assemble ref.state.cells ref2.state.cells = expected) :
    assemble actual.state.cells actual2.state.cells = expected := by
  have lift {left right : S → Option V} (eq : left = right)
      (uniq : ((next right).flatten.map Prod.fst).Nodup)
      (x : Completion (next left)) (y : Completion (next right)) :
      assemble left x.state.cells = assemble right y.state.cells := by
    subst left
    rw [sameCells uniq x y]
  exact (lift (sameCells unique actual ref) nextUnique actual2 ref2).trans correct

end ParallelFused.Schedules
