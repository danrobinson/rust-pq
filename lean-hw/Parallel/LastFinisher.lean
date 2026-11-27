import Parallel.SigningSchedules
import Parallel.SigningPublication

namespace ParallelFused.LastFinisher
open ParallelCached ParallelSigning
variable {S V : Type} [DecidableEq S]

/-- Claiming a ticket gives its worker an ordered list of individual stores.
The completion RMW occurs only after that worker's last store. A failed fetch
has no effect on these cells or on the completion counter. -/
inductive History (jobs : List (List (S × V))) :
    Nat → List (Nat × List (S × V)) → List Nat → (S → Option V) → Prop where
  | start : History jobs 0 [] [] (fun _ => none)
  | claim {i active done cells} (old : History jobs i active done cells) (h : i < jobs.length) :
      History jobs (i+1) ((i,jobs[i])::active) done cells
  | store {i left right done cells j s v tail}
      (old : History jobs i (left ++ (j,(s,v)::tail)::right) done cells) (empty : cells s = none) :
      History jobs i (left ++ (j,tail)::right) done (fun k => if k=s then some v else cells k)
  | finish {i left right done cells j}
      (old : History jobs i (left ++ (j,[])::right) done cells) :
      History jobs i (left++right) (j::done) cells

theorem projections {jobs : List (List (S × V))} {i active done cells}
    (history : History jobs i active done cells) :
    i ≤ jobs.length ∧ i = active.length + done.length ∧
    Trace jobs.length i (active.map Prod.fst) done ∧
    Run jobs.length (Tickets.writes jobs) i (active.flatMap Prod.snd) cells := by
  induction history with
  | start => exact ⟨Nat.zero_le _,rfl,.start,.start⟩
  | claim old h ih =>
    obtain ⟨bound,len,trace,run⟩ := ih
    refine ⟨h,by simp only [List.length_cons]; omega,.claim trace h,?_⟩
    simpa [Tickets.writes,List.getElem?_eq_getElem h] using run.claim h
  | @store i left right done cells j s v tail old empty ih =>
    obtain ⟨bound,len,trace,run⟩ := ih
    simp only [List.length_append,List.length_cons,List.map_append,List.map_cons,
      List.flatMap_append,List.flatMap_cons,List.cons_append] at *
    exact ⟨bound,len,trace,.publish run empty⟩
  | @finish i left right done cells j old ih =>
    obtain ⟨bound,len,trace,run⟩ := ih
    simp only [List.length_append,List.length_cons,List.map_append,List.map_cons,
      List.flatMap_append,List.flatMap_cons,List.nil_append] at *
    exact ⟨bound,by omega,trace.publish List.perm_middle,run⟩

/-- The last finisher can read the complete ledger immediately. Other workers
can still be in the pool, including ones that have yet to take an exit ticket. -/
theorem reducer_cells {jobs : List (List (S × V))} {i active done cells}
    (history : History jobs i active done cells) (last : done.length = jobs.length) :
    Run jobs.length (Tickets.writes jobs) jobs.length [] cells := by
  obtain ⟨bound,len,_,run⟩ := projections history
  have empty : active=[] := List.length_eq_zero_iff.mp (by omega)
  have all : i=jobs.length := by simp [empty,last] at len; exact len
  simpa [empty,all] using run

theorem reference_cells {jobs : List (List (S × V))} {i active done cells}
    (history : History jobs i active done cells) (last : done.length = jobs.length)
    (ref : Schedules.Completion jobs) (unique : (jobs.flatten.map Prod.fst).Nodup) :
    cells = ref.state.cells :=
  interleavings (reducer_cells history last)
    (Tickets.maximal_join ref.reachable ref.positive unique ref.stopped).2.2

private theorem finishOne {jobs : List (List (S × V))} (unique : (jobs.flatten.map Prod.fst).Nodup)
    {i rest done cells j remaining} (h : History jobs i ((j,remaining)::rest) done cells) :
    ∃ stored, History jobs i rest (j::done) stored := by
  induction remaining generalizing cells with
  | nil => exact ⟨_,History.finish (left:=[]) (right:=rest) h⟩
  | cons pair tail ih =>
    obtain ⟨slot,v⟩ := pair
    obtain ⟨bound,_,_,ledger⟩ := projections h
    have empty := pending_empty ledger (by rwa [Tickets.allWrites]) bound
      (show (slot,v) ∈ List.flatMap Prod.snd ((j,(slot,v)::tail)::rest) by simp)
    exact ih (History.store (left:=[]) (right:=rest) h empty)

private theorem drain {jobs : List (List (S × V))} (unique : (jobs.flatten.map Prod.fst).Nodup)
    {i active done cells} (h : History jobs i active done cells) :
    ∃ done' cells', History jobs i [] done' cells' := by
  induction active generalizing done cells with
  | nil => exact ⟨_,_,h⟩
  | cons head rest ih =>
    obtain ⟨j,remaining⟩ := head
    obtain ⟨_,finished⟩ := finishOne unique h
    exact ih finished

/-- From any finite normal history a worker can complete the queue. Uniqueness
of physical writes suffices even when one grouped job owns many cells. -/
theorem can_finish {jobs : List (List (S × V))} (unique : (jobs.flatten.map Prod.fst).Nodup)
    {i active done cells} (h : History jobs i active done cells) :
    ∃ done' cells', History jobs jobs.length [] done' cells' ∧ done'.length=jobs.length := by
  obtain ⟨later,stored,drained⟩ := drain unique h
  by_cases more : i < jobs.length
  · exact can_finish unique (History.claim drained more)
  · have bound := (projections drained).1
    have eq : i=jobs.length := by omega
    have count := (projections drained).2.1
    exact ⟨later,stored,eq ▸ drained,by simpa using count.symm.trans eq⟩
termination_by jobs.length-i

/-- The reducer can already supply the same final signature as a reference
schedule at the last increment, even before the other invocations retire. -/
theorem signature_at_last {T W A : Type} [DecidableEq T]
    {jobs : List (List (S × V))} {i active done cells}
    (history : History jobs i active done cells) (last : done.length = jobs.length)
    (ref : Schedules.Completion jobs) (unique : (jobs.flatten.map Prod.fst).Nodup)
    (next : (S → Option V) → List (List (T × W))) (assemble : (S → Option V) → (T → Option W) → A)
    (nextUnique : ((next ref.state.cells).flatten.map Prod.fst).Nodup)
    (actual2 : Schedules.Completion (next cells)) (ref2 : Schedules.Completion (next ref.state.cells)) :
    assemble cells actual2.state.cells = assemble ref.state.cells ref2.state.cells := by
  have equal := reference_cells history last ref unique
  subst cells
  rw [Schedules.sameCells nextUnique actual2 ref2]

/-- The same concrete history supplies the release/acquire ordering for every
published cell. The atomic model is shared with the signer source gate. -/
theorem visibility {jobs : List (List (Nat × V))} {i active done cells}
    (history : History jobs i active done cells) (last : done.length = jobs.length)
    {ticket cell value} (valid : ticket < jobs.length) (entry : (cell,value) ∈ jobs[ticket]) (w : Nat) :
    let owns := fun j s => ∃ v, (s,v) ∈ Tickets.writes jobs j
    Publication.Before done.reverse owns (.slot ticket cell) .reduce ∧
    Publication.Before done.reverse owns (.slot ticket cell) (.readRoots w) := by
  apply Publication.ready_sees_cells (projections history).2.2.1 last _ valid _ w
  exact ⟨value,by simpa [Tickets.writes,List.getElem?_eq_getElem valid] using entry⟩

end ParallelFused.LastFinisher
