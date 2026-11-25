import Parallel.PoolBorrow

/-! Safety of every finite path through the compiled pool destructor. The checker
projects the successful low-word branch, the raw job write, the release store,
and the two deliberate exits from rustc MIR. Other edges are unconstrained,
including loops and cleanup successors. -/
namespace ParallelPool.Guard

inductive Action where
  | other | acquiredLow | clearJob | releaseBusy | finish
  deriving DecidableEq, Repr

inductive Phase where
  | waiting | joined | cleared | released | finished | bad
  deriving DecidableEq, Repr

def next : Phase → Action → Phase
  | p, .other => p
  | .waiting, .acquiredLow => .joined
  | .joined, .clearJob => .cleared
  | .cleared, .releaseBusy => .released
  | .released, .finish => .finished
  | _, _ => .bad

/-- Newest event first, excluding steps that leave the protocol unchanged. -/
def events : Phase → List Action
  | .waiting | .bad => []
  | .joined => [.acquiredLow]
  | .cleared => [.clearJob,.acquiredLow]
  | .released => [.releaseBusy,.clearJob,.acquiredLow]
  | .finished => [.finish,.releaseBusy,.clearJob,.acquiredLow]

abbrev Edge := Nat × Action × Nat
abbrev Certificate := List (Nat × Phase)

/-- A finite overapproximation of reachable program counters and protocol states.
Lean checks each control-flow successor, including back edges. -/
def check (graph : List Edge) (states : Certificate) : Bool :=
  states.contains (0,.waiting) &&
  states.all (fun (pc,phase) => phase != .bad && graph.all fun (src,a,dst) =>
    src != pc || states.contains (dst,next phase a))

inductive Walk (graph : List Edge) : Nat → Phase → List Action → Prop where
  | start : Walk graph 0 .waiting []
  | edge {pc phase history dst a} : Walk graph pc phase history → (pc,a,dst) ∈ graph →
      Walk graph dst (next phase a) (a::history)

theorem walk_state {graph states} (cert : check graph states = true)
    {pc p history} (path : Walk graph pc p history) : (pc,p) ∈ states := by
  simp only [check,Bool.and_eq_true,List.contains_iff_mem,List.all_eq_true] at cert
  induction path with
  | start => exact cert.1
  | edge previous edge ih =>
    have h := (cert.2 _ ih).2 _ edge
    simpa using h

theorem walk_order {graph states} (cert : check graph states = true)
    {pc p history} (path : Walk graph pc p history) :
    p ≠ .bad ∧ history.filter (· != .other) = events p := by
  have present := walk_state cert path
  have allowed := cert
  simp only [check,Bool.and_eq_true,List.all_eq_true] at allowed
  have good : p ≠ .bad := by simpa using (allowed.2 _ present).1
  refine ⟨good,?_⟩
  induction path with
  | start => rfl
  | @edge prev before hist dst a prior _ ih =>
    have prevGood : before ≠ .bad := by simpa using (allowed.2 _ (walk_state cert prior)).1
    have prevOrder := ih (walk_state cert prior) prevGood
    cases before <;> cases a <;> simp_all [next,events] <;> assumption

/-- Every reached normal return or explicit worker-panic exit has the same
preceding three protocol operations. -/
theorem exit_order {graph states} (cert : check graph states = true)
    {pc p hist dst} (path : Walk graph pc p hist) (exitEdge : (pc,.finish,dst) ∈ graph) :
    hist.filter (· != .other) = [.releaseBusy,.clearJob,.acquiredLow] := by
  have safe := (walk_order cert (path.edge exitEdge)).1
  have order := (walk_order cert path).2
  cases p <;> simp_all [next,events]

/-- Feasibility of the MIR branch when its successful acquire reads this
counter word. The other edges carry no constraint on that observation. -/
def permits (observed : Nat) : Action → Bool
  | .acquiredLow => decide (observed < 2)
  | _ => true

/-- At the raw write, the specific load selected by the branch has seen the
release sequence of each assigned worker. The external atomic semantics
supply the modification order and reads-from window. -/
theorem clears_after_workers {graph states} (cert : check graph states = true)
    {pc p hist dst} (path : Walk graph pc p hist) (clearEdge : (pc,.clearJob,dst) ∈ graph)
    {n left count mods} (legal : Borrow.Trace n left count mods)
    (read : Borrow.ReadWindow (Borrow.counterWindow n mods))
    (lower : read.older.length ≤ read.source)
    (upper : read.source < read.older.length + (Borrow.counterWindow n mods).length)
    (branch : hist.all (permits read.seen.count) = true)
    (w : Nat) (assigned : w < n) : Borrow.ReleaseSequence w read.seen.mods := by
  have good := (walk_order cert (path.edge clearEdge)).1
  have ordered := (walk_order cert path).2
  have phase : p = .joined := by cases p <;> simp_all [next]
  have filtered : hist.filter (· != .other) = [.acquiredLow] := by simpa [phase,events] using ordered
  have lowEvent : Action.acquiredLow ∈ hist := (List.mem_filter.mp
    (show Action.acquiredLow ∈ hist.filter (· != .other) by rw [filtered]; simp)).1
  have low := List.all_eq_true.mp branch _ lowEvent
  exact Borrow.counter_source legal read lower upper (by simpa [permits] using low) w assigned

end ParallelPool.Guard
