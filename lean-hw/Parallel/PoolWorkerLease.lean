import Parallel.PoolLease
namespace ParallelPool.Lease.Worker

inductive Action where
  | other | copy | catchReturn | ok | panic | markFailed | idle | decrement | finish
  deriving DecidableEq, Repr

inductive Phase where
  | waiting | copied | caught | normal | panicked | flagged | idle (failed : Bool)
  | retired (failed : Bool) | finished (failed : Bool) | bad
  deriving DecidableEq, Repr

def next : Phase → Action → Phase
  | p,.other => p
  | .waiting,.copy => .copied
  | .copied,.catchReturn => .caught
  | .caught,.ok => .normal
  | .caught,.panic => .panicked
  | .panicked,.markFailed => .flagged
  | .normal,.idle => .idle false
  | .flagged,.idle => .idle true
  | .idle b,.decrement => .retired b
  | .retired b,.finish => .finished b
  | _,_ => .bad

def resultEvents : Bool → List Action
  | false => [.ok,.catchReturn,.copy]
  | true => [.markFailed,.panic,.catchReturn,.copy]

def events : Phase → List Action
  | .waiting | .bad => []
  | .copied => [.copy]
  | .caught => [.catchReturn,.copy]
  | .normal => resultEvents false
  | .panicked => [.panic,.catchReturn,.copy]
  | .flagged => resultEvents true
  | .idle b => .idle :: resultEvents b
  | .retired b => .decrement :: .idle :: resultEvents b
  | .finished b => .finish :: .decrement :: .idle :: resultEvents b

abbrev Edge := Nat × Action × Nat
abbrev Certificate := List (Nat × Phase)

def check (graph : List Edge) (states : Certificate) : Bool :=
  states.contains (0,.waiting) && states.all (fun st =>
    st.2 != .bad && graph.all (fun e => e.1 != st.1 || states.contains (e.2.2,next st.2 e.2.1)))

inductive Walk (graph : List Edge) : Nat → Phase → List Action → Prop where
  | start : Walk graph 0 .waiting []
  | step {pc p hist a dest} : Walk graph pc p hist → (pc,a,dest)∈graph →
      Walk graph dest (next p a) (a::hist)

theorem all_paths {graph states} (valid : check graph states=true) {pc p hist}
    (path : Walk graph pc p hist) :
    (pc,p)∈states ∧ p≠.bad ∧ hist.filter (· != .other)=events p := by
  simp only [check,Bool.and_eq_true,List.contains_iff_mem,List.all_eq_true] at valid
  induction path with
  | start => exact ⟨valid.1,by decide,rfl⟩
  | @step q prior trace a dest _ edge ih =>
    have member : (dest,next prior a)∈states := by simpa using (valid.2 _ ih.1).2 _ edge
    have good : next prior a≠.bad := by simpa using (valid.2 _ member).1
    refine ⟨member,good,?_⟩
    rcases ih with ⟨_,previous,h⟩
    cases prior <;> cases a <;> simp_all [next,events,resultEvents] <;> assumption

/-- A returning worker has finished calling the closure exactly once before
the Release store to its slot and the SeqCst decrement. A caught panic sets
the shared failure bit before retirement on all returning paths. -/
theorem finish_order {graph states} (valid : check graph states=true) {pc p hist dest}
    (path : Walk graph pc p hist) (exitEdge : (pc,.finish,dest)∈graph) :
    ∃ failed, hist.filter (· != .other)=.decrement :: .idle :: resultEvents failed := by
  have allowed := (all_paths valid (.step path exitEdge)).2.1
  have order := (all_paths valid path).2.2
  cases p <;> simp_all [next,events]
  rename_i failed
  cases failed <;> simp

end ParallelPool.Lease.Worker
