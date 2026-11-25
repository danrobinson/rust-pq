import Parallel.PoolWorkerLease
import Parallel.PoolGuard
namespace ParallelPool.Lease.Caller

inductive Action where
  | other | publish | call | drop | normal | unwind
  deriving DecidableEq, Repr

inductive Phase where
  | owns | called | dropped (called : Bool) | returned | unwound (called : Bool) | bad
  deriving DecidableEq, Repr

def next : Phase → Action → Phase
  | p,.other => p
  | .owns,.publish => .owns
  | .owns,.call => .called
  | .owns,.drop => .dropped false
  | .called,.drop => .dropped true
  | .dropped true,.normal => .returned
  | .dropped b,.unwind => .unwound b
  | _,_ => .bad

def keep : Action → Bool
  | .other | .publish => false
  | _ => true

def calls : Bool → List Action
  | true => [.call]
  | false => []

def events : Phase → List Action
  | .owns | .bad => []
  | .called => [.call]
  | .dropped b => .drop :: calls b
  | .returned => [.normal,.drop,.call]
  | .unwound b => .unwind :: .drop :: calls b

abbrev Edge := Nat × Action × Nat
abbrev Certificate := List (Nat × Phase)

def check (start : Nat) (g : List Edge) (states : Certificate) : Bool :=
  states.contains (start,.owns) && states.all (fun st =>
    st.2 != .bad && g.all (fun e => e.1 != st.1 || states.contains (e.2.2,next st.2 e.2.1)))

inductive Walk (start : Nat) (g : List Edge) : Nat → Phase → List Action → Prop where
  | begin : Walk start g start .owns []
  | step {pc p hist a dest} : Walk start g pc p hist → (pc,a,dest)∈g →
      Walk start g dest (next p a) (a::hist)

private theorem history_step (p : Phase) (a : Action) (safe : next p a ≠ .bad)
    (hist : List Action) (earlier : hist.filter keep = events p) :
    (a::hist).filter keep = events (next p a) := by
  rw [List.filter_cons]
  cases p <;> cases a <;> simp_all [next,keep,events,calls]
  all_goals rename_i invoked
  all_goals cases invoked <;> simp_all [next,events,calls]

theorem all_paths {start g states} (valid : check start g states=true) {pc p hist}
    (path : Walk start g pc p hist) :
    (pc,p)∈states ∧ p≠.bad ∧ hist.filter keep=events p := by
  simp only [check,Bool.and_eq_true,List.contains_iff_mem,List.all_eq_true] at valid
  induction path with
  | begin => exact ⟨valid.1,by decide,rfl⟩
  | @step q prior trace a dest _ edge ih =>
    have member : (dest,next prior a)∈states := by simpa using (valid.2 _ ih.1).2 _ edge
    have good : next prior a≠.bad := by simpa using (valid.2 _ member).1
    refine ⟨member,good,?_⟩
    exact history_step prior a good trace ih.2.2

theorem normal_order {start g states} (valid : check start g states=true) {pc p hist d}
    (path : Walk start g pc p hist) (exit : (pc,.normal,d)∈g) :
    hist.filter keep=[.drop,.call] := by
  have safe := (all_paths valid (.step path exit)).2.1
  have order := (all_paths valid path).2.2
  cases p <;> simp_all [next,events,calls]
  rename_i invoked
  cases invoked <;> simp_all [next,calls]

theorem unwind_order {start g states} (valid : check start g states=true) {pc p hist d}
    (path : Walk start g pc p hist) (exit : (pc,.unwind,d)∈g) :
    ∃ invoked, hist.filter keep=.drop :: calls invoked := by
  have safe := (all_paths valid (.step path exit)).2.1
  have order := (all_paths valid path).2.2
  cases p <;> simp_all [next,events]
  rename_i invoked
  cases invoked <;> simp

end ParallelPool.Lease.Caller
