import Parallel.MaximalSession

namespace slhdsa.WorkerFetch
open MaximalWorker
open ParallelCached.Tickets

abbrev Rows := List (Nat × Unit)

/-- A worker can be descheduled after fetch_add and before jobs.get. -/
inductive Frame where
  | claim
  | fetched (index : Nat)
  | write (remaining : Rows)
  deriving DecidableEq

structure Machine where
  counter : Nat
  threads : List Frame
  cells : Nat → Option Unit

def Frame.pending (jobs : Jobs) : Frame → Option Rows
  | .claim => some []
  | .fetched index => jobs[index]?
  | .write rows => some rows

def Machine.view (jobs : Jobs) (m : Machine) : MaximalWorker.State :=
  ⟨min m.counter jobs.length, m.counter, m.threads.filterMap (Frame.pending jobs), m.cells⟩

def start (workers : Nat) : Machine := ⟨0,List.replicate workers .claim,fun _ => none⟩

/-- Events follow the normal Rust call sequence. Lookup and retirement do not
modify the shared counter. A successful set writes exactly one empty cell. -/
inductive Event (jobs : Jobs) : Machine → List Nat → Machine → List Nat → Prop where
  | fetch (l r c cells log) :
    Event jobs ⟨c,l ++ .claim :: r,cells⟩ log ⟨c+1,l ++ .fetched c :: r,cells⟩ log
  | found (l r c cells log i rows) (lookup : jobs[i]? = some rows) :
    Event jobs ⟨c,l ++ .fetched i :: r,cells⟩ log ⟨c,l ++ .write rows :: r,cells⟩ log
  | exhausted (l r c cells log i) (lookup : jobs[i]? = none) :
    Event jobs ⟨c,l ++ .fetched i :: r,cells⟩ log ⟨c,l ++ r,cells⟩ log
  | set (l r c cells log k tail) (empty : cells k = none) :
    Event jobs ⟨c,l ++ .write ((k,())::tail) :: r,cells⟩ log
      ⟨c,l ++ .write tail :: r,fun j => if j=k then some () else cells j⟩ (k::log)
  | finish (l r c cells log) :
    Event jobs ⟨c,l ++ .write [] :: r,cells⟩ log ⟨c,l ++ .claim :: r,cells⟩ log

theorem refines {jobs w m log m' log'} (step : Event jobs m log m' log')
    (prior : History jobs w (m.view jobs) log) : History jobs w (m'.view jobs) log' := by
  cases step with
  | fetch l r c cells log =>
    by_cases live : c < jobs.length
    · have le : c+1 ≤ jobs.length := by omega
      simp [Machine.view,Frame.pending,List.getElem?_eq_getElem live,Nat.min_eq_left live.le,
        Nat.min_eq_left le] at prior ⊢
      exact .claim prior live
    · have last : jobs.length ≤ c := by omega
      have after : jobs.length ≤ c+1 := by omega
      simp [Machine.view,Frame.pending,List.getElem?_eq_none last,Nat.min_eq_right last,
        Nat.min_eq_right after] at prior ⊢
      exact .retire prior rfl
  | found l r c cells log i rows lookup =>
    simpa [Machine.view,Frame.pending,lookup] using prior
  | exhausted l r c cells log i lookup =>
    simpa [Machine.view,Frame.pending,lookup] using prior
  | set l r c cells log k tail empty =>
    simp [Machine.view,Frame.pending] at prior ⊢
    exact .store prior empty
  | finish => simpa [Machine.view,Frame.pending] using prior

inductive Execution (jobs : Jobs) (workers : Nat) : Machine → List Nat → Prop where
  | begin : Execution jobs workers (start workers) []
  | next {m log m' log'} (before : Execution jobs workers m log) (step : Event jobs m log m' log') :
      Execution jobs workers m' log'

theorem Execution.history {jobs workers m log} (run : Execution jobs workers m log) :
    History jobs workers (m.view jobs) log := by
  induction run with
  | begin =>
    simpa [start,Machine.view,initial,Frame.pending,List.filterMap_replicate] using
      (History.start : History jobs workers (initial workers) [])
  | next _ event ih => exact refines event ih

/-- At least one actual event is enabled whenever a participating frame remains.
A live store cannot encounter an already filled cell in a unique physical plan. -/
theorem progress {jobs workers m log} (run : Execution jobs workers m log)
    (owns : (jobs.flatten.map Prod.fst).Nodup) (live : m.threads≠[]) :
    ∃ next later, Event jobs m log next later := by
  obtain ⟨c,frames,cells⟩ := m
  obtain ⟨first,rest,rfl⟩ := List.exists_cons_of_ne_nil live
  cases first with
  | claim => exact ⟨_,_,.fetch [] rest c cells log⟩
  | fetched i =>
    cases lookup : jobs[i]? with
    | none => exact ⟨_,_,.exhausted [] rest c cells log i lookup⟩
    | some rows => exact ⟨_,_,.found [] rest c cells log i rows lookup⟩
  | write rows =>
    cases rows with
    | nil => exact ⟨_,_,.finish [] rest c cells log⟩
    | cons pair tail =>
      obtain ⟨k,payload⟩ := pair
      cases payload
      have reachable := run.history.reachable
      obtain ⟨todo,perm,record⟩ := ledger reachable
      have member : (k,()) ∈ ((Machine.view jobs ⟨c,.write ((k,())::tail)::rest,cells⟩).live).flatten := by
        simp [Machine.view,Frame.pending]
      have empty := ParallelCached.pending_empty record (by simpa only [allWrites] using owns)
        (counter_exact reachable).2.1 (perm.mem_iff.mpr member)
      exact ⟨_,_,.set [] rest c cells log k tail empty⟩

private def credit (jobs : Jobs) : Frame → Nat
  | .claim => 3
  | .fetched i => match jobs[i]? with | none => 2 | some rows => 3*rows.length+5
  | .write rows => 3*rows.length+4

def remaining (jobs : Jobs) (m : Machine) : Nat :=
  let rest := jobs.drop m.counter
  3*rest.length + 3*rest.flatten.length + (m.threads.map (credit jobs)).sum

theorem decreases {jobs m log m' log'} (step : Event jobs m log m' log') :
    remaining jobs m' < remaining jobs m := by
  cases step with
  | fetch l r c cells log =>
    by_cases live : c<jobs.length
    · have cut := (List.getElem_cons_drop live).symm
      simp only [remaining,cut,List.length_cons,List.flatten_cons,List.length_append,
        List.map_append,List.map_cons,List.sum_append,List.sum_cons,credit,List.getElem?_eq_getElem live]
      omega
    · have old : jobs.length≤c := by omega
      have next : jobs.length≤c+1 := by omega
      simp [remaining,List.drop_eq_nil_of_le old,List.drop_eq_nil_of_le next,credit,List.getElem?_eq_none old]
  | found l r c cells log i rows lookup => simp [remaining,credit,lookup]
  | exhausted l r c cells log i lookup => simp [remaining,credit,lookup]
  | set => simp [remaining,credit]
  | finish => simp [remaining,credit]

theorem Event.extends_log {jobs m log m' log'} (step : Event jobs m log m' log') : log <:+ log' := by
  cases step <;> first | exact List.suffix_refl _ | exact List.suffix_cons _ _

/-- Extend the actual prefix, preserving every store already observed. -/
theorem complete {jobs workers m log} (run : Execution jobs workers m log)
    (owns : (jobs.flatten.map Prod.fst).Nodup) :
    ∃ final later, Execution jobs workers final later ∧
      Relation.ReflTransGen (fun (a b : Machine × List Nat) => Event jobs a.1 a.2 b.1 b.2)
        (m,log) (final,later) ∧ log <:+ later ∧ final.threads=[] := by
  by_cases done : m.threads=[]
  · exact ⟨m,log,run,.refl,List.suffix_refl _,done⟩
  · obtain ⟨next,later,step⟩ := progress run owns done
    obtain ⟨last,history,finished,path,preserved,retired⟩ := complete (run.next step) owns
    exact ⟨last,history,finished,path.head step,(step.extends_log).trans preserved,retired⟩
termination_by remaining jobs m
decreasing_by exact decreases step

private theorem needs_thread {jobs : Jobs} {s t : MaximalWorker.State} (step : Step jobs s t) :
    s.live ≠ [] := by cases step <;> simp

def Execution.joined {jobs workers m log} (run : Execution jobs workers m log)
    (positive : 0<workers) (capacity : jobs.length+workers < 2^Aeneas.Std.UScalarTy.Usize.numBits)
    (joined : m.threads=[]) : MaxRun jobs where
  workers := workers
  workersPos := positive
  capacity := capacity
  state := m.view jobs
  order := log
  history := run.history
  stopped := by
    have nil : (m.view jobs).live = [] := by simp [Machine.view,joined]
    rintro ⟨_,step⟩
    exact needs_thread step nil

def ready : Rows → Frame
  | [] => .claim
  | row::tail => .write (row::tail)

def lower (s : MaximalWorker.State) : Machine := ⟨s.counter,s.live.map ready,s.cells⟩

private theorem finish_if_empty {jobs workers c cells log} (l r : List Frame) (rows : Rows)
    (h : Execution jobs workers ⟨c, l ++ .write rows :: r, cells⟩ log) :
    Execution jobs workers ⟨c, l ++ ready rows :: r, cells⟩ log := by
  cases rows with
  | nil => exact h.next (.finish ..)
  | cons => exact h

/-- Every existing ticket history has an execution of the concrete split
operations with exactly its store log. In particular, requiring such a log
in a public proof cannot make previously admitted histories disappear. -/
theorem realize {jobs workers s log} (h : History jobs workers s log) :
    Execution jobs workers (lower s) log := by
  induction h with
  | start =>
    simpa [lower, initial, start, ready] using (Execution.begin : Execution jobs workers (start workers) [])
  | @claim i c cells l r log prior within ih =>
    have ct : c=i := ((counter_exact prior.reachable).2.2 within).1
    subst c
    simp [lower,ready] at ih ⊢
    have fetched := ih.next (.fetch (l.map ready) (r.map ready) i cells log)
    exact finish_if_empty _ _ _ (fetched.next (.found _ _ _ _ _ _ _ (List.getElem?_eq_getElem within)))
  | @store i c cells l r tail k v log prior empty ih =>
    cases v
    simp [lower,ready] at ih ⊢
    exact finish_if_empty _ _ _ (ih.next (.set (l.map ready) (r.map ready) c cells log k tail empty))
  | @retire i c cells l r log prior all ih =>
    have balance := (counter_exact prior.reachable).1
    have live := live_bound prior.reachable
    simp only at balance live
    have past : jobs.length ≤ c := by omega
    simp [lower,ready] at ih ⊢
    have fetched := ih.next (.fetch (l.map ready) (r.map ready) c cells log)
    exact fetched.next (.exhausted _ _ _ _ _ _ (List.getElem?_eq_none past))

structure Joined (jobs : Jobs) (workers : Nat) where
  machine : Machine
  log : List Nat
  run : Execution jobs workers machine log
  retired : machine.threads=[]
  capacity : jobs.length+workers < 2^Aeneas.Std.UScalarTy.Usize.numBits

def Joined.ofStopped {jobs workers m log} (run : Execution jobs workers m log)
    (owns : (jobs.flatten.map Prod.fst).Nodup) (stopped : ¬∃ next later, Event jobs m log next later)
    (capacity : jobs.length+workers < 2^Aeneas.Std.UScalarTy.Usize.numBits) : Joined jobs workers :=
  ⟨m,log,run,by by_contra active; exact stopped (progress run owns active),capacity⟩

theorem joins_from_prefix {jobs workers m log} (run : Execution jobs workers m log)
    (owns : (jobs.flatten.map Prod.fst).Nodup)
    (capacity : jobs.length+workers < 2^Aeneas.Std.UScalarTy.Usize.numBits) :
    ∃ endRun : Joined jobs workers, log <:+ endRun.log ∧
      Relation.ReflTransGen (fun (a b : Machine × List Nat) => Event jobs a.1 a.2 b.1 b.2)
        (m,log) (endRun.machine,endRun.log) := by
  obtain ⟨last,history,finished,path,preserved,retired⟩ := complete run owns
  exact ⟨⟨last,history,finished,retired,capacity⟩,preserved,path⟩

def fromMax {jobs : Jobs} (run : MaxRun jobs) (unique : (jobs.flatten.map Prod.fst).Nodup) :
    Joined jobs run.workers where
  machine := lower run.state
  log := run.order
  run := realize run.history
  retired := by
    have nil := (order_complete run.history unique run.workersPos run.stopped).2.2
    simp [lower,nil]
  capacity := run.capacity

/-- Supply the public signing theorems with the orders actually produced by
two event executions, including arbitrary pauses between fetch and lookup. -/
def session {f x l w workers} (plan : PhasePlan f x l) (positive : 0<workers)
    (phaseOne : Joined plan.jobs workers) (phaseTwo : Joined (single w).jobs workers) :
    Session f x l w :=
  ⟨plan, phaseOne.run.joined positive phaseOne.capacity phaseOne.retired,
    phaseTwo.run.joined positive phaseTwo.capacity phaseTwo.retired, rfl⟩

theorem session_orders {f x l w workers} (plan : PhasePlan f x l) (positive : 0<workers)
    (one : Joined plan.jobs workers) (two : Joined (single w).jobs workers) :
    let s := session plan positive one two
    (s.schedules.forest f).completed = (plan.reducer.reverse ++ one.log).filterMap (region (x+l) f) ∧
    (s.schedules.chunks x).completed = one.log.filterMap (region 0 x) ∧
    (s.schedules.leaves l).completed = one.log.filterMap (region x l) ∧
    (s.schedules.wots w).completed = two.log := (session plan positive one two).orders

end slhdsa.WorkerFetch
