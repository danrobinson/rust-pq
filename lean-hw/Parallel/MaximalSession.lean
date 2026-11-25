import Parallel.MaximalSchedules
import Parallel.RawChunkLayout
open Aeneas Aeneas.Std
namespace slhdsa.MaximalWorker
open ParallelCached ParallelCached.Tickets

def region (base len i : Nat) := if base ≤ i ∧ i < base+len then some (i-base) else none

/-- The first queue holds XMSS chunks, leaf keys, direct FORS fields and split
children in separate physical regions. Only the reducer writes the reserved
direct fields after the normal worker queue reaches its last increment. -/
structure PhasePlan (forest chunks leaves : Nat) where
  jobs : Jobs
  reducer : List Nat
  unique : (jobs.flatten.map Prod.fst).Nodup
  forestCover : (((jobs.flatten.map Prod.fst)++reducer).filterMap (region (chunks+leaves) forest)).Perm (List.range forest)
  chunkCover : ((jobs.flatten.map Prod.fst).filterMap (region 0 chunks)).Perm (List.range chunks)
  leafCover : ((jobs.flatten.map Prod.fst).filterMap (region chunks leaves)).Perm (List.range leaves)

def PhasePlan.forestLayout {f x l} (plan : PhasePlan f x l) : Layout f :=
  ⟨plan.jobs,plan.reducer,region (x+l) f,plan.unique,plan.forestCover⟩
def PhasePlan.chunkLayout {f x l} (plan : PhasePlan f x l) : Layout x :=
  ⟨plan.jobs,[],region 0 x,plan.unique,by simpa using plan.chunkCover⟩
def PhasePlan.leafLayout {f x l} (plan : PhasePlan f x l) : Layout l :=
  ⟨plan.jobs,[],region x l,plan.unique,by simpa using plan.leafCover⟩

structure MaxRun (jobs : Jobs) where
  workers : Nat
  workersPos : 0<workers
  capacity : jobs.length+workers < 2^UScalarTy.Usize.numBits
  state : State
  order : List Nat
  history : History jobs workers state order
  stopped : ¬∃ next, Step jobs state next

def MaxRun.project {n} (layout : Layout n) (run : MaxRun layout.jobs) : Execution n :=
  ⟨⟨layout,run.workers,run.workersPos⟩,⟨run.state,run.order,run.history,run.stopped⟩⟩

structure Session (forest chunks leaves wots : Nat) where
  plan : PhasePlan forest chunks leaves
  first : MaxRun plan.jobs
  second : MaxRun (single wots).jobs
  samePool : first.workers=second.workers

/-- The checked public caller uses only the parameter set's four concrete sizes.
Other sizes select a total default, without imposing hypotheses on the caller. -/
def atSize {n} (s : WidthEight.Ticket.Schedule n) (k : Nat) : WidthEight.Ticket.Schedule k :=
  if eq : n=k then eq ▸ s else WidthEight.Ticket.inOrder k

theorem at_size {n} (s : WidthEight.Ticket.Schedule n) : atSize s n=s := by simp [atSize]

def Session.schedules {f x l w} (session : Session f x l w) : WidthEight.Ticket.Schedules where
  forest := atSize ((session.first.project session.plan.forestLayout).schedule)
  chunks := atSize ((session.first.project session.plan.chunkLayout).schedule)
  leaves := atSize ((session.first.project session.plan.leafLayout).schedule)
  wots := atSize ((session.second.project (single w)).schedule)

def For (p : params.Params) := Session (p.k.val*(p.a.val+1))
  (ParallelRawChunks.slots p.hp.val (p.d.val*p.hp.val)).length (p.d.val-1) p.d.val

theorem Session.orders {f x l w} (s : Session f x l w) :
    (s.schedules.forest f).completed=(s.plan.reducer.reverse++s.first.order).filterMap (region (x+l) f) ∧
    (s.schedules.chunks x).completed=s.first.order.filterMap (region 0 x) ∧
    (s.schedules.leaves l).completed=s.first.order.filterMap (region x l) ∧
    (s.schedules.wots w).completed=s.second.order := by
  simp [Session.schedules,at_size,Execution.schedule,Maximal.schedule,MaxRun.project,
    PhasePlan.forestLayout,PhasePlan.chunkLayout,PhasePlan.leafLayout,single]

structure InitialRun (jobs : Jobs) where
  workers : Nat
  workersPos : 0<workers
  capacity : jobs.length+workers < 2^UScalarTy.Usize.numBits
  state : State
  order : List Nat
  history : History jobs workers state order

theorem InitialRun.can_complete {jobs} (start : InitialRun jobs) : ∃ final : MaxRun jobs,
    start.workers=final.workers ∧ Relation.ReflTransGen (Step jobs) start.state final.state ∧ start.order <:+ final.order := by
  obtain ⟨s,log,path,history,suffix,stopped⟩ := start.history.extend
  exact ⟨⟨start.workers,start.workersPos,start.capacity,s,log,history,stopped⟩,rfl,path,suffix⟩

noncomputable def InitialRun.complete {jobs} (start : InitialRun jobs) := Classical.choose start.can_complete

structure Beginning (forest chunks leaves wots : Nat) where
  plan : PhasePlan forest chunks leaves
  first : InitialRun plan.jobs
  second : InitialRun (single wots).jobs
  samePool : first.workers=second.workers

noncomputable def Beginning.complete {f x l w} (s : Beginning f x l w) : Session f x l w :=
  ⟨s.plan,s.first.complete,s.second.complete,
    (Classical.choose_spec s.first.can_complete).1.symm.trans (s.samePool.trans (Classical.choose_spec s.second.can_complete).1)⟩

theorem Beginning.extends {f x l w} (s : Beginning f x l w) :
    Relation.ReflTransGen (Step s.plan.jobs) s.first.state s.complete.first.state ∧
    s.first.order <:+ s.complete.first.order ∧
    Relation.ReflTransGen (Step (single w).jobs) s.second.state s.complete.second.state ∧
    s.second.order <:+ s.complete.second.order := by
  obtain ⟨_,firstPath,firstOrder⟩ := Classical.choose_spec s.first.can_complete
  obtain ⟨_,secondPath,secondOrder⟩ := Classical.choose_spec s.second.can_complete
  exact ⟨firstPath,firstOrder,secondPath,secondOrder⟩

def StartFor (p : params.Params) := Beginning (p.k.val*(p.a.val+1))
  (ParallelRawChunks.slots p.hp.val (p.d.val*p.hp.val)).length (p.d.val-1) p.d.val

def untouched {f x l w} (plan : PhasePlan f x l) (count : Nat) (positive : 0<count)
    (firstFit : plan.jobs.length+count<2^UScalarTy.Usize.numBits) (secondFit : (single w).jobs.length+count<2^UScalarTy.Usize.numBits) : Beginning f x l w :=
  ⟨plan,⟨count,positive,firstFit,initial count,[],.start⟩,⟨count,positive,secondFit,initial count,[],.start⟩,rfl⟩

theorem MaxRun.counter_fits {jobs} (run : MaxRun jobs) :
    run.state.counter<2^UScalarTy.Usize.numBits := (fetch_bound run.history.reachable run.capacity).1

end slhdsa.MaximalWorker
