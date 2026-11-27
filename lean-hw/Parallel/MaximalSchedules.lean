import Parallel.MaximalWorker
import Parallel.WorkerSchedules
namespace slhdsa.MaximalWorker
open ParallelCached ParallelCached.Tickets

structure Setup (n : Nat) where
  layout : Layout n
  workers : Nat
  positive : 0<workers

structure Execution (n : Nat) extends Setup n where
  result : Maximal layout workers

def Execution.schedule {n} (run : Execution n) := run.result.schedule run.positive

def single (n : Nat) : Layout n where
  jobs := (List.range n).map (fun i => [(i,())])
  reducer := []
  select := some
  unique := by simpa [← List.flatMap_def,List.map_flatMap] using List.nodup_range (n:=n)
  cover := by simp [← List.flatMap_def,List.map_flatMap,Function.comp_def]

theorem fuel_bound {n} (run : Execution n) :
    run.result.state.counter=run.layout.jobs.length+run.workers ∧ run.result.state.live=[] ∧
      ¬ ∃ seq : Nat → State, ∀ i, Step run.layout.jobs (seq i) (seq (i+1)) := by
  obtain ⟨_,count,retired⟩ := order_complete run.result.history run.layout.unique run.positive run.result.stopped
  exact ⟨count,retired,fun ⟨seq,steps⟩ => no_infinite seq steps⟩

/-- A last-finisher history exists with precisely the terminal cell state of
this maximal run, including after stable or unstable reordering of tied jobs. -/
theorem last_finisher {n} (run : Execution n) (sorted : Jobs) (perm : run.layout.jobs.Perm sorted) :
    ∃ done, ParallelFused.LastFinisher.History sorted sorted.length [] done run.result.state.cells ∧ done.length=sorted.length := by
  have pairs : run.layout.jobs.flatten.Perm sorted.flatten := by simpa only [List.flatMap_id] using perm.flatMap_right id
  have own := (pairs.map Prod.fst).nodup_iff.mp run.layout.unique
  obtain ⟨log,cells,history,last⟩ := ParallelFused.LastFinisher.can_finish own
    (ParallelFused.LastFinisher.History.start (jobs:=sorted))
  have eq := equal_at_reduction perm run.result.history run.positive run.layout.unique run.result.stopped history last
  exact ⟨log,eq ▸ history,last⟩

end slhdsa.MaximalWorker
