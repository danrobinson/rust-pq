import Parallel.WorkerRuntime

namespace ParallelWorkerRuntime.Wots
open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive ParallelWorkerHeap ParallelWorkerInterleave

set_option backward.isDefEq.respectTransparency false

abbrev Bytes := alloc.vec.Vec U8

/-- The normal WOTS queue, retaining the failed OnceLock::set result. -/
def body (N : Usize) (len : Usize) (values : Usize → Bytes) : Program (Shared N) (ControlFlow Unit Unit) := do
  let j ← rmw .phase2Next 1#usize
  if j.val < len.val then
    let dest : ParallelWorkerCells.Ref (Shared N) Bytes := slot N (.wotsSigs j.val)
    let result ← ParallelWorkerInterleave.set dest (values j)
    match result with
    | .Ok _ => pure (cont ())
    | .Err _ => ParallelWorkerInterleave.liftResult (fail .panic)
  else pure (done ())

def worker (N len : Usize) (values : Usize → Bytes) : Program (Shared N) Unit :=
  runLoop (fun () => body N len values) ()

/-- A worker that has fetched j can retain it indefinitely before its store.
An occupied cell fails the worker and leaves the old bytes in place. -/
def saving (N len : Usize) (values : Usize → Bytes) (j : Usize) : Program (Shared N) Unit :=
  let dest : ParallelWorkerCells.Ref (Shared N) Bytes := slot N (.wotsSigs j.val)
  ITree.vis (E := effects (Shared N))
    (.atomic (fun s => if (s.cells (.wotsSigs j.val)).isNone then dest.write (values j) s else s))
    (fun s => if (s.cells (.wotsSigs j.val)).isNone then worker N len values else liftResult (fail .panic))

theorem unfold_worker (N len : Usize) (values : Usize → Bytes) :
    worker N len values = ITree.vis (E := effects (Shared N)) (.atomic (fun s => increment s .phase2Next 1#usize))
      (fun s => let j := oldTicket s .phase2Next
                if j.val < len.val then saving N len values j else pure ()) := by
  conv => lhs; unfold worker; rw [runLoop_unfold]
  have again (b : Unit) : runLoop (fun () => body N len values) b = worker N len values := by cases b; rfl
  simp only [again]
  simp only [body,rmw,vis_bind]
  congr 1
  funext s
  simp only [Bind.bind, itree_ret_bind]
  by_cases live : (oldTicket s .phase2Next).val < len.val
  · simp only [ite_eq_left live, ParallelWorkerInterleave.set, vis_bind, itree_vis_bind, itree_ret_bind, saving]
    congr 1
    · congr 1
      funext h
      cases found : h.cells (.wotsSigs (oldTicket s .phase2Next).val) <;>
        simp [slot,found]
    · funext h
      cases found : h.cells (.wotsSigs (oldTicket s .phase2Next).val) <;>
        simp [slot,found, pure_bind, liftResult, fail,vis_bind, Bind.bind,itree_ret_bind]
      congr 1; funext o; exact PEmpty.elim o
  · simp [live,pure_bind]

def Correct (len : Usize) (values : Usize → Bytes) (s : Shared N) : Prop :=
  ∀ i v, s.cells (.wotsSigs i) = some v → ∃ j : Usize, j.val = i ∧ i < len.val ∧ v = values j

inductive Residual (N len : Usize) (values : Usize → Bytes) : Program (Shared N) Unit → Prop where
  | next : Residual N len values (worker N len values)
  | save (j : Usize) (live : j.val < len.val) : Residual N len values (saving N len values j)
  | retired : Residual N len values (pure ())
  | failed : Residual N len values (liftResult (fail .panic))

private theorem correct_set {len : Usize} {values : Usize → Bytes} (s : Shared N)
    (good : Correct len values s) (j : Usize) (live : j.val < len.val) :
    Correct len values ((slot N (.wotsSigs j.val)).write (values j) s) := by
  intro i v found
  by_cases eq : j.val = i
  · subst i
    have same := read_after_write s.toHeap (.wotsSigs j.val) (values j)
    exact ⟨j,rfl,live,Option.some.inj (found.symm.trans same)⟩
  · have same := frame s.toHeap (.wotsSigs i) (.wotsSigs j.val) (by simp [eq]) (values j)
    exact good i v (same.symm.trans found)

/-- Inversion of an actual scheduled event, including duplicate-store failure. -/
theorem local_safe {N len} {values : Usize → Bytes} {w w'} {h h' : Shared N}
    (localState : Residual N len values w) (event : Step h [w] h' [w'])
    (good : Correct len values h) : Correct len values h' ∧ Residual N len values w' := by
  cases localState with
  | next =>
    rw [unfold_worker] at event
    obtain ⟨rfl,rfl⟩ := event.unique_worker (Step.atomic h [] [] _ _)
    refine ⟨good,?_⟩
    dsimp only
    split
    · exact .save _ ‹_›
    · exact .retired
  | save j live =>
    unfold saving at event
    obtain ⟨rfl,rfl⟩ := event.unique_worker (Step.atomic h [] [] _ _)
    by_cases empty : (h.cells (.wotsSigs j.val)).isNone
    · simpa only [ite_eq_left empty] using And.intro (correct_set h good j live) (Residual.next (N:=N) (len:=len) (values:=values))
    · simpa only [ite_eq_right empty] using And.intro good (Residual.failed (N:=N) (len:=len) (values:=values))
  | retired =>
    obtain ⟨f,k,impossible,_,_⟩ := event.single_view
    change ITree.ret () = ITree.vis _ _ at impossible
    grind
  | failed =>
    obtain ⟨f,k,impossible,_,_⟩ := event.single_view
    have clash := vis_inj_effect impossible
    cases clash

theorem all_schedules {N len} (values : Usize → Bytes) (h h' : Shared N) (workers : Nat)
    (threads : List (Program (Shared N) Unit))
    (run : Steps h (List.replicate workers (worker N len values)) h' threads)
    (init : Correct len values h) : Correct len values h' := by
  let invariant := fun (state : Shared N × List (Program (Shared N) Unit)) =>
    Correct len values state.1 ∧ ∀ w ∈ state.2, Residual N len values w
  have start : invariant (h, List.replicate workers (worker N len values)) := by
    refine ⟨init,?_⟩
    intro w hw
    obtain ⟨_,rfl⟩ := List.mem_replicate.mp hw
    exact .next
  have preserve {x y : Shared N × List (Program (Shared N) Unit)}
      (inv : invariant x) (step : Step x.1 x.2 y.1 y.2) : invariant y := by
    rcases x with ⟨s,xs⟩; rcases y with ⟨t,ys⟩
    dsimp only at step
    cases step with
    | atomic left right f k =>
      obtain ⟨valid,owned⟩ := inv
      have active := owned _ (List.mem_append_right _ List.mem_cons_self)
      have changed := local_safe active (Step.atomic s [] [] f k) valid
      refine ⟨changed.1,?_⟩
      intro w hw
      rcases List.mem_append.mp hw with before | rest
      · exact owned _ (List.mem_append_left _ before)
      rcases List.mem_cons.mp rest with rfl | after
      · exact changed.2
      · exact owned _ (List.mem_append_right _ (List.mem_cons_of_mem _ after))
  have whole : invariant (h',threads) := Relation.ReflTransGen.head_induction_on run
    (motive := fun s _ => invariant s → invariant (h',threads)) id
    (fun step _ ih inv => ih (preserve inv step)) start
  exact whole.1

end ParallelWorkerRuntime.Wots
