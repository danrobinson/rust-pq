import Parallel.WorkerHeap
import Parallel.WorkerPayload

namespace ParallelWorkerHeap
open Aeneas Aeneas.Std Result slhdsa.WorkerPayload

/-- At the acquire barrier, retain every phase-one byte and counter. Install
the live WOTS queue view into that same heap. -/
def wotsHeap (base : Heap N) (m : Machine (alloc.vec.Vec U8)) : Heap N where
  counts
    | .phase2Next => m.counter
    | c => base.counts c
  cells
    | .wotsSigs i => m.cells i
    | .sigFors => base.cells .sigFors
    | .xmssAuth => base.cells .xmssAuth
    | .roots => base.cells .roots
    | .xmssSlots i => base.cells (.xmssSlots i)
    | .leafPks i => base.cells (.leafPks i)
    | .forsDirect i => base.cells (.forsDirect i)
    | .forsSplit i => base.cells (.forsSplit i)

theorem wots_begin (base : Heap N) (workers : Nat) (zero : base.counts .phase2Next = 0)
    (fresh : ∀ i, base.cells (.wotsSigs i) = none) : wotsHeap base (start workers) = base := by
  cases base with
  | mk counts cells =>
    apply Heap.ext
    · funext c; cases c <;> simp_all [wotsHeap,start] <;> rfl
    · funext k; cases k <;> simp_all [wotsHeap,start] <;> rfl

/-- Each scheduling microstep acts on actual values in the common heap. This
also specifies the old ticket returned to the fetching worker. -/
inductive WotsAction {N : Usize} : Heap N → Heap N → Prop where
  | idle (h) : WotsAction h h
  | claim (h) (i) (ticket : (fetch .phase2Next h).1 = i) :
    WotsAction h (fetch .phase2Next h).2
  | put (h h') (i : Nat) (v : alloc.vec.Vec U8)
      (stored : ParallelWorkerCells.set (ref N (.wotsSigs i)) v h = ok (.Ok (),h')) :
    WotsAction h h'

theorem wots_step (base : Heap N) {jobs m log m' log'}
    (event : Event jobs m log m' log') : WotsAction (wotsHeap base m) (wotsHeap base m') := by
  cases event with
  | fetch l r c cells log =>
    convert WotsAction.claim (wotsHeap base ⟨c,l ++ .claim :: r,cells⟩) c rfl using 1
    apply Heap.ext
    · funext k; cases k <;> rfl
    · rfl
  | set l r c cells log k v tail fresh =>
    apply WotsAction.put _ _ k v
    let h := wotsHeap base ⟨c,l ++ .write ((k,v)::tail) :: r,cells⟩
    have stored := ParallelWorkerCells.set_empty (ref N (.wotsSigs k)) v h fresh
    refine stored.trans ?_
    apply congrArg (fun x : Heap N => ok (core.result.Result.Ok (), x))
    apply Heap.ext
    · rfl
    funext j
    cases j <;> simp [h,wotsHeap,ref,write]
    rename_i i
    by_cases eq : k=i
    · subst i; simp <;> rfl
    · simp [eq,Ne.symm eq] <;> rfl
  | found | exhausted | finish => exact .idle _

theorem wots_heap_run (base : Heap N) {jobs workers m log} (run : Execution jobs workers m log)
    (zero : base.counts .phase2Next = 0) (fresh : ∀ i, base.cells (.wotsSigs i) = none) :
    Relation.ReflTransGen WotsAction base (wotsHeap base m) := by
  induction run with
  | begin => rw [wots_begin base _ zero fresh]
  | next _ event ih => exact ih.tail (wots_step base event)

end ParallelWorkerHeap
