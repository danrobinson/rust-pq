import Parallel.WorkerHeapQueue
import Parallel.WorkerBarrier

namespace ParallelWorkerHeap
open Aeneas Aeneas.Std Result slhdsa
abbrev Monitor (N : Usize) := WorkerBarrier.Heap (alloc.vec.Vec U8)
  (alloc.vec.Vec (Array U8 N)) (alloc.vec.Vec (Array U8 N))

/-- The monitor uses the same three cells read by WOTS and post-join assembly. -/
def barrierHeap (base : Heap N) (b : Monitor N) : Heap N where
  counts := base.counts
  cells
    | .sigFors => b.cells.fors
    | .xmssAuth => b.cells.auth
    | .roots => b.cells.roots
    | .wotsSigs i => base.cells (.wotsSigs i)
    | .xmssSlots i => base.cells (.xmssSlots i)
    | .leafPks i => base.cells (.leafPks i)
    | .forsDirect i => base.cells (.forsDirect i)
    | .forsSplit i => base.cells (.forsSplit i)

inductive BarrierAction {N : Usize} : Heap N → Heap N → Prop where
  | idle (h) : BarrierAction h h
  | store (h h') (k : Key) (v : Payload N k)
      (stored : ParallelWorkerCells.set (ref N k) v h = ok (.Ok (),h')) :
    BarrierAction h h'

theorem barrier_step (base : Heap N) {f a r} {h h' : Monitor N}
    (step : WorkerBarrier.Step f a r h h') : BarrierAction (barrierHeap base h) (barrierHeap base h') := by
  cases step with
  | setFors _ clear =>
    apply BarrierAction.store _ _ .sigFors f
    refine (ParallelWorkerCells.set_empty (ref N .sigFors) f (barrierHeap base h) clear).trans ?_
    apply congrArg (fun x : Heap N => ok (core.result.Result.Ok (),x))
    apply Heap.ext <;> first | rfl | (funext j; cases j <;> rfl)
  | setAuth _ clear =>
    apply BarrierAction.store _ _ .xmssAuth a
    refine (ParallelWorkerCells.set_empty (ref N .xmssAuth) a (barrierHeap base h) clear).trans ?_
    apply congrArg (fun x : Heap N => ok (core.result.Result.Ok (),x))
    apply Heap.ext <;> first | rfl | (funext j; cases j <;> rfl)
  | setRoots _ clear =>
    apply BarrierAction.store _ _ .roots r
    refine (ParallelWorkerCells.set_empty (ref N .roots) r (barrierHeap base h) clear).trans ?_
    apply congrArg (fun x : Heap N => ok (core.result.Result.Ok (),x))
    apply Heap.ext <;> first | rfl | (funext j; cases j <;> rfl)
  | _ => exact .idle _

theorem barrier_run (base : Heap N) {f a r} {h : Monitor N} (run : WorkerBarrier.Run f a r h)
    (fc : base.cells .sigFors = none) (ac : base.cells .xmssAuth = none)
    (rc : base.cells .roots = none) :
    Relation.ReflTransGen BarrierAction base (barrierHeap base h) := by
  induction run with
  | refl =>
    have eq : barrierHeap base WorkerBarrier.initial = base := by
      apply Heap.ext <;> first | rfl | skip
      funext j
      cases j <;> first | rfl | exact fc.symm | exact ac.symm | exact rc.symm
    rw [eq]
  | tail _ event ih => exact ih.tail (barrier_step base event)

/-- Starting with the phase-one heap, install the three reducer values, cross
the acquire barrier, and run any prefix of phase two. All WOTS publications
and post-join reads see the same physical cells throughout this path. -/
theorem barrier_to_wots (base : Heap N) {f a r} {h : Monitor N}
    (monitor : WorkerBarrier.Run f a r h) {i} (passed : h.workers i = .reading)
    (fc : base.cells .sigFors = none) (ac : base.cells .xmssAuth = none)
    (rc : base.cells .roots = none) (zero : base.counts .phase2Next = 0)
    (fresh : ∀ j, base.cells (.wotsSigs j) = none) {jobs workers m log}
    (run : WorkerPayload.Execution jobs workers m log) :
    let joined := wotsHeap (barrierHeap base h) m
    Relation.ReflTransGen BarrierAction base (barrierHeap base h) ∧
    Relation.ReflTransGen WotsAction (barrierHeap base h) joined ∧
    joined.cells .sigFors = some f ∧ joined.cells .xmssAuth = some a ∧
    joined.cells .roots = some r ∧ ∀ j, joined.cells (.wotsSigs j) = m.cells j := by
  have seen := WorkerBarrier.read_cells monitor passed
  exact ⟨barrier_run base monitor fc ac rc, wots_heap_run _ run zero fresh,
    congrArg WorkerBarrier.Cells.fors seen, congrArg WorkerBarrier.Cells.auth seen,
    congrArg WorkerBarrier.Cells.roots seen, fun _ => rfl⟩

end ParallelWorkerHeap
