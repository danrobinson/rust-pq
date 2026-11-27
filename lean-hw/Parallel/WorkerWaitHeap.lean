import Parallel.WorkerBarrierMir
import Parallel.WorkerHeapBarrier
import Parallel.WorkerRuntime

namespace ParallelWorkerHeap
open Aeneas Aeneas.Std Result slhdsa WorkerBarrierMir

/-- A successful return in the production wait CFG licenses use of the three
typed reducer cells by the subsequent WOTS workers on this same heap. -/
theorem wait_to_wots (base : Heap N) {f a r} {h : Monitor N} {g decode facts pc seen}
    (cert : Certified g decode facts) (exec : Interleaved f a r g decode h pc seen)
    (valid : pc < g.length) (ok : decode g[pc].ops = .accept)
    (fc : base.cells .sigFors = none) (ac : base.cells .xmssAuth = none)
    (rc : base.cells .roots = none) (zero : base.counts .phase2Next = 0)
    (fresh : ∀ j, base.cells (.wotsSigs j) = none) {jobs workers m log}
    (run : WorkerPayload.Execution jobs workers m log) :
    let joined := wotsHeap (barrierHeap base h) m
    Relation.ReflTransGen BarrierAction base (barrierHeap base h) ∧
    Relation.ReflTransGen WotsAction (barrierHeap base h) joined ∧
    joined.cells .sigFors = some f ∧ joined.cells .xmssAuth = some a ∧
    joined.cells .roots = some r ∧ ∀ j, joined.cells (.wotsSigs j) = m.cells j := by
  have visible := accepts_installed cert exec valid ok
  exact ⟨barrier_run base exec.projects.1 fc ac rc, wots_heap_run _ run zero fresh,
    congrArg WorkerBarrier.Cells.fors visible, congrArg WorkerBarrier.Cells.auth visible,
    congrArg WorkerBarrier.Cells.roots visible, fun _ => rfl⟩

open Aeneas.Data.Coinductive ParallelWorkerInterleave ParallelWorkerRuntime

private theorem wait_unroll {N : Usize} :
    (waitReady : Program (Shared N) Bool) =
    ITree.vis (E := effects (Shared N)) (.atomic id)
      (fun s => if s.ready then .ret true else waitReady) := by
  conv => lhs; unfold waitReady; rw [ITree.iter.eq_1]
  simp only [poll,Bind.bind,itree_vis_bind,itree_ret_bind]
  congr 1
  funext s
  cases ready : s.ready <;> simp [Pure.pure,Bind.bind,poll,waitReady]

/-- A certified normal return in the concrete wait corresponds to an enabled
poll-to-continuation step in the effectful extracted worker, in any scheduler
context. Both the readiness bit and installed tables come from the same monitor. -/
theorem wait_runtime_step (base : Heap N) {f a r} {h : Monitor N} {g decode facts pc seen}
    (cert : Certified g decode facts) (exec : Interleaved f a r g decode h pc seen)
    (valid : pc < g.length) (ok : decode g[pc].ops = .accept)
    (k : Bool → Program (Shared N) B) (l rworkers : List (Program (Shared N) B)) :
    let runtime : Shared N := ⟨barrierHeap base h, h.writer.released⟩
    ParallelWorkerInterleave.Step runtime (l ++ (waitReady >>= k) :: rworkers)
      runtime (l ++ k true :: rworkers) ∧
    runtime.cells .sigFors = some f ∧ runtime.cells .xmssAuth = some a ∧ runtime.cells .roots = some r := by
  obtain ⟨_,trace,observed⟩ := exec.projects
  have ready := observed (accepts_after_ready cert trace valid ok)
  have installed := accepts_installed cert exec valid ok
  refine ⟨?_,congrArg WorkerBarrier.Cells.fors installed,
    congrArg WorkerBarrier.Cells.auth installed,congrArg WorkerBarrier.Cells.roots installed⟩
  let runtime : Shared N := ⟨barrierHeap base h, h.writer.released⟩
  rw [wait_unroll,vis_bind]
  have step := ParallelWorkerInterleave.Step.atomic runtime l rworkers id
    (fun s : Shared N => (if s.ready then (ITree.ret true : Program (Shared N) Bool) else waitReady) >>= k)
  simpa [runtime,ready,Bind.bind] using step

/-- The sender's release changes exactly the readiness field of the
interpreter's shared heap; the three reducer cells already agree. -/
theorem publish_runtime_step (base : Heap N) (h : Monitor N)
    (locked : h.writer = .locked) (k : Unit → Program (Shared N) B) (l r : List (Program (Shared N) B)) :
    let before : Shared N := ⟨barrierHeap base h, h.writer.released⟩
    let after := {h with writer := .ready}
    ParallelWorkerInterleave.Step before (l ++ (publish >>= k) :: r)
      (⟨barrierHeap base after, after.writer.released⟩ : Shared N) (l ++ k () :: r) ∧
    before.ready = false := by
  refine ⟨publish_step _ _ _ _, ?_⟩
  change h.writer.released = false
  rw [locked]
  rfl

end ParallelWorkerHeap
