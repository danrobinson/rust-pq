import Parallel.WorkerHeap
import Parallel.WorkerInterleave

namespace ParallelWorkerRuntime
open Aeneas Aeneas.Std Aeneas.Data.Coinductive ParallelWorkerInterleave ParallelWorkerHeap

/-- Invocation-local storage of the normal worker, including the published phase flag. -/
structure Shared (N : Usize) extends Heap N where
  ready : Bool

def fresh (N : Usize) : Shared N := ⟨empty N,false⟩

def slot (N : Usize) (key : Key) : ParallelWorkerCells.Ref (Shared N) (Payload N key) :=
  ⟨fun s => s.cells key, fun v s => {s with toHeap := write s.toHeap key v}⟩

def table (N : Usize) (key : Nat → Key) (T : Type) (ty : ∀ i, Payload N (key i) = T)
    (len : Usize) : alloc.vec.Vec (ParallelWorkerCells.Ref (Shared N) T) :=
  alloc.vec.Vec.from ((List.range len.val).map fun i => ty i ▸ slot N (key i)) (by simp; scalar_tac)

theorem index_table (N : Usize) (key : Nat → Key) (T : Type) (ty : ∀ i, Payload N (key i) = T)
    (len : Usize) (i : Nat) (bound : i < len.val) :
    (table N key T ty len).val[i]? = some (ty i ▸ slot N (key i)) := by
  simp [table,alloc.vec.Vec.from_val,List.getElem?_map,List.getElem?_range bound]

theorem table_length (N : Usize) (key : Nat → Key) (T : Type) (ty : ∀ i, Payload N (key i) = T)
    (len : Usize) : (table N key T ty len).val.length = len.val := by
  simp [table, alloc.vec.Vec.from_val]

theorem wots_lookup (N : Usize) (len j : Usize) :
    core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice _)
      (table N Key.wotsSigs _ (fun _ => rfl) len).deref j =
    Result.ok (if j.val < len.val then some (slot N (.wotsSigs j.val)) else none) := by
  simp only [core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    Slice.getElem?_Usize_eq, alloc.vec.Vec.deref, Slice.from_val]
  split
  · exact congrArg Result.ok (index_table N Key.wotsSigs _ (fun _ => rfl) len j.val ‹_›)
  · apply congrArg Result.ok
    apply List.getElem?_eq_none
    refine (table_length N Key.wotsSigs (alloc.vec.Vec U8) (fun _ => rfl) len).le.trans ?_
    omega

def oldTicket (s : Shared N) (c : Counter) : Usize :=
  ⟨BitVec.ofNat _ (s.counts c)⟩

def increment (s : Shared N) (c : Counter) (n : Usize) : Shared N :=
  {s with counts := fun j => if j=c then (UScalar.wrapping_add (oldTicket s c) n).val else s.counts j}

def rmw (c : Counter) (n : Usize) : Program (Shared N) Usize :=
  .vis (.atomic (fun s => increment s c n)) (fun s => .ret (oldTicket s c))

def publish : Program (Shared N) Unit :=
  .vis (.atomic (fun s => {s with ready := true})) (fun _ => .ret ())

/-- Normal-return wait semantics after abstracting mutex/spurious-wake steps:
a worker may keep polling, and can return successfully only after READY. -/
def poll : Program (Shared N) Bool :=
  .vis (.atomic id) (fun s => .ret s.ready)

def waitReady : Program (Shared N) Bool :=
  ITree.iter (fun () => do
    if ← (poll : Program (Shared N) Bool) then pure (.inr true) else pure (.inl ())) ()

theorem rmw_step (c : Counter) (n : Usize) (h : Shared N) (k : Usize → Program (Shared N) A) (l r) :
    Step h (l ++ (rmw c n >>= k) :: r) (increment h c n) (l ++ k (oldTicket h c) :: r) := by
  unfold rmw
  rw [ParallelWorkerInterleave.atomic_bind]
  exact
    (Step.atomic h l r (fun s => increment s c n) (fun s => k (oldTicket s c)))

theorem publish_step (h : Shared N) (k : Unit → Program (Shared N) A) (l r) :
    Step h (l ++ (publish >>= k) :: r) {h with ready := true} (l ++ k () :: r) := by
  unfold publish
  rw [ParallelWorkerInterleave.atomic_bind]
  exact
    (Step.atomic h l r (fun s => {s with ready := true}) (fun _ => k ()))

/-- A program exposes this update as its next scheduler-visible operation. -/
def Starts {H A} (f : H → H) (prog : Program H A) : Prop :=
  ∃ k, prog = ITree.vis (E := effects H) (.atomic f) k

theorem Starts.bind {f : H → H} {prog : Program H A} (first : Starts f prog)
    (next : A → Program H B) : Starts f (prog >>= next) := by
  obtain ⟨k,rfl⟩ := first
  exact ⟨_,vis_bind _ _ _⟩

theorem Starts.loop {f : H → H} (body : A → Program H (ControlFlow A B)) (x : A)
    (first : Starts f (body x)) : Starts f (runLoop body x) := by
  unfold runLoop
  rw [ITree.iter.eq_1]
  obtain ⟨k,eq⟩ := first
  rw [eq]
  exact ⟨_,(congrArg (fun p => ITree.bind p _) (vis_bind _ _ _)).trans (itree_vis_bind _ _ _)⟩

theorem Starts.step {f : H → H} {prog : Program H A} (first : Starts f prog)
    (h : H) (l r : List (Program H A)) : ∃ after, Step h (l ++ prog :: r) (f h) (l ++ after :: r) := by
  obtain ⟨k,rfl⟩ := first
  exact ⟨k h,Step.atomic h l r f k⟩

end ParallelWorkerRuntime
