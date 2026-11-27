import Parallel.WorkerCells

namespace ParallelWorkerHeap
open Aeneas Aeneas.Std

/-- Addresses are scoped to one invocation of the signer. A vector element
keeps both its allocation site and its index. -/
inductive Key where
  | xmssSlots (index : Nat)
  | leafPks (index : Nat)
  | forsDirect (index : Nat)
  | forsSplit (index : Nat)
  | wotsSigs (index : Nat)
  | sigFors | xmssAuth | roots
  deriving DecidableEq

inductive Counter where
  | phase1Next | phase1Done | phase2Next
  deriving DecidableEq

def Payload (N : Usize) : Key → Type
  | .xmssSlots _ | .leafPks _ | .forsDirect _ | .forsSplit _ => Array U8 N
  | .wotsSigs _ | .sigFors => alloc.vec.Vec U8
  | .xmssAuth | .roots => alloc.vec.Vec (Array U8 N)

@[ext] structure Heap (N : Usize) where
  counts : Counter → Nat
  cells : (k : Key) → Option (Payload N k)

def empty (N : Usize) : Heap N := ⟨fun _ => 0, fun _ => none⟩

def write (h : Heap N) (k : Key) (v : Payload N k) : Heap N :=
  {h with cells := fun j => if eq : k = j then some (eq ▸ v) else h.cells j}

def ref (N : Usize) (k : Key) : ParallelWorkerCells.Ref (Heap N) (Payload N k) :=
  ⟨fun h => h.cells k, fun v h => write h k v⟩

theorem read_after_write (h : Heap N) (k : Key) (v : Payload N k) :
    (write h k v).cells k = some v := by simp [write]

theorem frame (h : Heap N) (j k : Key) (different : k ≠ j) (v : Payload N k) :
    (write h k v).cells j = h.cells j := by simp [write, different]

/-- Linearization of an atomic increment when the Rust counter has capacity. -/
def fetch (c : Counter) (h : Heap N) : Nat × Heap N :=
  (h.counts c, {h with counts := fun j => if j = c then h.counts c + 1 else h.counts j})

theorem fetch_frame (c : Counter) (h : Heap N) :
    (fetch c h).1 = h.counts c ∧ (fetch c h).2.counts c = h.counts c + 1 ∧
    (∀ j, j ≠ c → (fetch c h).2.counts j = h.counts j) ∧
    (fetch c h).2.cells = h.cells := by
  refine ⟨rfl, by simp [fetch], ?_, rfl⟩
  intro j different
  simp [fetch, different]

/-- Two callers may interleave fetches on different counters without affecting
either returned ticket. Two fetches on the same counter yield successive tickets. -/
theorem successive_fetch (c d : Counter) (h : Heap N) :
    (fetch d (fetch c h).2).1 = if d = c then (fetch c h).1 + 1 else (fetch d h).1 := rfl

end ParallelWorkerHeap
