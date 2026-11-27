import Parallel.PoolVisibleLease
import Parallel.WorkerInterleave

namespace ParallelWorkerPool
open ParallelPool.Borrow ParallelPool.Lease
open ParallelWorkerInterleave

/-- Invoke a recovered callback only at its captured allocation, generation,
offset and monomorphized type. A stale job or a cleared cell fails resolution. -/
def resolve (expected : Object) (callback : ParallelWorkerInterleave.Program H A) :
    Option Value → Option (ParallelWorkerInterleave.Program H A)
  | some (.called actual) => if actual = expected then some callback else none
  | _ => none

/-- The dispatcher itself calls f directly. Each helper obtains its copy via
the published job pointer, trampoline and closure read of this epoch. -/
def participants (object : Nat → Object) (epoch helpers : Nat)
    (callback : ParallelWorkerInterleave.Program H A) (source : Fin helpers → Option Write) :
    Option (List (ParallelWorkerInterleave.Program H A)) := do
  let workers ← (List.finRange helpers).mapM (fun w =>
    resolve (object epoch) callback (fromCell production object (source w)))
  return callback :: workers

private theorem repeated {α β : Type} (items : List α) (f : α → Option β) (value : β)
    (same : ∀ x ∈ items, f x = some value) :
    items.mapM f = some (List.replicate items.length value) := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, same x (by simp), ih (by intro j member; exact same j (by simp [member]))]
    rfl

theorem exact_callbacks {H A} (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (object : Nat → Object) (e : Nat) (callback : ParallelWorkerInterleave.Program H A)
    (source : Fin (epochs e).workers → Option Write)
    (visible : ∀ w : Fin (epochs e).workers, Visible epochs (.copyJob e w) (source w)) :
    participants object e (epochs e).workers callback source =
      some (List.replicate ((epochs e).workers + 1) callback) := by
  unfold participants
  rw [repeated _ _ callback]
  · simp [List.replicate_succ]
  · intro w _
    have installed := (dispatched_closure epochs co object e w w.isLt (source w) (visible w) 0).1
    rw [installed]
    simp [resolve]

/-- An interleaving starts with the exact caller and helper callback objects
selected by the pool, and all helper uses precede the end of the Rust borrow. -/
theorem dispatched_steps {H A} (epochs : (e : Nat) → Epoch e) (co : Coherent epochs)
    (object : Nat → Object) (e : Nat) (callback : ParallelWorkerInterleave.Program H A)
    (source : Fin (epochs e).workers → Option Write)
    (visible : ∀ w : Fin (epochs e).workers, Visible epochs (.copyJob e w) (source w))
    (h final : H) (out : List (ParallelWorkerInterleave.Program H A)) :
    ((∃ start, participants object e (epochs e).workers callback source = some start ∧
        Steps h start final out) ↔ Steps h (List.replicate ((epochs e).workers + 1) callback) final out) ∧
    ∀ w : Fin (epochs e).workers, HB epochs (.useClosure e w) (.endBorrow e) := by
  rw [exact_callbacks epochs co object e callback source visible]
  refine ⟨by simp,?_⟩
  intro w
  exact (dispatched_closure epochs co object e w w.isLt (source w) (visible w) 0).2.1

/-- The zero-helper and busy paths both synchronously invoke the caller. -/
theorem caller_only (object : Nat → Object) (e : Nat) (callback : ParallelWorkerInterleave.Program H A)
    (source : Fin 0 → Option Write) : participants object e 0 callback source = some [callback] := rfl

end ParallelWorkerPool
