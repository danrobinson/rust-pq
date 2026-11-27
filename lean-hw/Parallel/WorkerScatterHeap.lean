import Parallel.WorkerScatter
import Parallel.WorkerRuntime

open Aeneas Aeneas.Std ParallelWorkerInterleave ParallelWorkerHeap ParallelWorkerRuntime
namespace ParallelWorkerScatter

inductive ForsTable | direct | split

def ForsTable.cells (site : ForsTable) (N count : Usize) :
    alloc.vec.Vec (ParallelWorkerCells.Ref (Shared N) (Array U8 N)) :=
  match site with
  | .direct => table N .forsDirect _ (fun _ => rfl) count
  | .split => table N .forsSplit _ (fun _ => rfl) count

theorem ForsTable.length (site : ForsTable) (N count : Usize) :
    (site.cells N count).length = count.val := by
  cases site <;> exact table_length _ _ _ _ _


private theorem atKey (N count : Usize) (key : Nat → Key) (T : Type) (ty : ∀ i, Payload N (key i) = T)
    (i : Nat) (hi : i < (table N key T ty count).length) :
    (table N key T ty count).val[i] = ty i ▸ slot N (key i) := by
  have bound : i < count.val := (table_length N key T ty count) ▸ hi
  have eq := index_table N key T ty count i bound
  rw [List.getElem?_eq_getElem hi] at eq
  exact Option.some.inj eq

theorem ForsTable.read_fresh (site : ForsTable) (N count : Usize) (i : Nat)
    (bound : i < (site.cells N count).length) :
    ((site.cells N count).val[i]).read (fresh N) = none := by
  cases site with
  | direct => simp only [ForsTable.cells] at *; erw [atKey N count .forsDirect _ (fun _ => rfl) i bound]; rfl
  | split => simp only [ForsTable.cells] at *; erw [atKey N count .forsSplit _ (fun _ => rfl) i bound]; rfl

theorem ForsTable.disjoint (site : ForsTable) (N count : Usize) (i j : Nat)
    (bi : i < (site.cells N count).length) (bj : j < (site.cells N count).length)
    (apart : i ≠ j) (v : Array U8 N) (h : Shared N) :
    ((site.cells N count).val[j]).read (((site.cells N count).val[i]).write v h) =
    ((site.cells N count).val[j]).read h := by
  cases site with
  | direct =>
    simp only [ForsTable.cells] at *
    erw [atKey N count .forsDirect _ (fun _ => rfl) i bi,
      atKey N count .forsDirect _ (fun _ => rfl) j bj]
    exact frame h.toHeap (.forsDirect j) (.forsDirect i) (by simp [apart]) v
  | split =>
    simp only [ForsTable.cells] at *
    erw [atKey N count .forsSplit _ (fun _ => rfl) i bi,
      atKey N count .forsSplit _ (fun _ => rfl) j bj]
    exact frame h.toHeap (.forsSplit j) (.forsSplit i) (by simp [apart]) v

/-- The actual invocation-local FORS allocations admit a complete lane
schedule from the fresh signer heap for every in-bounds injective lane layout. -/
theorem serial_fors {A : Type} (site : ForsTable) (N count : Usize)
    (values : List (Array U8 N)) (idx : Nat → Nat) (limit : Nat)
    (width : limit ≤ values.length) (fits : ∀ i < limit, idx i < count.val)
    (unique : ∀ i j, i < j → j < limit → idx i ≠ idx j)
    (peers : List (Program (Shared N) A)) :
    ∃ dest, Scatter limit (storeAt (site.cells N count) values idx)
      0 (fresh N) peers dest peers := by
  apply serial _ _ _ _ width (fun i hi => site.length N count ▸ fits i hi)
  · intro i hi j hj less v h
    apply site.disjoint
    exact unique i j less hj
  · intro j _ hj
    apply site.read_fresh

end ParallelWorkerScatter
