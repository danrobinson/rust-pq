import Parallel.RawChunkLayout
import Parallel.PhaseTwoObserved
open Aeneas Aeneas.Std Result
namespace slhdsa.ParallelRawChunks
open WidthEight.Ticket

def fill {α β : Type} [Inhabited α] (compute : α → Result (Option β)) (keys : List α)
    (plan : Schedule keys.length) :=
  writeRows keys.length (fun j => do
    let result ← compute keys[j]!
    match result with
    | some v => ok v
    | none => fail .panic) plan.completed

/-- A linearized set of successful per-slot writes has the same physical rows as
evaluating the producers in slot order, for any normally joined ticket schedule. -/
theorem fill_eq {α β : Type} [Inhabited α] (compute : α → Result (Option β)) (keys : List α)
    (plan : Schedule keys.length) (works : ∀ k∈keys, ∃ v, compute k=ok (some v)) :
    fill compute keys plan=collect compute keys := by
  obtain ⟨expected,run,len,each⟩ := collect_ok compute keys (fun k h =>
    let ⟨v,returned⟩ := works k h
    ⟨some v,returned⟩)
  let f := fun (j : Nat) => do
    let result ← compute keys[j]!
    match result with
    | some v => ok v
    | none => fail .panic
  have total (i : Nat) (hi : i<keys.length) : ∃ row, f i=ok row ∧ expected[i]! = some row := by
    have mem : keys[i]! ∈ keys := by rw [getElem!_pos keys i hi];apply List.getElem_mem
    obtain ⟨v,correct⟩ := works _ mem
    have value := each i hi
    rw [correct] at value
    exact ⟨v,by simp only [f,correct,bind_tc_eq,bind_ok],(Result.ok_injective value).symm⟩
  obtain ⟨unique,covers⟩ := (plan.trace.joined plan.drained).exactly_once
  obtain ⟨out,ret,count,rows⟩ := writes keys.length f (fun j row => expected[j]! = some row)
    total plan.completed unique (fun i h => (covers i).mp h)
  change writeRows keys.length f plan.completed=_
  rw [ret,run]
  congr 1
  apply List.ext_getElem (count.trans len.symm)
  intro i ho he
  have hi := count ▸ ho
  obtain ⟨v,get,eq⟩ := (ite_eq_left ((covers i).mpr hi)) ▸ rows i hi
  rw [List.getElem?_eq_getElem ho] at get
  rw [←getElem!_pos expected i he,eq,Option.some.inj get]

end slhdsa.ParallelRawChunks
