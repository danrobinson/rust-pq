"""Bind the complete phase-one loop and its concrete direct-FORS plan at reducer entry."""

import re

PREFIX = "shake.slh.parallel.flat_worker_loop"


def phase_one_witness(generated):
    header = generated.split("def " + PREFIX + "\n", 1)[1].split("  (xmss_slots :", 1)[
        0
    ]
    args = " ".join(re.findall(r"\((\w+) :", header))
    if not args.endswith("fors_indices xmss_meta fors_split_meta"):
        raise ValueError("unexpected phase-one input list")
    sizes = "(xmssLen leafLen directLen splitLen : Usize)"
    tables = " ".join(
        f"(table N Key.{key} _ (fun _ => rfl) {length})"
        for key, length in (
            ("xmssSlots", "xmssLen"),
            ("leafPks", "leafLen"),
            ("forsDirect", "directLen"),
            ("forsSplit", "splitLen"),
        )
    )
    cells = "(slot N .sigFors) (slot N .xmssAuth) (slot N .roots)"
    plan = f"phasePlan {args} xmssLen leafLen directLen splitLen"
    worker = f"interpreted.flat_worker_loop concurrentOps (concurrentSync N) {args} {tables} .phase1Next .phase1Done () () () {cells}"
    dispatch = f"interpreted.dispatch concurrentOps fors_stride a fors_addr sk seed layers fors_indices {tables}"
    return f"""
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow Error
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelPhaseOne
noncomputable section
set_option backward.isDefEq.respectTransparency false

def phasePlan
{header}  {sizes} : Plan N shake.slh.parallel.WorkItem where
  jobs := jobs
  total := total_phase1
  dispatch := {dispatch}
  reduce := interpreted.reduce concurrentOps d hp leaf_pk_count fors_stride fors_addr p md seed layers
    xmss_meta fors_split_meta {tables} {cells}

theorem phase_worker_eq
{header}  {sizes} :
    {worker} = ({plan}).worker := by
  unfold interpreted.flat_worker_loop Plan.worker
  change runLoop (fun () => _) () = runLoop (fun _ : Unit => _) ()
  congr 1
  funext u
  cases u
  unfold interpreted.flat_worker_loop.body Plan.body
  dsimp only [concurrentSync,phasePlan]
  congr 1
  funext ticket
  have lookup : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice _) jobs.deref ticket =
      ok (jobs.val[ticket.val]?) := by
    simp [core.slice.Slice.get,core.slice.index.SliceIndexUsizeSlice,
      core.slice.index.Usize.get,Slice.getElem?_Usize_eq,alloc.vec.Vec.deref,alloc.vec.Vec.val]
  simp only [lookup,lifted_ok,pure_bind]
  cases jobs.val[ticket.val]? with
  | none => rfl
  | some item => rfl

/-- A nonempty constant plan with a native direct FORS node at each job
position reaches the actual reducer with all those values already stored. -/
theorem phase_direct_reducer
{header}  {sizes} (values : Nat → Array U8 N)
    (nonempty : 0 < total_phase1.val) (count : jobs.val.length = total_phase1.val)
    (space : total_phase1.val ≤ directLen.val)
    (inputs : ∀ i (live : i < total_phase1.val),
      ∃ idx height dest, (jobs.val[i]'(count ▸ live)).kind = .ForsNodeDirect idx height dest ∧
        dest.val = i ∧ shake.fors.fors_node sk idx height seed fors_addr = ok (values i))
    (peers : List (Program (Shared N) Unit)) :
    ∃ h, Steps (fresh N) ({worker} :: peers) h (({plan}).reducing :: peers) ∧
      h.counts .phase1Done = total_phase1.val ∧
      ∀ i, h.cells (.forsDirect i) = if i < total_phase1.val then some (values i) else none := by
  let c := {plan}
  have job (i : Nat) (live : i < total_phase1.val) (s : Shared N)
      (free : s.cells (.forsDirect i) = none) :
      Step s [c.dispatch (jobs.val[i]'(count ▸ live))]
        ((slot N (.forsDirect i)).write (values i) s) [pure ()] := by
    obtain ⟨idx,height,dest,kind,position,hashed⟩ := inputs i live
    have index : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _)
        (table N .forsDirect _ (fun _ => rfl) directLen) dest = ok (slot N (.forsDirect i)) := by
      erw [alloc.vec.Vec.index_slice_index]
      obtain ⟨v,read,rfl⟩ := spec_imp_exists
        (alloc.vec.Vec.index_usize_spec (table N .forsDirect _ (fun _ => rfl) directLen) dest
          (by change dest.val < (table N .forsDirect _ (fun _ => rfl) directLen).val.length;
              rw [table_length,position]; omega))
      have atDest := index_table N .forsDirect _ (fun _ => rfl) directLen dest.val (by omega)
      have inTable : dest.val < (table N .forsDirect _ (fun _ => rfl) directLen).val.length := by
        rw [table_length,position]; omega
      rw [List.getElem?_eq_getElem inTable] at atDest
      rw [read,Option.some.inj atDest,position]
    exact direct_step fors_stride a idx height dest fors_addr sk seed (values i) layers fors_indices
      {tables} (slot N (.forsDirect i)) s [] [] _ kind hashed index free
  obtain ⟨dest,sched,doneCount,contents⟩ :=
    direct_plan c values count job 0 (fresh N) peers nonempty rfl rfl (fun j => by
      simp [fresh,empty])
  rw [phase_worker_eq]
  exact ⟨dest,sched.executes,doneCount,contents⟩

end
end slhdsa.WorkerEffects
"""
