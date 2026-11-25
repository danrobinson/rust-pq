import Parallel.ForsSplitCells
import Parallel.PhaseTwoObserved
open Aeneas Aeneas.Std Result
namespace slhdsa.RawFors
open WidthEight.Ticket ParallelRawChunks

/-- Each completed ticket first writes its indexed slot. Once the queue has
joined, read the results in physical order and require every slot to be full. -/
def joinedJobs {α : Type} (n : Nat) (f : Nat→Result α) (s : Schedule n) : Result (List α) := do
  let cells ← writeRows n f s.completed
  collect (fun cell => core.option.Option.expect cell (toStr "split job completed")) cells

private theorem read_all {α : Type} (xs : List α) :
    collect (fun cell => core.option.Option.expect cell (toStr "split job completed")) (xs.map some)=ok xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,collect,core.option.Option.expect,Result.ofOption,bind_ok,bind_tc_eq] at ih ⊢;rw [ih,bind_ok]

theorem joinedJobs_eq {α : Type} [Inhabited α] (n : Nat) (f : Nat→Result α) (s : Schedule n)
    (total : ∀ i<n, ∃ v, f i=ok v) : joinedJobs n f s=collect f (List.range n) := by
  obtain ⟨expected,call,len,each⟩ := collect_ok f (List.range n) (fun i h => total i (List.mem_range.mp h))
  simp only [List.length_range] at len each
  have run (i : Nat) (hi : i<n) : f i=ok expected[i]! := by
    have value := each i hi
    rwa [getElem!_pos (List.range n) i (by simpa using hi),List.getElem_range] at value
  have trace := (s.trace.joined s.drained).exactly_once
  obtain ⟨cells,write,size,written⟩ := writes n f (fun i row => row=expected[i]!)
    (fun i hi => ⟨_,run i hi,rfl⟩) s.completed trace.1 (fun i hi => (trace.2 i).mp hi)
  have physical : cells=expected.map some := by
    apply List.ext_getElem (by simp only [List.length_map,size,len])
    intro i hc he
    have hi : i<n := size ▸ hc
    obtain ⟨v,get,val⟩ := (ite_eq_left ((trace.2 i).mpr hi)) ▸ written i hi
    rw [List.getElem?_eq_getElem hc] at get
    rw [List.getElem_map,Option.some.inj get,val,getElem!_pos _ _ (by omega)]
  unfold joinedJobs
  rw [write,bind_ok,physical,read_all,call]

noncomputable def scheduledScalarMerge {N} (host : ParallelScalarFors.Platform) (d : Data N) (sat : Bool)
    (t j sub : U32) (s : Schedule (2^(j.val-sub.val))) : Result (ScalarMerge N) := do
  let count := 2^(j.val-sub.val)
  let jobs ← joinedJobs count (fun i => scalarJob host d sat t j sub (indexSize i)) s
  ok ⟨t,j,sub,0#usize,alloc.vec.Vec.new _,physical count (fun i => jobs[i]!)⟩

theorem scheduledScalarMerge_eq {N} (host : ParallelScalarFors.Platform) (d : Data N) (v : Valid d) (sat : Bool)
    (t j sub : U32) (tree : t.val<d.p.k.val) (field : j.val<d.p.a.val) (lower : sub.val<j.val)
    (s : Schedule (2^(j.val-sub.val))) :
    scheduledScalarMerge host d sat t j sub s=buildScalarMerge host d sat t j sub := by
  unfold scheduledScalarMerge buildScalarMerge
  dsimp only
  rw [joinedJobs_eq]
  intro i hi
  obtain ⟨row,call,_⟩ := scalarJob_runs host d v sat t j sub tree field lower i hi
  exact ⟨_,call⟩

noncomputable def scheduledGroupMerge {N} (d : Data N) (first : U16) (active h low : U8) (j sub : U32)
    (s : Schedule (2^(j.val-sub.val))) : Result (GroupMerge N) := do
  let count := 2^(j.val-sub.val)
  let chunks := indexSize count
  let jobs ← joinedJobs count (fun i => groupJob d first active h low chunks (indexWord i)) s
  let cells := physical (active.val*count) (fun i => jobs[i%count]!.val[i/count]!)
  ok ⟨first,active,h,low,j,sub,0#usize,chunks,alloc.vec.Vec.new _,cells⟩

theorem scheduledGroupMerge_eq {N} (d : Data N) (v : Valid d) (first : U16) (active h low : U8) (j sub : U32)
    (field : h.val<d.p.a.val) (lower : low.val<h.val) (hj : j.val=h.val) (hs : sub.val=low.val)
    (on : 0<active.val) (width : active.val≤3) (range : first.val+active.val≤d.choices.length)
    (s : Schedule (2^(j.val-sub.val))) :
    scheduledGroupMerge d first active h low j sub s=buildGroupMerge d first active h low j sub := by
  unfold scheduledGroupMerge buildGroupMerge
  dsimp only
  rw [joinedJobs_eq]
  intro i hi
  obtain ⟨row,call,_⟩ := groupJob_runs d v first active h low j sub field lower hj hs on width range i hi
  exact ⟨_,call⟩
end slhdsa.RawFors
