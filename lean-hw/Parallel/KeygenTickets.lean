import Parallel.CacheTickets
import Parallel.SplitTree

namespace ParallelKeygen
open Spec ParallelCached ParallelCached.Tickets

def subHeight (x86 : Bool) (hp : Nat) :=
  if hp ≥ (if x86 then 8 else 9) then 3 else if hp ≥ 6 then 2 else 0

def count (x86 : Bool) (hp : Nat) := 2^(hp-subHeight x86 hp)

theorem geometry (x86 : Bool) (hp : Nat) (supported : hp≤9) :
    subHeight x86 hp ≤ hp ∧ count x86 hp≤512 ∧
    ∀ i<count x86 hp, (i+1)*2^subHeight x86 hp≤2^hp := by
  have sub : subHeight x86 hp≤hp := by
    unfold subHeight; cases x86 <;> simp <;> split <;> (try split) <;> omega
  have scale : count x86 hp * 2^subHeight x86 hp = 2^hp := by
    rw [count,←Nat.pow_add,Nat.sub_add_cancel sub]
  refine ⟨sub, Nat.pow_le_pow_right (by decide) (by omega : hp-subHeight x86 hp≤9), ?_⟩
  intro i hi
  rw [←scale]
  exact Nat.mul_le_mul_right _ hi

def jobs (n : Nat) (compute : Nat → Bytes) : List (List (Nat × Bytes)) :=
  (List.range n).map fun i => [(i,compute i)]

private theorem canonical (n i : Nat) (le : i≤n) :
    ParallelSigning.Trace n i [] (List.range i).reverse := by
  induction i with
  | zero => exact .start
  | succ i ih =>
    simpa [List.range_succ] using
      (ParallelSigning.Trace.publish (ParallelSigning.Trace.claim (ih (by omega)) (by omega)) (List.Perm.refl [i]))

def result (p : Params) (pk : Bytes) (a : Adrs) (sub : Nat) (st : State Nat Bytes) :=
  ParallelSplitTree.merge (fun h i l r => H p pk {(a.setTypeAndClear TREE) with word2:=h,word3:=i} (l++r))
    0 sub (p.hp-sub) (fun i => (st.cells i).getD [])

/-- The cells read by reduce_tree are the cells published by successful fetch_add tickets. -/
theorem joined_root (p : Params) (sk pk : Bytes) (a : Adrs) (sub workers : Nat)
    (within : sub≤p.hp) (positive : 0<workers) (compute : Nat → Bytes)
    (correct : ∀ i<2^(p.hp-sub), compute i=xmssNode p sk i sub pk a)
    {st} (run : Reach (jobs (2^(p.hp-sub)) compute) workers st)
    (stopped : ¬∃ next, Step (jobs (2^(p.hp-sub)) compute) st next) :
    result p pk a sub st = xmssNode p sk 0 p.hp pk a := by
  let n := 2^(p.hp-sub)
  have keys (l : List Nat) : ((l.map fun i => [(i,compute i)]).flatten.map Prod.fst)=l := by
    induction l with
    | nil => rfl
    | cons i rest ih => simpa using congrArg (i::·) ih
  have own : ((jobs n compute).flatten.map Prod.fst).Nodup := by rw [jobs, keys]; exact List.nodup_range
  have complete := (maximal_join run positive own stopped).2.2
  have cell (i : Nat) : st.cells i = ParallelSigning.fill (fun j => xmssNode p sk j sub pk a) (List.range n).reverse i := by
    rw [ParallelSigning.fill_lookup]
    by_cases hi : i<n
    · simp only [List.mem_reverse,List.mem_range,hi,ite_true]
      rw [←correct i hi]
      apply (joined complete _ _).mpr
      refine ⟨i,by simpa [jobs] using hi,?_⟩
      simp [writes,jobs,List.getElem?_map,List.getElem?_range,hi,n]
    · simp only [List.mem_reverse,List.mem_range,hi,ite_false]
      cases eq : st.cells i with
      | none => rfl
      | some v =>
        obtain ⟨j,hj,pair⟩ := (joined complete _ _).mp eq
        change j<(jobs n compute).length at hj
        simp [jobs] at hj
        change (i,v)∈writes (jobs n compute) j at pair
        simp [writes,jobs,List.getElem?_map,List.getElem?_range,hj] at pair
        omega
  unfold result
  simp only [cell]
  exact ParallelSplitTree.keygenRoot p sk pk a sub within
    (ParallelSigning.Trace.stop (canonical n n (by omega)) (by omega)) (by omega)

noncomputable def finished (n workers : Nat) (compute : Nat → Bytes) :
    {st : State Nat Bytes // Reach (jobs n compute) workers st ∧ ¬∃ next, Step (jobs n compute) st next} :=
  let h := maximal_extension (Reach.start (jobs:=jobs n compute) (workerCount:=workers))
  ⟨h.choose, h.choose_spec.2⟩

end ParallelKeygen
