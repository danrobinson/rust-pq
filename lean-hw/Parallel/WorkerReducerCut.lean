import Parallel.WorkerReducerPeers

open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive
open ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerCounterSafety
open ParallelWorkerFrozenReads ParallelDispatchWrites ParallelPhaseOne ParallelPhaseOne.Mixed
open ParallelWorkerSplitCut
namespace ParallelReducerPeers

structure Changed (start dest : Shared N) (writes : List (Publication N)) : Prop where
  installed : ∀ w ∈ writes, dest.cells w.key=some w.value
  kept : Extends start dest
  frame : ∀ key, (∀ w∈writes, w.key≠key) → dest.cells key=start.cells key
  count : dest.counts .phase2Next=start.counts .phase2Next

theorem Changed.initial (h : Shared N) : Changed h h [] := ⟨by simp,fun _ _ => id,fun _ _ => rfl,rfl⟩

theorem Changed.peer {start other dest : Shared N} {ws}
    (cells : other.cells=start.cells) (count : other.counts .phase2Next=start.counts .phase2Next)
    (later : Changed other dest ws) : Changed start dest ws := by
  exact ⟨later.installed,fun k v old => later.kept k v (cells ▸ old),
    fun k free => (later.frame k free).trans (congrFun cells k),later.count.trans count⟩

theorem Changed.prepend {h dest : Shared N} (w : Publication N) {ws} (free : h.cells w.key=none)
    (rest : Changed (put w.key w.value h) dest ws) : Changed h dest (w::ws) := by
  refine ⟨?_,fun k v old => rest.kept k v (put_keeps w ⟨k,v⟩ h old),?_,?_⟩
  · intro u member
    rcases List.mem_cons.mp member with rfl|tail
    · exact rest.kept _ _ (by simp [put,slot,free,read_after_write])
    · exact rest.installed u tail
  · intro k separate
    rw [rest.frame k (fun u m => separate u (List.mem_cons_of_mem _ m))]
    have different := separate w List.mem_cons_self
    simp [put,slot,free,ParallelWorkerHeap.frame _ _ _ different]
  · simpa [put,slot,free,write] using rest.count

/-- A cut through a normally joined execution that retains the full state of
the slower peers, the exact untouched cells and both halves of the schedule. -/
theorem segment_cut {N J} {p : Plan N J} (next : Bool → Program (Shared N) Unit)
    {base h final : Shared N} {roles lead tail writes out}
    (cert : Segment base tail lead writes) (ext : Extends base h)
    (valid : Valid p h roles) (history : Steps h (roles.map (Role.code p next lead)) final out)
    (normal : ∀ x∈out,x=pure ()) :
    ∃ mid roles', Valid p mid roles' ∧ Changed h mid writes ∧ roles'.length=roles.length ∧
      Steps h (roles.map (Role.code p next lead)) mid (roles'.map (Role.code p next tail)) ∧
      Steps mid (roles'.map (Role.code p next tail)) final out := by
  let start := (h,roles.map (Role.code p next lead))
  change Relation.ReflTransGen (fun (a b : Shared N × List (Program (Shared N) Unit)) =>
    Step a.1 a.2 b.1 b.2) start (final,out) at history
  generalize source : start=z at history
  suffices result : ∀ roles lead writes, z.2=roles.map (Role.code p next lead) → Segment base tail lead writes →
      Extends base z.1 → Valid p z.1 roles →
      ∃ mid roles', Valid p mid roles' ∧ Changed z.1 mid writes ∧ roles'.length=roles.length ∧
        Steps z.1 z.2 mid (roles'.map (Role.code p next tail)) ∧
        Steps mid (roles'.map (Role.code p next tail)) final out by
    subst z; exact result roles lead writes rfl cert ext valid
  clear source
  induction history using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro roles lead writes shape seg _ ok
    have member : Role.leader ∈ roles := List.count_pos_iff.mp (ok.unique ▸ Nat.zero_lt_one)
    have done := normal _ (shape ▸ List.mem_map_of_mem (f:=Role.code p next lead) member)
    change lead=pure () at done
    cases seg with
    | stop => exact ⟨final,roles,ok,Changed.initial _,rfl,shape ▸ .refl,shape ▸ .refl⟩
    | load | put => exact False.elim (not_vis_ret done.symm)
    | failed => simp only [liftResult,Result.match.fail] at done; exact False.elim (not_vis_ret done.symm)
  | @head a b event tailRun ih =>
    intro roles lead writes shape seg extend ok
    have edge := event
    change Step a.1 a.2 b.1 b.2 at edge
    rw [shape] at edge
    obtain ⟨q,own,whereAt⟩ | ⟨newRoles,whereAt,ok',cells,counter,length⟩ := observe next ok edge
    · cases seg with
      | stop => exact ⟨a.1,roles,ok,Changed.initial _,rfl,shape ▸ .refl,shape ▸ .head event tailRun⟩
      | load k _ more =>
        obtain ⟨state,code⟩ := own.unique_worker (Step.atomic a.1 [] [] id k)
        change b.1=a.1 at state
        rw [code] at whereAt
        obtain ⟨mid,ps,good,changed,len,first,rest⟩ := ih roles _ _ whereAt (more _ extend)
          (state ▸ extend) (state ▸ ok)
        exact ⟨mid,ps,good,state ▸ changed,len,.head event first,rest⟩
      | @put w prog ws more =>
        obtain ⟨state,code⟩ := own.unique_worker (Step.atomic a.1 [] [] _ _)
        have keep : Extends base b.1 := fun key v old => state ▸ put_keeps w ⟨key,v⟩ _ (extend key v old)
        have ok' : Valid p b.1 roles := by
          rw [state]; cases e : a.1.cells w.key <;> simp [put,slot,e] <;> exact ⟨ok.unique,ok.waiting,ok.used,ok.space⟩
        cases value : a.1.cells w.key with
        | none =>
          simp only [value] at code
          obtain ⟨mid,ps,good,changed,len,first,rest⟩ := ih roles _ _ (by simpa [code] using whereAt) more keep ok'
          exact ⟨mid,ps,good,Changed.prepend w value (state ▸ changed),len,.head event first,rest⟩
        | some v =>
          simp only [value] at code
          obtain ⟨mid,ps,good,changed,len,first,rest⟩ :=
            ih roles _ (w::ws) (by simpa [code] using whereAt) (.failed _) keep ok'
          exact ⟨mid,ps,good,by simpa [state,put,slot,value] using changed,len,.head event first,rest⟩
      | failed =>
        obtain ⟨_,_,eq,_,_⟩ := own.single_view
        simp only [liftResult,Result.match.fail] at eq; cases vis_inj_effect eq
    · obtain ⟨mid,ps,good,changed,len,first,rest⟩ := ih newRoles _ _ whereAt seg
        (fun k v seen => cells ▸ extend k v seen) ok'
      exact ⟨mid,ps,good,changed.peer cells counter,len.trans length,.head event first,rest⟩

end ParallelReducerPeers
