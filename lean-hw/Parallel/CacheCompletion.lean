import Parallel.Cached
import Mathlib.Data.List.Perm.Basic

namespace ParallelCached
variable {S V : Type} [DecidableEq S]

/-- Include the publication history so a pending slot cannot also have been consumed. -/
private theorem history {n t : Nat} {writes : Nat → List (S × V)} {pending cells}
    (run : Run n writes t pending cells) :
    ∃ published : List (S × V),
      (pending ++ published).Perm ((List.range t).flatMap writes) ∧
      (∀ s v, cells s=some v ↔ (s,v)∈published) := by
  induction run with
  | start => exact ⟨[],by simp,by simp⟩
  | @claim ticket todo cells _ _ ih =>
    obtain ⟨sent,perm,record⟩ := ih
    refine ⟨sent,?_,record⟩
    rw [List.range_succ,List.flatMap_append]
    simpa [List.append_assoc] using (perm.append_left (writes ticket)).trans (List.perm_append_comm)
  | @publish ticket before after cells s v _ empty ih =>
    obtain ⟨sent,perm,record⟩ := ih
    refine ⟨(s,v)::sent,?_,?_⟩
    · apply List.Perm.trans _ perm
      simp only [List.append_assoc,List.cons_append]
      apply List.Perm.append_left
      exact List.perm_middle
    · intro slot value
      by_cases h : slot=s
      · subst slot
        simp [empty,← record,eq_comm]
      · simp [h,record]

/-- A plan with exactly one writer per slot cannot encounter an occupied slot during draining. -/
theorem pending_empty {n t : Nat} {writes : Nat → List (S × V)} {pending cells}
    (run : Run n writes t pending cells) (plan : (((List.range n).flatMap writes).map Prod.fst).Nodup)
    (tLe : t≤n) {s : S} {v : V} (waiting : (s,v)∈pending) : cells s=none := by
  obtain ⟨sent,perm,record⟩ := history run
  have earlier : (((List.range t).flatMap writes).map Prod.fst).Nodup := by
    have eq : n=t+(n-t) := by omega
    rw [eq,List.range_add,List.flatMap_append,List.map_append] at plan
    exact (List.nodup_append.mp plan).1
  have all := (perm.map Prod.fst).nodup_iff.mpr earlier
  rw [List.map_append] at all
  have disjoint := (List.nodup_append.mp all).2.2
  cases entry : cells s with
  | none => rfl
  | some val =>
    have present := (record s val).mp entry
    exact False.elim (disjoint s (List.mem_map_of_mem (f:=Prod.fst) waiting) s (List.mem_map_of_mem (f:=Prod.fst) present) rfl)

/-- A finite continuation of the current ticket and cell state to a fully drained join. -/
inductive Completion (n : Nat) (writes : Nat → List (S × V)) :
    Nat → List (S × V) → (S → Option V) → (S → Option V) → Prop where
  | done {cells} : Completion n writes n [] cells cells
  | claim {t pending cells out} : t<n → Completion n writes (t+1) (writes t ++ pending) cells out →
      Completion n writes t pending cells out
  | publish {t before after cells s v out} : cells s=none →
      Completion n writes t (before++after) (fun k => if k=s then some v else cells k) out →
      Completion n writes t (before++(s,v)::after) cells out

theorem Completion.joined {n t : Nat} {writes : Nat → List (S × V)} {pending cells out}
    (steps : Completion n writes t pending cells out) (run : Run n writes t pending cells) :
    Run n writes n [] out := by
  induction steps with
  | done => exact run
  | claim smaller _ ih => exact ih (.claim run smaller)
  | publish empty _ ih => exact ih (.publish run empty)

private theorem drain {n : Nat} {writes : Nat → List (S × V)}
    (plan : (((List.range n).flatMap writes).map Prod.fst).Nodup) {pending cells}
    (run : Run n writes n pending cells) : ∃ out, Completion n writes n pending cells out := by
  induction pending generalizing cells with
  | nil => exact ⟨cells,.done⟩
  | cons entry rest ih =>
    obtain ⟨s,v⟩ := entry
    have empty := pending_empty run plan (Nat.le_refl _) List.mem_cons_self
    obtain ⟨out,steps⟩ := ih (Run.publish (before:=[]) run empty)
    exact ⟨out,.publish (before:=[]) empty steps⟩

/-- No normally executing pool can be stuck on a duplicate OnceLock write when the
plan assigns each slot once. From every partial history there is a finite continuation. -/
theorem can_join {n t : Nat} {writes : Nat → List (S × V)} {pending cells}
    (run : Run n writes t pending cells) (plan : (((List.range n).flatMap writes).map Prod.fst).Nodup)
    (tLe : t≤n) : ∃ out, Completion n writes t pending cells out := by
  by_cases more : t<n
  · obtain ⟨out,steps⟩ := can_join (Run.claim run more) plan (by omega)
    exact ⟨out,.claim more steps⟩
  · have eq : t=n := by omega
    subst t
    exact drain plan run
termination_by n-t

def planWrites (jobs : List (List Nat)) (compute : Nat → Nat → V) (ticket : Nat) :=
  (jobs[ticket]?.getD []).map (fun slot => (slot,compute ticket slot))

private theorem planMap (jobs : List (List Nat)) (compute : Nat → Nat → V) :
    (((List.range jobs.length).flatMap (planWrites jobs compute)).map Prod.fst) = jobs.flatten := by
  rw [List.map_flatMap,List.flatMap_def]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [planWrites,List.map_map,Function.comp_def,List.getElem?_eq_getElem hj]

/-- Source-projected, sorted job plans certify both finite completion from any prefix and
coverage of every output cell. Hash results are arbitrary ticket- and slot-dependent values. -/
theorem plan_completion (jobs : List (List Nat)) (total : Nat) (compute : Nat → Nat → V)
    (ownership : jobs.flatten.Perm (List.range total)) {t pending cells}
    (run : Run jobs.length (planWrites jobs compute) t pending cells) (issued : t≤jobs.length) :
    ∃ out, Completion jobs.length (planWrites jobs compute) t pending cells out ∧
      ∀ s, (∃ v, out s=some v) ↔ s<total := by
  have unique : (((List.range jobs.length).flatMap (planWrites jobs compute)).map Prod.fst).Nodup := by
    rw [planMap];exact ownership.nodup_iff.mpr List.nodup_range
  obtain ⟨out,steps⟩ := can_join run unique issued
  refine ⟨out,steps,?_⟩
  intro s
  rw [← List.mem_range,← ownership.mem_iff,← planMap jobs compute]
  simp only [List.mem_map,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨v,entry⟩
    obtain ⟨t,lt,has⟩ := (joined (steps.joined run) s v).mp entry
    exact ⟨(s,v),⟨t,lt,has⟩,rfl⟩
  · rintro ⟨⟨_,v⟩,⟨t,lt,has⟩,rfl⟩
    exact ⟨v,(joined (steps.joined run) _ _).mpr ⟨t,lt,has⟩⟩

end ParallelCached
