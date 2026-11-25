import Mathlib.Logic.Relation
import Parallel.CacheCompletion

namespace ParallelCached.Tickets
variable {S V : Type} [DecidableEq S]

/-- Each live invocation owns its remaining stores. An empty queue is about to
call fetch_add. A failed get retires exactly that invocation. -/
structure State (S V : Type) where
  issued : Nat
  counter : Nat
  live : List (List (S × V))
  cells : S → Option V

def initial (count : Nat) : State S V := ⟨0,0,List.replicate count [],fun _ => none⟩

inductive Step (jobs : List (List (S × V))) : State S V → State S V → Prop where
  | claim (left right) (i counter cells) (within : i<jobs.length) :
      Step jobs ⟨i,counter,left++[]::right,cells⟩
        ⟨i+1,counter+1,left++jobs[i]::right,cells⟩
  | store (left right tail) (i counter cells s v) (empty : cells s=none) :
      Step jobs ⟨i,counter,left++((s,v)::tail)::right,cells⟩
        ⟨i,counter,left++tail::right,fun k => if k=s then some v else cells k⟩
  | retire (left right) (i counter cells) (all : i=jobs.length) :
      Step jobs ⟨i,counter,left++[]::right,cells⟩ ⟨i,counter+1,left++right,cells⟩

def writes (jobs : List (List (S × V))) (i : Nat) := jobs[i]?.getD []

/-- The number of non-stuttering transitions left counts claims, stores and
terminal fetch_add calls. Stores transferred by a claim move between summands. -/
def fuel (jobs : List (List (S × V))) (st : State S V) :=
  let rest := jobs.drop st.issued
  rest.length + rest.flatten.length + st.live.flatten.length + st.live.length

theorem decreases {jobs : List (List (S × V))} {a b} (step : Step jobs a b) :
    fuel jobs a = fuel jobs b + 1 := by
  cases step with
  | claim left right i counter cells within =>
    have rest : jobs.drop i = jobs[i]::jobs.drop (i+1) := (List.getElem_cons_drop within).symm
    simp only [fuel,rest,List.length_cons,List.flatten_cons,List.length_append,
      List.flatten_append,List.nil_append]
    omega
  | store left right tail i counter cells s v empty =>
    simp [fuel,List.flatten_append,List.flatten_cons]; omega
  | retire left right i counter cells all =>
    simp [fuel,List.flatten_append,List.flatten_cons]; omega

inductive Reach (jobs : List (List (S × V))) (workerCount : Nat) : State S V → Prop where
  | start : Reach jobs workerCount (initial workerCount)
  | next {a b} : Reach jobs workerCount a → Step jobs a b → Reach jobs workerCount b

theorem counter_exact {jobs : List (List (S × V))} {workers st} (run : Reach jobs workers st) :
    st.counter + st.live.length = st.issued + workers ∧ st.issued ≤ jobs.length ∧
    (st.issued < jobs.length → st.counter=st.issued ∧ st.live.length=workers) := by
  induction run with
  | start => simp [initial]
  | next prev step ih =>
    cases step <;> simp_all <;> omega

theorem live_bound {jobs : List (List (S × V))} {workers st} (run : Reach jobs workers st) :
    st.live.length≤workers := by
  induction run with
  | start => simp [initial]
  | next _ step ih => cases step <;> simp_all; omega

/-- The counter matches the actual index used by jobs.get, including its
out-of-range values on exit. The final unsuccessful claims cannot wrap usize
when the plan and the number of participating workers fit this bound. -/
theorem fetch_bound {jobs : List (List (S × V))} {workers st limit}
    (run : Reach jobs workers st) (capacity : jobs.length+workers<limit) :
    st.counter<limit ∧ (st.counter<jobs.length ↔ st.issued<jobs.length) := by
  obtain ⟨balance,bound,early⟩ := counter_exact run
  have liveBound := live_bound run
  constructor
  · omega
  · constructor
    · omega
    · intro h; rw [(early h).1]; exact h


/-- Every active schedule is finite even when workers are selected adversarially. -/
theorem no_infinite {jobs : List (List (S × V))} (schedule : Nat → State S V) :
    ¬ ∀ i, Step jobs (schedule i) (schedule (i+1)) := by
  intro steps
  have consumed (i : Nat) : fuel jobs (schedule i)+i=fuel jobs (schedule 0) := by
    induction i with
    | zero => simp
    | succ i ih => have := decreases (steps i); omega
  have := consumed (fuel jobs (schedule 0)+1)
  omega

/-- Every reachable state has a finite extension ending at a maximal state.
Together with progress this supplies a normally joined witness for any plan
with unique cell ownership and at least one worker. -/
theorem maximal_extension {jobs : List (List (S × V))} {workers st}
    (run : Reach jobs workers st) :
    ∃ final, Relation.ReflTransGen (Step jobs) st final ∧ Reach jobs workers final ∧
      ¬∃ next, Step jobs final next := by
  by_cases more : ∃ next, Step jobs st next
  · obtain ⟨next,step⟩ := more
    obtain ⟨final,path,ready,stopped⟩ := maximal_extension (Reach.next run step)
    exact ⟨final,path.head step,ready,stopped⟩
  · exact ⟨st,.refl,run,more⟩
termination_by fuel jobs st
decreasing_by have := decreases step; omega

/-- Forgetting worker identity preserves the order-independent publication ledger. -/
theorem ledger {jobs : List (List (S × V))} {workers st} (run : Reach jobs workers st) :
    ∃ todo, todo.Perm st.live.flatten ∧ Run jobs.length (writes jobs) st.issued todo st.cells := by
  induction run with
  | start =>
    refine ⟨[],?_,.start⟩
    simp [initial]
  | next _ step ih =>
    obtain ⟨todo,perm,record⟩ := ih
    cases step with
    | claim left right i counter cells within =>
      refine ⟨writes jobs i ++ todo,?_,.claim record within⟩
      simp [List.flatten_append] at perm ⊢
      simp only [writes,List.getElem?_eq_getElem within,Option.getD_some]
      exact (perm.append_left _).trans (List.perm_append_comm_assoc ..)
    | store left right tail i counter cells s v empty =>
      simp only [List.flatten_append,List.flatten_cons,List.cons_append] at perm ⊢
      have member : (s,v)∈todo := perm.mem_iff.mpr (by simp)
      obtain ⟨before,after,eq⟩ := List.append_of_mem member
      subst todo
      refine ⟨before++after,?_,.publish record empty⟩
      apply List.Perm.cons_inv (a:=(s,v))
      exact List.perm_middle.symm.trans (perm.trans List.perm_middle)
    | retire left right i counter cells all =>
      refine ⟨todo,?_,record⟩
      simpa [List.flatten_append] using perm

omit [DecidableEq S] in
private theorem allWrites (jobs : List (List (S × V))) :
    (List.range jobs.length).flatMap (writes jobs) = jobs.flatten := by
  rw [List.flatMap_def]
  apply congrArg List.flatten
  apply List.ext_getElem
  · simp
  · intro i _ hi
    simp [writes,List.getElem?_eq_getElem hi]

/-- A normally executing worker can take its next step until every invocation
has retired. The proof supplies the empty cell required by Rust's OnceLock.set. -/
theorem progress {jobs : List (List (S × V))} {workers st} (run : Reach jobs workers st)
    (owns : (jobs.flatten.map Prod.fst).Nodup) (live : st.live≠[]) :
    ∃ next, Step jobs st next := by
  obtain ⟨i,count,queues,cells⟩ := st
  obtain ⟨first,rest,rfl⟩ := List.exists_cons_of_ne_nil live
  cases first with
  | nil =>
    by_cases more : i<jobs.length
    · exact ⟨_,.claim [] rest i count cells more⟩
    · have bound := (counter_exact run).2.1
      exact ⟨_,.retire [] rest i count cells (by simpa using Nat.le_antisymm bound (Nat.le_of_not_gt more))⟩
  | cons pair tail =>
    obtain ⟨s,v⟩ := pair
    obtain ⟨todo,perm,record⟩ := ledger run
    have empty := pending_empty record (by simpa only [allWrites] using owns)
      (counter_exact run).2.1 (perm.mem_iff.mpr (show (s,v)∈((s,v)::tail)++rest.flatten by simp))
    exact ⟨_,.store [] rest tail i count cells s v empty⟩

/-- A normal maximal execution with at least one participating worker issues all
tickets, retires every invocation once and drains all writes before returning. -/
theorem maximal_join {jobs : List (List (S × V))} {workers st} (run : Reach jobs workers st)
    (positive : 0<workers) (owns : (jobs.flatten.map Prod.fst).Nodup)
    (stopped : ¬∃ next, Step jobs st next) :
    st.counter=jobs.length+workers ∧ st.live=[] ∧ Run jobs.length (writes jobs) jobs.length [] st.cells := by
  have done : st.live=[] := by by_contra live; exact stopped (progress run owns live)
  obtain ⟨balance,bound,early⟩ := counter_exact run
  have len : st.live.length=0 := by simp [done]
  have all : st.issued=jobs.length := by
    by_contra h
    have := (early (by omega)).2
    omega
  obtain ⟨todo,perm,record⟩ := ledger run
  have empty : todo=[] := by simpa [done] using perm
  exact ⟨by omega,done,by simpa [all,empty] using record⟩

end ParallelCached.Tickets
