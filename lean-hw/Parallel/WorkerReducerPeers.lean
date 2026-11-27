import Parallel.WorkerMixedCallback
import Parallel.WorkerWotsEntry
import Parallel.WorkerSplitCut

open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive
open ParallelWorkerHeap ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerCounterSafety
open ParallelWorkerFrozenReads ParallelDispatchWrites ParallelPhaseOne ParallelPhaseOne.Mixed
namespace ParallelReducerPeers

inductive Role where | leader | late | waiting
  deriving DecidableEq

def Role.code (p : Plan N J) (next : Bool → Program (Shared N) Unit) (focus : Program (Shared N) Unit) :
    Role → Program (Shared N) Unit
  | .leader => focus
  | .late => throughWait p.worker next
  | .waiting => afterWait next

def Role.needsFetch : Role → Bool
  | .leader | .late => true
  | .waiting => false

def no_leader {p : Plan N J} (next : Bool → Program (Shared N) Unit) (a b : Program (Shared N) Unit)
    (roles : List Role) (clear : .leader ∉ roles) : roles.map (Role.code p next a)=roles.map (Role.code p next b) := by
  apply List.map_congr_left
  intro x mem
  cases x with
  | leader => exact False.elim (clear mem)
  | late | waiting => rfl

structure Valid (p : Plan N J) (h : Shared N) (roles : List Role) : Prop where
  unique : roles.count .leader=1
  waiting : h.ready=false
  used : p.jobs.length≤h.counts .phase1Next
  space : h.counts .phase1Next+roles.countP Role.needsFetch<2^System.Platform.numBits

private theorem waiting_step (p : Plan N J) (next : Bool → Program (Shared N) Unit)
    (h : Shared N) (hs : h.ready=false) : Step h [afterWait next] h [afterWait next] :=
  Mixed.waiting next h hs

private theorem late_step (p : Plan N J) (next : Bool → Program (Shared N) Unit) (h : Shared N)
    (used : p.jobs.length≤h.counts .phase1Next) (cap : h.counts .phase1Next<2^System.Platform.numBits) :
    Step h [throughWait p.worker next] (increment h .phase1Next 1#usize) [afterWait next] := by
  have miss : p.jobs.val[(oldTicket h .phase1Next).val]?=none := by
    apply List.getElem?_eq_none
    rw [current_ticket h .phase1Next cap]
    exact used
  simpa only [throughWait,List.nil_append,pure_bind] using
    (claiming_exhausted p h miss).continuation (fun _ => afterWait next) [] []

theorem observe {N J} {p : Plan N J} (next : Bool → Program (Shared N) Unit) {q : Program (Shared N) Unit}
    {h t : Shared N} {roles out} (valid : Valid p h roles)
    (edge : Step h (roles.map (Role.code p next q)) t out) :
    (∃ q', Step h [q] t [q'] ∧ out=roles.map (Role.code p next q')) ∨
    (∃ roles', out=roles'.map (Role.code p next q) ∧ Valid p t roles' ∧
      t.cells=h.cells ∧ t.counts .phase2Next=h.counts .phase2Next ∧ roles'.length=roles.length) := by
  generalize eq : roles.map (Role.code p next q)=ts at edge
  cases edge with
  | atomic left right f k =>
    obtain ⟨l,x,r,rfl,rfl,own,rfl⟩ := splitMap eq
    have one : Step h [x.code p next q] (f h) [k h] := by rw [←own]; exact Step.atomic h [] [] f k
    cases x with
    | leader =>
      left
      have unique := valid.unique
      simp [List.count_append] at unique
      have freeL : .leader ∉ l := List.count_eq_zero.mp (by omega)
      have freeR : .leader ∉ r := List.count_eq_zero.mp (by omega)
      exact ⟨_,one,by simp only [List.map_append,List.map_cons,Role.code]; rw [no_leader next q (k h) l freeL,no_leader next q (k h) r freeR]⟩
    | late =>
      have cap := valid.space
      simp [List.countP_append,List.countP_cons,Role.needsFetch] at cap
      have room : h.counts .phase1Next+1 < 2^System.Platform.numBits := by omega
      obtain ⟨heap,after⟩ := one.unique_worker (late_step p next h valid.used (by omega))
      right
      refine ⟨l++.waiting::r,by simp [Role.code,after],⟨?_,?_,?_,?_⟩,?_,?_,by simp⟩
      · simpa [List.count_append] using valid.unique
      · rw [heap]; exact valid.waiting
      · rw [heap,increment_exact _ _ room]; exact Nat.le_succ_of_le valid.used
      · rw [heap,increment_exact _ _ room]; simp [List.countP_append,List.countP_cons,Role.needsFetch]; omega
      · rw [heap]; rfl
      · rw [heap]; rfl
    | waiting =>
      obtain ⟨heap,after⟩ := one.unique_worker (waiting_step p next h valid.waiting)
      right
      refine ⟨l++.waiting::r,by simp [Role.code,after],(by rw [heap]; exact valid),?_,?_,rfl⟩ <;> rw [heap]

theorem scheduler_length {H A} {h t : H} {xs ys : List (Program H A)} (history : Steps h xs t ys) :
    ys.length=xs.length := by
  let view := fun x : H × List (Program H A) => x.2.length=xs.length
  have stable {a b : H × List (Program H A)} (old : view a) (step : Step a.1 a.2 b.1 b.2) : view b := by
    rcases a with ⟨h,as_⟩; rcases b with ⟨t,bs⟩
    change Step h as_ t bs at step
    cases step with
    | atomic l r f k => simpa [view] using old
  exact Relation.ReflTransGen.head_induction_on history (motive:=fun x _ => view x → view (t,ys))
    id (fun edge _ ih old => ih (stable old edge)) rfl

theorem ready_roles {p : Plan N J} (d : Dispatch p) (next : Bool → Program (Shared N) Unit)
    {h : Shared N} {ts} (ready : ReadyAt (throughWait · next) d h ts)
    (room : p.total.val + ts.length + ts.length < 2^System.Platform.numBits) :
    ∃ roles, ts=roles.map (Role.code p next (throughWait p.reducing next)) ∧ Valid p h roles := by
  classical
  obtain ⟨_,_,_,used,⟨l,r,shape,others⟩,closed,_,max,_⟩ := ready
  let tag : Program (Shared N) Unit → Role := fun v => if v=throughWait p.worker next then .late else .waiting
  let roles := l.map tag ++ .leader :: r.map tag
  have tagCode (xs : List (Program (Shared N) Unit)) (all : ∀ x∈xs,x=throughWait p.worker next ∨ x=throughWait (pure ()) next) :
      (xs.map tag).map (Role.code p next (throughWait p.reducing next))=xs := by
    rw [List.map_map]
    conv => rhs; rw [← List.map_id xs]
    apply List.map_congr_left
    intro x mem
    rcases all x mem with e|e
    · simp [tag,e,Role.code]
    · by_cases same : x=throughWait p.worker next
      · simp [tag,same,Role.code]
      · change (tag x).code p next (throughWait p.reducing next)=x
        simp only [tag,ite_eq_right same,Role.code]
        rw [e,throughWait,pure_bind]
  have left := tagCode l (fun x mem => others x (List.mem_append_left _ mem))
  have right := tagCode r (fun x mem => others x (List.mem_append_right _ mem))
  have length : roles.length=ts.length := by simp [roles,shape]
  refine ⟨roles,by simp [roles,Role.code,left,right,shape],⟨?_,closed,d.size ▸ used,?_⟩⟩
  · have free (xs : List (Program (Shared N) Unit)) : (xs.map tag).count .leader=0 := by
      apply List.count_eq_zero.mpr
      intro mem
      obtain ⟨v,_,eq⟩ := List.mem_map.mp mem
      unfold tag at eq; split at eq <;> contradiction
    simp [roles,List.count_append,free]
  · have count := List.countP_le_length (p:=Role.needsFetch) (l:=roles)
    omega

end ParallelReducerPeers
