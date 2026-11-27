import Parallel.WorkerMixedCallback
import Parallel.WorkerWotsHistory
import Parallel.WorkerWotsFrame

open Aeneas Aeneas.Std Result Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelPhaseOne.Mixed
namespace ParallelWorkerRuntime.Wots.Entry

/-- WOTS shares physical state with slower workers taking their final
phase-one ticket. Forget just that exhausted counter for the WOTS trace. -/
def mask (h : Shared N) : Shared N :=
  { h with counts := fun c => if c=.phase1Next then 0 else h.counts c }

private theorem mask_increment1 (h : Shared N) :
    mask (increment h .phase1Next 1#usize)=mask h := by
  unfold mask increment
  congr 2
  funext c
  cases c <;> rfl

private theorem mask_increment2 (h : Shared N) :
    mask (increment h .phase2Next 1#usize)=increment (mask h) .phase2Next 1#usize := by
  unfold mask increment
  congr 2
  funext c
  cases c <;> rfl

private theorem mask_store (h : Shared N) (j : Nat) (v : Bytes) :
    mask ((slot N (.wotsSigs j)).write v h) =
      (slot N (.wotsSigs j)).write v (mask h) := rfl

theorem project_wots {N len values} {p q : Program (Shared N) Unit} {h h'} (safe : Residual N len values p)
    (edge : Step h [p] h' [q]) :
    Step (mask h) [p] (mask h') [q] ∧ Residual N len values q ∧ h'.ready=h.ready ∧
      h'.counts .phase1Next=h.counts .phase1Next ∧ h'.cells .roots=h.cells .roots := by
  cases safe with
  | next =>
    rw [unfold_worker] at edge ⊢
    obtain ⟨rfl,rfl⟩ := edge.unique_worker (Step.atomic h [] [] _ _)
    rw [mask_increment2]
    refine ⟨Step.atomic (mask h) [] [] _ _,?_,rfl,rfl,rfl⟩
    dsimp only
    split
    · exact .save _ ‹_›
    · exact .retired
  | save j live =>
    unfold saving at edge ⊢
    obtain ⟨rfl,rfl⟩ := edge.unique_worker (Step.atomic h [] [] _ _)
    have chosen := Step.atomic (mask h) ([] : List (Program (Shared N) Unit)) []
      (fun s => if (s.cells (.wotsSigs j.val)).isNone then (slot N (.wotsSigs j.val)).write (values j) s else s)
      (fun s => if (s.cells (.wotsSigs j.val)).isNone then worker N len values else liftResult (fail .panic))
    by_cases empty : (h.cells (.wotsSigs j.val)).isNone
    · have vacant : ((mask h).cells (.wotsSigs j.val)).isNone := empty
      refine ⟨?_,?_,?_,?_,?_⟩
      · simpa only [List.nil_append,ite_eq_left empty,ite_eq_left vacant,mask_store] using chosen
      · simpa only [ite_eq_left empty] using (Residual.next (N:=N) (len:=len) (values:=values))
      · simp [empty,slot]
      · simp [empty,slot,write]
      · simp [empty,slot,write]
    · have occupied : ¬((mask h).cells (.wotsSigs j.val)).isNone := empty
      simp only [ite_eq_right empty]
      exact ⟨by simpa only [List.nil_append,ite_eq_right occupied] using chosen,.failed,by simp,by simp,by simp⟩
  | retired => obtain ⟨_,_,e,_,_⟩ := edge.single_view; exact False.elim (not_vis_ret e)
  | failed =>
    obtain ⟨_,_,eq,_,_⟩ := edge.single_view
    simp only [liftResult,Result.match.fail] at eq
    cases vis_inj_effect eq

/-- The three executable prefixes remaining at publication: final exhausted
fetch, successful wait, and reading the published roots. Each property is
a one-step equation, so takes no position on scheduling order. -/
structure Start (N len : Usize) (values : Usize → Bytes) where
  jobs : Nat
  roots : Payload N .roots
  finish : Program (Shared N) Unit
  wait : Program (Shared N) Unit
  load : Program (Shared N) Unit
  finishStep : ∀ h : Shared N, jobs ≤ h.counts .phase1Next →
    h.counts .phase1Next < 2^System.Platform.numBits →
    Step h [finish] (increment h .phase1Next 1#usize) [wait]
  waitStep : ∀ h : Shared N, h.ready=true → Step h [wait] h [load]
  loadStep : ∀ h : Shared N, h.cells .roots=some roots → Step h [load] h [worker N len values]

inductive Position (N len : Usize) (values : Usize → Bytes) where
  | finish | wait | load
  | signing (p : Program (Shared N) Unit) (valid : Residual N len values p)

def Position.code (s : Start N len values) : Position N len values → Program (Shared N) Unit
  | .finish => s.finish | .wait => s.wait | .load => s.load | .signing p _ => p

def Position.view : Position N len values → Program (Shared N) Unit
  | .signing p _ => p
  | _ => worker N len values

def Position.needsTicket : Position N len values → Bool
  | .finish => true | _ => false

/-- Slow workers can take their last fetch and read the initial roots after
other workers have already started signing. Every such schedule projects to
a real WOTS schedule with identical physical cells. -/
theorem project {N len values} (s : Start N len values) {h dest : Shared N} {positions : List (Position N len values)} {out}
    (published : h.ready=true) (roots : h.cells .roots=some s.roots) (exhausted : s.jobs≤h.counts .phase1Next)
    (capacity : h.counts .phase1Next + positions.countP Position.needsTicket < 2^System.Platform.numBits)
    (run : Steps h (positions.map (Position.code s)) dest out) :
    ∃ ps : List (Position N len values), out=ps.map (Position.code s) ∧
      dest.ready=true ∧ dest.cells .roots=some s.roots ∧ s.jobs≤dest.counts .phase1Next ∧
      dest.counts .phase1Next + ps.countP Position.needsTicket < 2^System.Platform.numBits ∧
      Steps (mask h) (positions.map Position.view) (mask dest) (ps.map Position.view) := by
  let start := (h,positions.map (Position.code s))
  change Relation.ReflTransGen (fun (x y : Shared N × List (Program (Shared N) Unit)) =>
    Step x.1 x.2 y.1 y.2) start (dest,out) at run
  generalize finalEq : (dest,out)=z at run
  suffices result : ∃ ps : List (Position N len values), z.2=ps.map (Position.code s) ∧
      z.1.ready=true ∧ z.1.cells .roots=some s.roots ∧ s.jobs≤z.1.counts .phase1Next ∧
      z.1.counts .phase1Next + ps.countP Position.needsTicket < 2^System.Platform.numBits ∧
      Steps (mask h) (positions.map Position.view) (mask z.1) (ps.map Position.view) by
    cases finalEq; exact result
  clear finalEq
  induction run with
  | refl => exact ⟨positions,rfl,published,roots,exhausted,capacity,.refl⟩
  | @tail before after _ event ih =>
    obtain ⟨ps,codes,ready,full,limit,cap,history⟩ := ih
    obtain ⟨b,bs⟩ := before; obtain ⟨a,threads⟩ := after
    change Step b bs a threads at event
    change bs=ps.map (Position.code s) at codes
    cases event with
    | atomic l r f k =>
      obtain ⟨left,stage,right,rfl,rfl,code,rfl⟩ := splitMap codes.symm
      have own : Step b [stage.code s] (f b) [k b] := by rw [←code]; exact Step.atomic b [] [] _ _
      cases stage with
      | finish =>
        change b.counts .phase1Next + _ < _ at cap
        simp [Position.needsTicket,List.countP_append,List.countP_cons] at cap
        have room : b.counts .phase1Next+1 < 2^System.Platform.numBits := by omega
        obtain ⟨state,next⟩ := own.unique_worker (s.finishStep b limit (by omega))
        refine ⟨left ++ .wait :: right,by simp [next,Position.code],by simpa [state,increment] using ready,
          by simpa [state,increment] using full,?_,?_,?_⟩
        · change _ ≤ (f b).counts .phase1Next
          rw [state,increment_exact _ _ room]; exact Nat.le_succ_of_le limit
        · change (f b).counts .phase1Next + _ < _
          simp [state,increment_exact _ _ room,Position.needsTicket,List.countP_append,List.countP_cons]; omega
        · simpa [state,mask_increment1,Position.view] using history
      | wait =>
        obtain ⟨state,next⟩ := own.unique_worker (s.waitStep b ready)
        exact ⟨left ++ .load :: right,by simp [next,Position.code],by simpa [state,increment] using ready,
          by simpa [state,increment] using full,by simpa [state] using limit,
          by simpa [state,Position.needsTicket,List.countP_append,List.countP_cons] using cap,
          by simpa [state,Position.view] using history⟩
      | load =>
        obtain ⟨state,next⟩ := own.unique_worker (s.loadStep b full)
        exact ⟨left ++ .signing _ .next :: right,by simp [Position.code,next],by simpa [state,increment] using ready,
          by simpa [state,increment] using full,by simpa [state] using limit,
          by simpa [state,Position.needsTicket,List.countP_append,List.countP_cons] using cap,
          by simpa [state,Position.view] using history⟩
      | signing prog valid =>
        obtain ⟨virtual,valid',ready',count',roots'⟩ := project_wots valid own
        refine ⟨left ++ .signing _ valid' :: right,by simp [Position.code],ready'.trans ready,
          roots'.trans full,by simpa [count'] using limit,by simpa [count',Position.needsTicket,List.countP_append,List.countP_cons] using cap,?_⟩
        obtain ⟨upd,cont,eq,heap,thread⟩ := virtual.single_view
        have moved := Step.atomic (mask b) (left.map Position.view) (right.map Position.view) upd cont
        apply history.follow
        simpa [Position.view,eq,heap,thread] using moved

/-- The actual worker prefix is the original phase-one loop, wait and
root load. A late worker's exhausted fetch is an ordinary scheduler event. -/
def Start.ofPlan (p : ParallelPhaseOne.Plan N J) (size : p.jobs.length=p.total.val)
    (roots : Payload N .roots) (next : Bool → Program (Shared N) Unit)
    (load : ∀ h : Shared N, h.cells .roots=some roots →
      Step h [next true] h [worker N len values]) : Start N len values where
  jobs := p.total.val
  roots := roots
  finish := throughWait p.worker next
  wait := afterWait next
  load := next true
  loadStep := load
  waitStep := accepted next
  finishStep h exhausted cap := by
    have miss : p.jobs.val[(oldTicket h .phase1Next).val]?=none := by
      apply List.getElem?_eq_none
      change p.jobs.length ≤ _
      rw [size,ParallelWorkerCounterSafety.current_ticket _ _ cap]
      exact exhausted
    have st := (claiming_exhausted p h miss).continuation (fun _ => afterWait next) [] []
    simpa only [List.nil_append,pure_bind,throughWait] using st

theorem joined {N len values} (s : Start N len values) {h dest : Shared N}
    {positions : List (Position N len values)} {out}
    (positive : 0<positions.length) (room : len.val+positions.length<2^System.Platform.numBits)
    (pending : ∀ x∈positions, x=.finish ∨ x=.wait)
    (published : h.ready=true) (roots : h.cells .roots=some s.roots) (exhausted : s.jobs≤h.counts .phase1Next)
    (capacity : h.counts .phase1Next + positions.countP Position.needsTicket < 2^System.Platform.numBits)
    (fresh : ∀ i, h.cells (.wotsSigs i)=none) (zero : h.counts .phase2Next=0)
    (run : Steps h (positions.map (Position.code s)) dest out) (normal : ∀ p∈out, p=pure ()) :
    (∀ j : Usize, j.val<len.val → dest.cells (.wotsSigs j.val)=some (values j)) ∧
    ∀ k, (∀ i,Key.wotsSigs i≠k) → dest.cells k=h.cells k := by
  obtain ⟨ps,final,ready,installed,past,cap,projected⟩ :=
    project s published roots exhausted capacity run
  have beginCode : positions.map Position.view = List.replicate positions.length (worker N len values) := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp,?_⟩
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    rcases pending x hx with rfl|rfl <;> rfl
  rw [beginCode] at projected
  have stopped : ∀ y∈ps.map Position.view, y=pure () := by
    intro y mem
    obtain ⟨x,member,rfl⟩ := List.mem_map.mp mem
    have ret := normal _ (final ▸ List.mem_map_of_mem member)
    have impossible {w : Program (Shared N) Unit} {t q} (st : Step dest [w] t [q]) (returned : w=pure ()) :
        False := by
      obtain ⟨_,_,eq,_,_⟩ := st.single_view; rw [returned] at eq; exact not_vis_ret eq
    cases x with
    | signing => exact ret
    | wait => exact False.elim (impossible (s.waitStep _ ready) ret)
    | load => exact False.elim (impossible (s.loadStep _ installed) ret)
    | finish =>
      have fit : dest.counts .phase1Next < 2^System.Platform.numBits := by omega
      exact False.elim (impossible (s.finishStep _ past fit) ret)
  obtain ⟨_,_,_,_,contents⟩ := Wots.joined values positions.length positive room (mask h) (mask dest)
    zero fresh _ projected stopped
  refine ⟨contents,?_⟩
  apply Wots.untouched values (mask h) (mask dest) positions.length _ projected
  intro i v set
  change h.cells (.wotsSigs i)=some v at set
  rw [fresh] at set
  contradiction

theorem Start.joined_flags {N len values} (s : Start N len values) {h dest : Shared N}
    (late : List Bool) {out} (positive : 0<late.length) (room : len.val+late.length<2^System.Platform.numBits)
    (published : h.ready=true) (roots : h.cells .roots=some s.roots) (exhausted : s.jobs≤h.counts .phase1Next)
    (capacity : h.counts .phase1Next+late.countP id<2^System.Platform.numBits)
    (fresh : ∀ i, h.cells (.wotsSigs i)=none) (zero : h.counts .phase2Next=0)
    (run : Steps h (late.map (fun b => if b then s.finish else s.wait)) dest out)
    (normal : ∀ p∈out, p=pure ()) :
    (∀ j : Usize, j.val<len.val → dest.cells (.wotsSigs j.val)=some (values j)) ∧
    ∀ k, (∀ i,Key.wotsSigs i≠k) → dest.cells k=h.cells k := by
  let pos : Bool → Position N len values := fun b => if b then .finish else .wait
  apply joined s (positions:=late.map pos) (out:=out) (by simpa using positive) (by simpa using room)
    _ published roots exhausted _ fresh zero _ normal
  · intro x mem
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp mem
    cases b <;> simp [pos]
  · simpa only [List.countP_map,show Position.needsTicket ∘ pos = id from funext (fun b => by cases b <;> rfl)] using capacity
  · rw [List.map_map]
    convert run using 2
    congr 1
    funext b; cases b <;> rfl

end ParallelWorkerRuntime.Wots.Entry
