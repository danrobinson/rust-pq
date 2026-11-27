import Parallel.WorkerWotsLoop
import Parallel.WorkerPayloadHeap

namespace ParallelWorkerRuntime.Wots
open Aeneas Aeneas.Std Aeneas.Data.Coinductive ParallelWorkerInterleave ParallelWorkerHeap slhdsa

/-- Ghost state for a live callback: fetched tickets survive descheduling. -/
inductive Stage where
  | claim | put (i : Usize) | retired

def Stage.code (N len : Usize) (values : Usize → Bytes) : Stage → Program (Shared N) Unit
  | .claim => worker N len values
  | .put i => saving N len values i
  | .retired => pure ()

def Stage.view : Stage → Option WorkerFetch.Frame
  | .claim => some .claim
  | .put i => some (.write [(i.val,())])
  | .retired => none

def image (h : Shared N) (frames : List Stage) : WorkerFetch.Machine :=
  ⟨h.counts .phase2Next,frames.filterMap Stage.view,fun i => (h.cells (.wotsSigs i)).map fun _ => ()⟩

private theorem split_map {A B : Type} {f : A → B} {xs : List A} {l r : List B} {w : B}
    (eq : xs.map f = l ++ w :: r) : ∃ a s b, xs=a++s::b ∧ l=a.map f ∧ w=f s ∧ r=b.map f := by
  induction l generalizing xs with
  | nil =>
    cases xs with
    | nil => simp at eq
    | cons x xs =>
      simp at eq
      exact ⟨[],x,xs,rfl,rfl,eq.1.symm,eq.2.symm⟩
  | cons head l ih =>
    cases xs with
    | nil => simp at eq
    | cons x xs =>
      simp only [List.map_cons,List.cons_append,List.cons.injEq] at eq
      obtain ⟨a,s,b,rfl,rfl,rfl,rfl⟩ := ih eq.2
      exact ⟨x::a,s,b,rfl,by simp [eq.1],rfl,rfl⟩

private theorem pending_free {N len workers log} {h : Shared N} {l r : List Stage} {i : Usize}
    (run : WorkerFetch.Execution (MaximalWorker.single len).jobs workers (image h (l ++ .put i :: r)) log) :
    h.cells (.wotsSigs i.val) = none := by
  have reach := run.history.reachable
  obtain ⟨_,perm,record⟩ := ParallelCached.Tickets.ledger reach
  have mem : (i.val,()) ∈ ((image h (l ++ .put i :: r)).view (MaximalWorker.single len).jobs).live.flatten := by
    simp [image,Stage.view,WorkerFetch.Machine.view,WorkerFetch.Frame.pending]
  have vacant := ParallelCached.pending_empty record (by simpa [ParallelCached.Tickets.allWrites] using
    (MaximalWorker.single len).unique) (ParallelCached.Tickets.counter_exact reach).2.1 (perm.mem_iff.mpr mem)
  simpa [image,WorkerFetch.Machine.view] using vacant

private theorem advance {N : Usize} {h : Shared N} {n : Nat}
    (count : h.counts .phase2Next = n) (room : n+1 < 2^UScalarTy.Usize.numBits) :
    (oldTicket h .phase2Next).val = n ∧ (increment h .phase2Next 1#usize).counts .phase2Next = n+1 := by
  have old : n < 2^UScalarTy.Usize.numBits := by omega
  have t : (oldTicket h .phase2Next).val = n := by
    change h.counts .phase2Next % (2^UScalarTy.Usize.numBits) = n
    rw [count,Nat.mod_eq_of_lt old]
  refine ⟨t,?_⟩
  simp only [increment,ite_true,UScalar.wrapping_add_val_eq,t]
  have one : (1#usize).val=1 := by decide
  rw [one,UScalar.size_def,Nat.mod_eq_of_lt room]

private theorem increment_cells (s : Shared N) :
    (increment s .phase2Next 1#usize).cells = s.cells := rfl

theorem reflect_step {N len : Usize} (values : Usize → Bytes) (workers : Nat)
    (room : len.val+workers < 2^UScalarTy.Usize.numBits) {h h' : Shared N} {log frames out}
    (prior : WorkerFetch.Execution (MaximalWorker.single len.val).jobs workers (image h frames) log)
    (physical : Step h (frames.map (Stage.code N len values)) h' out) :
    ∃ frames' log', out=frames'.map (Stage.code N len values) ∧
      WorkerFetch.Execution (MaximalWorker.single len.val).jobs workers (image h' frames') log' := by
  generalize hx : frames.map (Stage.code N len values) = xs at physical
  cases physical with
  | atomic l r f k =>
    obtain ⟨left,s,right,rfl,rfl,code,rfl⟩ := split_map hx
    have atWorker : Step h [s.code N len values] (f h) [k h] := by
      rw [←code]; exact Step.atomic h [] [] f k
    let jobs := (MaximalWorker.single len.val).jobs
    have jobsLen : jobs.length=len.val := by simp [jobs,MaximalWorker.single]
    cases s with
    | claim =>
      change Step h [worker N len values] _ _ at atWorker
      rw [unfold_worker] at atWorker
      obtain ⟨state,next⟩ := atWorker.unique_worker (Step.atomic h [] [] _ _)
      let j := oldTicket h .phase2Next
      -- A claiming worker is still live, so even its final exit fetch fits.
      have notLast : h.counts .phase2Next < len.val+workers := by
        have live : 0 < ((image h (left ++ .claim :: right)).view jobs).live.length := by
          simp [image,Stage.view,WorkerFetch.Machine.view,WorkerFetch.Frame.pending]
        have balance := (ParallelCached.Tickets.counter_exact prior.history.reachable).1
        change h.counts .phase2Next + ((image h (left ++ .claim :: right)).view jobs).live.length =
          min (h.counts .phase2Next) jobs.length + workers at balance
        have limit := Nat.min_le_right (h.counts .phase2Next) jobs.length
        rw [jobsLen] at limit balance
        omega
      obtain ⟨ticket,inc⟩ := advance (h:=h) rfl (by omega)
      let left' := left.filterMap Stage.view
      let right' := right.filterMap Stage.view
      let cells := (image h []).cells
      have start : WorkerFetch.Execution jobs workers ⟨h.counts .phase2Next,left' ++ .claim :: right',cells⟩ log := by
        simpa [image,Stage.view,left',right',cells] using prior
      have fetched := start.next (WorkerFetch.Event.fetch ..)
      by_cases live : j.val < len.val
      · have found : jobs[h.counts .phase2Next]?=some [(j.val,())] := by
          rw [←ticket]; simp [jobs,MaximalWorker.single,List.getElem?_map,j,List.getElem?_range live]
        have looked := fetched.next (WorkerFetch.Event.found _ _ _ _ _ _ _ found)
        refine ⟨left ++ .put j :: right,log,by simp [next,Stage.code,j,live],?_⟩
        simpa [state,image,Stage.view,left',right',cells,inc,increment_cells] using looked
      · have miss : jobs[h.counts .phase2Next]?=none :=
          List.getElem?_eq_none (by rw [jobsLen,←ticket]; exact Nat.le_of_not_gt live)
        have retired := fetched.next (WorkerFetch.Event.exhausted _ _ _ _ _ _ miss)
        refine ⟨left ++ .retired :: right,log,by simp [next,Stage.code,j,live],?_⟩
        simpa [state,image,Stage.view,List.filterMap_cons,left',right',cells,inc,increment_cells] using retired
    | put j =>
      change Step h [saving N len values j] _ _ at atWorker
      unfold saving at atWorker
      obtain ⟨state,next⟩ := atWorker.unique_worker (Step.atomic h [] [] _ _)
      have free := pending_free prior
      simp only [free,Option.isNone_none,ite_true] at state next
      have start : WorkerFetch.Execution jobs workers
          ⟨h.counts .phase2Next,left.filterMap Stage.view ++ .write [(j.val,())] :: right.filterMap Stage.view,
            (image h []).cells⟩ log := by simpa [image,Stage.view] using prior
      have set := start.next (WorkerFetch.Event.set _ _ _ _ _ _ _ (by simp [image,free]))
      have finish := set.next (WorkerFetch.Event.finish ..)
      refine ⟨left ++ .claim :: right,j.val::log,by simp [Stage.code,next],?_⟩
      rw [state]; convert finish using 1
      simp [image,Stage.view,slot,write]
      funext i
      by_cases eq : j.val=i
      · subst i; simp; exact ⟨_,rfl⟩
      · simp [eq,Ne.symm eq]
    | retired =>
      change Step h [pure ()] _ _ at atWorker
      obtain ⟨_,_,impossible,_,_⟩ := atWorker.single_view
      change ITree.ret () = ITree.vis _ _ at impossible
      grind

theorem reflect_run {N len : Usize} (values : Usize → Bytes) (workers : Nat)
    (room : len.val+workers < 2^UScalarTy.Usize.numBits) (base dest : Shared N)
    (initial : base.counts .phase2Next=0) (fresh : ∀ i, base.cells (.wotsSigs i)=none)
    (threads : List (Program (Shared N) Unit))
    (run : Steps base (List.replicate workers (worker N len values)) dest threads) :
    ∃ frames log, threads=frames.map (Stage.code N len values) ∧
      WorkerFetch.Execution (MaximalWorker.single len.val).jobs workers (image dest frames) log := by
  let inv := fun (s : Shared N × List (Program (Shared N) Unit)) =>
    ∃ frames log, s.2=frames.map (Stage.code N len values) ∧
      WorkerFetch.Execution (MaximalWorker.single len.val).jobs workers (image s.1 frames) log
  have start : inv (base,List.replicate workers (worker N len values)) := by
    refine ⟨List.replicate workers Stage.claim,[],by simp [Stage.code],?_⟩
    have same : image base (List.replicate workers Stage.claim)=WorkerFetch.start workers := by
      simp [image, WorkerFetch.start,Stage.view,initial,fresh,List.filterMap_replicate]
    rw [same]; exact .begin
  have preserve {x y : Shared N × List (Program (Shared N) Unit)} (p : inv x)
      (step : Step x.1 x.2 y.1 y.2) : inv y := by
    obtain ⟨frames,log,eq,prior⟩ := p
    rw [eq] at step
    exact reflect_step values workers room prior step
  exact Relation.ReflTransGen.head_induction_on run
    (motive := fun s _ => inv s → inv (dest,threads)) id
    (fun step _ ih old => ih (preserve old step)) start

/-- For every normally joined execution of the actual WOTS queue tree, the
Rust counter capacity gives a legal physical ticket history and all signature
slots contain exactly the computed native vector. -/
theorem joined {N len : Usize} (values : Usize → Bytes) (workers : Nat) (positive : 0<workers)
    (room : len.val+workers < 2^UScalarTy.Usize.numBits) (base dest : Shared N)
    (initial : base.counts .phase2Next=0) (fresh : ∀ i, base.cells (.wotsSigs i)=none)
    (threads : List (Program (Shared N) Unit))
    (run : Steps base (List.replicate workers (worker N len values)) dest threads)
    (retired : ∀ w∈threads, w = pure ()) :
    ∃ frames log, WorkerFetch.Execution (MaximalWorker.single len.val).jobs workers (image dest frames) log ∧
      (image dest frames).threads=[] ∧
      ∀ j : Usize, j.val<len.val → dest.cells (.wotsSigs j.val)=some (values j) := by
  obtain ⟨frames,log,eq,history⟩ := reflect_run values workers room base dest initial fresh threads run
  have stop : ∀ f ∈ frames, f = Stage.retired := by
    intro f hf
    have done := retired (f.code N len values) (eq ▸ List.mem_map.mpr ⟨_,hf,rfl⟩)
    cases f with
    | retired => rfl
    | claim =>
      change worker N len values = ITree.ret () at done
      rw [unfold_worker] at done; grind
    | put j =>
      change saving N len values j = ITree.ret () at done
      unfold saving at done; grind
  have noFrames : (image dest frames).threads=[] := by
    change frames.filterMap Stage.view=[]
    apply List.filterMap_eq_nil_iff.mpr
    intro x member
    rw [stop x member]; rfl
  have correct := all_schedules values base dest workers threads run
    (by intro i v seen; rw [fresh] at seen; contradiction)
  refine ⟨frames,log,history,noFrames,?_⟩
  intro j live
  have filled := slhdsa.WorkerPayload.all_written history positive noFrames j.val live
  cases cell : dest.cells (.wotsSigs j.val) with
  | none => simp [image,cell] at filled
  | some val =>
    obtain ⟨idx,id,_,v⟩ := correct _ val cell
    have ij : idx=j := UScalar.eq_of_val_eq id
    rw [v,ij]
    rfl

end ParallelWorkerRuntime.Wots
