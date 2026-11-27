import Parallel.WorkerMixedRun

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelDispatchWrites
open ParallelWorkerCounterSafety
namespace ParallelPhaseOne.Mixed

variable {N : Usize} {J : Type}

def ReadyAt (lift : Program (Shared N) Unit → Program (Shared N) Unit) {p : Plan N J} (d : Dispatch p) (h : Shared N) (threads : List (Program (Shared N) Unit)) :=
  lift p.reducing ∈ threads ∧ h.counts .phase1Done=p.total.val ∧
    (∀ i, ∃ bound, (∀ fuel ≥ bound, (d.jobAt i).receipt fuel = ok (d.writes i,())) ∧
      ∀ w ∈ d.writes i, Present w h) ∧ p.total.val≤h.counts .phase1Next ∧
    (∃ left right, threads=left ++ lift p.reducing :: right ∧
      ∀ x∈left++right, x=lift p.worker ∨ x=lift (pure ())) ∧
    h.ready=false ∧ h.counts .phase2Next=0 ∧ h.counts .phase1Next≤p.total.val+threads.length ∧
    ∀ k v, h.cells k=some v → ∃ i, (⟨k,v⟩ : Publication N)∈d.writes i

abbrev ReadyToReduce {p : Plan N J} := @ReadyAt N J id p

theorem splitMap {F P : Type} {f : F → P} {xs : List F} {l r : List P} {w : P}
    (eq : xs.map f = l ++ w :: r) : ∃ a s b, xs=a++s::b ∧ l=a.map f ∧ w=f s ∧ r=b.map f := by
  induction l generalizing xs with
  | nil =>
    cases xs with
    | nil => simp at eq
    | cons x xs => simp at eq; exact ⟨[],x,xs,rfl,rfl,eq.1.symm,eq.2.symm⟩
  | cons head l ih =>
    cases xs with
    | nil => simp at eq
    | cons x xs =>
      simp only [List.map_cons,List.cons_append,List.cons.injEq] at eq
      obtain ⟨a,s,b,rfl,rfl,rfl,rfl⟩ := ih eq.2
      exact ⟨x::a,s,b,rfl,by simp [eq.1],rfl,rfl⟩

/-- Reflection of every prefix of the real scheduler. Either the workers are
still accounted for by the ticket ledger, or this very execution passed
through a reducer with every canonical dispatch result already installed. -/
theorem reflectMap {p : Plan N J} (d : Dispatch p) {h : Shared N} {workers out}
    (lift : Program (Shared N) Unit → Program (Shared N) Unit)
    (project : ∀ {s t : Shared N} {prog q : Program (Shared N) Unit}, s.ready=false →
      Step s [lift prog] t [q] → (t=s ∧ q=lift prog) ∨ ∃ q', Step s [prog] t [q'] ∧ q=lift q')
    (positive : 0<p.total.val) (room : p.total.val+workers<2^System.Platform.numBits)
    (run : Steps (fresh N) (List.replicate workers (lift p.worker)) h out) :
    (∃ s : State N p.total.val, out=s.frames.map (lift ∘ Frame.code p) ∧ s.frames.length=workers ∧
      Invariant d.writes h s ∧ Evidence d s ∧ Capacity h s ∧ h.counts .phase1Done<p.total.val ∧ Exhausted h s ∧ h.ready=false ∧ Origin d h s.frames) ∨
    ∃ middle threads, Steps (fresh N) (List.replicate workers (lift p.worker)) middle threads ∧
      ReadyAt lift d middle threads ∧ Steps middle threads h out := by
  let start := (fresh N,List.replicate workers (lift p.worker))
  change Relation.ReflTransGen (fun (x y : Shared N × List (Program (Shared N) Unit)) =>
    Step x.1 x.2 y.1 y.2) start (h,out) at run
  generalize endpoint : (h,out) = z at run
  suffices all : (∃ s : State N p.total.val, z.2=s.frames.map (lift ∘ Frame.code p) ∧ s.frames.length=workers ∧
      Invariant d.writes z.1 s ∧ Evidence d s ∧ Capacity z.1 s ∧ z.1.counts .phase1Done<p.total.val ∧ Exhausted z.1 s ∧ z.1.ready=false ∧ Origin d z.1 s.frames) ∨
    ∃ middle threads, Steps start.1 start.2 middle threads ∧ ReadyAt lift d middle threads ∧
      Steps middle threads z.1 z.2 by cases endpoint; exact all
  clear endpoint
  induction run with
  | refl =>
    left
    refine ⟨⟨∅,List.replicate workers .claim⟩,by simp [start,Frame.code,Function.comp_def],by simp,
      Invariant.initial ..,⟨by simp,?_⟩,?_,positive,?_,rfl,⟨?_,rfl,?_⟩⟩
    · intro f hf; obtain rfl := List.eq_of_mem_replicate hf; trivial
    · simp [Capacity,start,fresh,empty]
    · intro mem
      exact False.elim (by cases List.eq_of_mem_replicate mem)
    · intro _ k v seen; cases seen
    · intro f mem; obtain rfl := List.eq_of_mem_replicate mem; trivial
  | @tail mid final before physical ih =>
    rcases ih with ⟨s,eq,size,inv,ev,cap,low,exited,ready,origin⟩ | ⟨m,ts,prior,correct,after⟩
    · obtain ⟨fin,fs⟩ := s
      obtain ⟨h0,ts⟩ := mid
      obtain ⟨h1,rs⟩ := final
      change Step h0 ts h1 rs at physical
      change ts=fs.map (lift ∘ Frame.code p) at eq
      cases physical with
      | atomic l r f k =>
        obtain ⟨left,frame,right,rfl,rfl,code,rfl⟩ := splitMap eq.symm
        have own : Step h0 [(lift ∘ Frame.code p) frame] (f h0) [k h0] := by rw [←code]; exact Step.atomic h0 [] [] _ _
        obtain idle | ⟨core,real,wrapped⟩ := project ready own
        · left
          obtain ⟨unchanged,again⟩ := idle
          refine ⟨⟨fin,left ++ frame :: right⟩,by simp [again],size,?_,ev,?_,?_,?_,?_,?_⟩ <;> rwa [unchanged]
        obtain cont|reducer := reflectWorker d inv ev origin low exited cap (size ▸ room) real
        · obtain ⟨newDone,g,gcode,valid,paid,capacity,small,miss,still,newOrigin⟩ := cont
          left
          exact ⟨⟨newDone,left ++ g::right⟩,by simp [wrapped,gcode],by simpa using size,valid,paid,capacity,small,miss,still.trans ready,newOrigin⟩
        · right
          obtain ⟨code',count,receipts,issued,idle,phase,zero,originAt,high⟩ := reducer
          refine ⟨_,_,before.tail (Step.atomic h0 _ _ f k),⟨by simp [wrapped,code'],count,?_,issued,?_,phase.trans ready,zero,?_,originAt (fun i => (receipts i).1)⟩,.refl⟩
          · intro i
            obtain ⟨stable,stored⟩ := receipts i
            obtain ⟨bound,hb⟩ := stable.choose_spec
            exact ⟨bound,by simpa only [Dispatch.writes,dite_eq_left stable] using hb,stored⟩
          · refine ⟨_,_,by rw [wrapped,code'],?_⟩
            intro x hx
            rw [←List.map_append] at hx
            obtain ⟨g,mem,rfl⟩ := List.mem_map.mp hx
            rcases idle g mem with rfl|rfl <;> simp [Frame.code]
          · simpa using high

    · exact Or.inr ⟨m,ts,prior,correct,after.follow physical⟩

private theorem Frame.returned {p : Plan N J} (f : Frame N n) (ret : f.code p = pure ()) :
    f=.retired := by
  cases f with
  | retired => rfl
  | failed i =>
    simp only [Frame.code,liftResult,Result.match.fail] at ret
    exact False.elim (not_vis_ret ret.symm)
  | stalled i prog stuck => exact False.elim (stuck.not_returned () ret)
  | writing i xs =>
    cases xs with
    | nil => simp [Frame.code,prepend,Plan.counter,rmw,vis_bind] at ret; exact False.elim (not_vis_ret ret.symm)
    | cons w ws => simp [Frame.code,prepend,action,vis_bind] at ret; exact False.elim (not_vis_ret ret.symm)
  | claim =>
    have unfoldWorker : p.worker=p.body >>= p.resume := by
      unfold Plan.worker; rw [runLoop_unfold]; congr 1; funext x; cases x <;> rfl
    simp only [Frame.code,unfoldWorker,Plan.body,rmw,vis_bind] at ret
    exact False.elim (not_vis_ret ret.symm)

theorem joined {p : Plan N J} (d : Dispatch p) {h : Shared N} {workers out}
    (jobs : 0<p.total.val) (active : 0<workers) (room : p.total.val+workers<2^System.Platform.numBits)
    (run : Steps (fresh N) (List.replicate workers p.worker) h out) (normal : ∀ x∈out, x=pure ()) :
    ∃ mid ts, Steps (fresh N) (List.replicate workers p.worker) mid ts ∧
      ReadyToReduce d mid ts ∧ Steps mid ts h out := by
  obtain pending|done := reflectMap d id (fun _ step => Or.inr ⟨_,step,rfl⟩) jobs room run
  · obtain ⟨s,codes,length,inv,_,_,low,exited,_⟩ := pending
    have retired : ∀ f ∈ s.frames, f=.retired := fun f mem =>
      f.returned (p:=p) (normal _ (codes ▸ List.mem_map_of_mem mem))
    have existsWorker : s.frames ≠ [] := by intro e; simp [e] at length; omega
    obtain ⟨f,mem⟩ := List.exists_mem_of_ne_nil _ existsWorker
    have past := exited (retired f mem ▸ mem)
    have all : s.finished=Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro i
      have issued := (inv.ownership.issued i).mp (i.isLt.trans_le past)
      rcases issued with owns|paid
      · simp [State.ledger,Ledger.active] at owns
        obtain ⟨g,hg,seen⟩ := owns
        rw [retired g hg] at seen
        contradiction
      · exact paid
    have count := inv.count
    rw [all,Finset.card_univ,Fintype.card_fin] at count
    omega
  · exact done

end ParallelPhaseOne.Mixed
