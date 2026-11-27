import Parallel.WorkerMixedPrefix
open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelDispatchWrites
open ParallelWorkerCounterSafety
set_option backward.isDefEq.respectTransparency false
namespace ParallelPhaseOne.Mixed

variable {N : Usize} {J : Type}

structure Dispatch (p : Plan N J) where
  job : J → RecordedJob N Unit
  same : ∀ j, p.dispatch j = (job j).live.raw
  size : p.jobs.length=p.total.val

def Dispatch.jobAt {p : Plan N J} (d : Dispatch p) (i : Fin p.total.val) :=
  d.job (p.jobs.val[i.val]'(by change i.val<p.jobs.length; rw [d.size]; exact i.isLt))

noncomputable def Dispatch.writes {p : Plan N J} (d : Dispatch p) (i : Fin p.total.val) :
    List (Publication N) := open Classical in
  if h : StableReceipt (d.jobAt i).receipt () then h.choose else []

theorem Dispatch.success {p : Plan N J} (d : Dispatch p) (i : Fin p.total.val)
    (stable : StableReceipt (d.jobAt i).receipt ()) :
    (d.jobAt i).live.raw = prepend (d.writes i) (pure ()) := by
  classical
  obtain ⟨fuel,valid⟩ := stable.choose_spec
  apply (d.jobAt i).sound fuel
  simpa only [Dispatch.writes,dite_eq_left stable] using valid fuel (by omega)

def Dispatch.admitted {p : Plan N J} (d : Dispatch p) : Frame N p.total.val → Prop
  | .writing i _ => StableReceipt (d.jobAt i).receipt ()
  | _ => True

structure Evidence {p : Plan N J} (d : Dispatch p) (s : State N p.total.val) : Prop where
  paid : ∀ i ∈ s.finished, StableReceipt (d.jobAt i).receipt ()
  live : ∀ f ∈ s.frames, d.admitted f

private theorem Evidence.replace {p : Plan N J} {d : Dispatch p} {done left right f g}
    (ev : Evidence d ⟨done,left ++ f::right⟩) (ok : d.admitted g) :
    Evidence d ⟨done,left ++ g::right⟩ := by
  refine ⟨ev.paid,?_⟩
  intro x hx
  rcases List.mem_append.mp hx with l|m
  · exact ev.live x (by simp [l])
  · rcases List.mem_cons.mp m with rfl|r
    · exact ok
    · exact ev.live x (by simp [r])

def Dispatch.remaining {p : Plan N J} (d : Dispatch p) : Frame N p.total.val → Prop
  | .writing i xs => ∀ w∈xs, w∈d.writes i
  | .stalled i _ _ => ¬StableReceipt (d.jobAt i).receipt ()
  | _ => True

def Dispatch.Written {p : Plan N J} (d : Dispatch p) (h : Shared N) :=
  (∀ i,StableReceipt (d.jobAt i).receipt ()) →
    ∀ k v, h.cells k=some v → ∃ i, (⟨k,v⟩ : Publication N)∈d.writes i

structure Origin {p : Plan N J} (d : Dispatch p) (h : Shared N) (frames : List (Frame N p.total.val)) : Prop where
  trace : d.Written h
  unused : h.counts .phase2Next=0
  suffix : ∀ f∈frames, d.remaining f

theorem Origin.change {p : Plan N J} {d : Dispatch p} {h t : Shared N} {l r f g}
    (origin : Origin d h (l++f::r)) (rest : d.remaining g)
    (trace : d.Written t) (unused : t.counts .phase2Next=0) : Origin d t (l++g::r) := by
  refine ⟨trace,unused,?_⟩
  intro x member
  rcases List.mem_append.mp member with left|tail
  · exact origin.suffix x (by simp [left])
  · rcases List.mem_cons.mp tail with rfl|right
    · exact rest
    · exact origin.suffix x (by simp [right])

theorem Origin.store {p : Plan N J} {d : Dispatch p} {h : Shared N} {l r i w ws}
    (origin : Origin d h (l++.writing i (w::ws)::r)) :
    let next : Frame N p.total.val := if (h.cells w.key).isNone then .writing i ws else .failed i
    Origin d (put w.key w.value h) (l++next::r) := by
  intro next
  have listed := origin.suffix (.writing i (w::ws)) (by simp)
  apply origin.change
  · cases e : h.cells w.key <;> simp [next,e,Dispatch.remaining]
    intro v mem; exact listed v (by simp [mem])
  · intro stable key v seen
    cases e : h.cells w.key with
    | some _ => exact origin.trace stable key v (by simpa [put,slot,e] using seen)
    | none =>
      by_cases eq : w.key=key
      · subst key
        have same : w.value=v := Option.some.inj (by simpa [put,slot,e,read_after_write] using seen)
        subst v
        exact ⟨i,listed w List.mem_cons_self⟩
      · apply origin.trace stable key v
        simpa [put,slot,e,ParallelWorkerHeap.frame _ _ _ eq] using seen
  · cases e : h.cells w.key <;> simpa [put,slot,e,write] using origin.unused

def Frame.retiredFlag : Frame N n → Bool
  | .retired => true
  | _ => false

def Capacity (h : Shared N) (s : State N n) :=
  h.counts .phase1Next ≤ n + s.frames.countP Frame.retiredFlag

/-- Before reduction a retired worker has already seen the exhausted queue. -/
def Exhausted (h : Shared N) (s : State N n) :=
  Frame.retired ∈ s.frames → n ≤ h.counts .phase1Next

/-- On a single scheduler step either the same invariant continues or the
actual last finisher is at the first reducer instruction with its inputs. -/
theorem reflectWorker {p : Plan N J} (d : Dispatch p) {h h' : Shared N} {done left right f q}
    (inv : Invariant d.writes h ⟨done,left ++ f :: right⟩)
    (evidence : Evidence d ⟨done,left ++ f :: right⟩)
    (origin : Origin d h (left ++ f :: right))
    (low : h.counts .phase1Done<p.total.val)
    (exited : Exhausted h ⟨done,left ++ f :: right⟩)
    (cap : Capacity h ⟨done,left ++ f :: right⟩)
    (fits : p.total.val + (left ++ f :: right).length < 2^System.Platform.numBits)
    (step : Step h [f.code p] h' [q]) :
    (∃ done' g, q=g.code p ∧ Invariant d.writes h' ⟨done',left ++ g :: right⟩ ∧ Evidence d ⟨done',left ++ g :: right⟩ ∧ Capacity h' ⟨done',left ++ g :: right⟩ ∧ h'.counts .phase1Done<p.total.val ∧ Exhausted h' ⟨done',left ++ g :: right⟩ ∧ h'.ready=h.ready ∧ Origin d h' (left++g::right)) ∨
    (q=p.reducing ∧ h'.counts .phase1Done=p.total.val ∧
      (∀ i, StableReceipt (d.jobAt i).receipt () ∧ ∀ w ∈ d.writes i, Present w h') ∧
      p.total.val≤h'.counts .phase1Next ∧ (∀ x∈left++right, x=.claim ∨ x=.retired) ∧
      h'.ready=h.ready ∧ h'.counts .phase2Next=0 ∧ d.Written h' ∧ h'.counts .phase1Next ≤ p.total.val+(left ++ f::right).length) := by
  classical
  cases f with
  | claim =>
    have room : h.counts .phase1Next+1 < 2^System.Platform.numBits := by
      have a := List.countP_le_length (p:=Frame.retiredFlag) (l:=left)
      have b := List.countP_le_length (p:=Frame.retiredFlag) (l:=right)
      simp [Capacity,Frame.retiredFlag,List.countP_append] at cap
      simp at fits; omega
    have old := current_ticket h .phase1Next (by omega)
    by_cases live : h.counts .phase1Next < p.total.val
    · let i : Fin p.total.val := ⟨h.counts .phase1Next,live⟩
      let j := p.jobs.val[i.val]'(by change i.val < p.jobs.length; rw [d.size]; exact i.isLt)
      have lookup : p.jobs.val[(oldTicket h .phase1Next).val]?=some j := by
        rw [old]; apply List.getElem?_eq_getElem
      obtain ⟨rfl,next⟩ := step.unique_worker (fetch_job p h [] j lookup)
      have next' : q=((d.jobAt i).live.raw >>= fun () => p.counter) := by
        simpa only [d.same,Dispatch.jobAt,j] using next
      have claimed := inv.claim i rfl room
      by_cases stable : StableReceipt (d.jobAt i).receipt ()
      · left
        refine ⟨done,.writing i (d.writes i),?_,claimed,evidence.replace stable,?_,low,?_,rfl,?_⟩
        · rw [next',d.success i stable,prepend_bind,pure_bind]; rfl
        · simp [Capacity,increment_exact _ _ room,Frame.retiredFlag,List.countP_append]; omega
        · simp [Exhausted,increment_exact _ _ room] at exited ⊢; intro m; exact (exited m).trans (Nat.le_succ _)
        · exact origin.change (fun _ mem => mem) origin.trace origin.unused
      · left
        have stuck := (d.jobAt i).stalled_bind stable (fun () => p.counter)
        refine ⟨done,.stalled i q (next' ▸ stuck),rfl,?_,evidence.replace trivial,?_,low,?_,rfl,?_⟩
        · exact claimed.replace rfl rfl (fun _ x => x) trivial
        · simp [Capacity,increment_exact _ _ room,Frame.retiredFlag,List.countP_append]; omega
        · simp [Exhausted,increment_exact _ _ room] at exited ⊢; intro m; exact (exited m).trans (Nat.le_succ _)
        · exact origin.change stable origin.trace origin.unused
    · have miss : p.jobs.val[(oldTicket h .phase1Next).val]?=none := by
        apply List.getElem?_eq_none; change p.jobs.length ≤ _; rw [d.size,old]; omega
      obtain ⟨rfl,rfl⟩ := step.unique_worker (claiming_exhausted p h miss)
      refine Or.inl ⟨done,.retired,rfl,inv.exhaust (by omega) room,evidence.replace trivial,?_,low,?_,rfl,?_⟩
      · simp [Capacity,Frame.retiredFlag,List.countP_append,increment_exact _ _ room] at cap ⊢; omega
      · intro _; rw [increment_exact _ _ room]; omega
      · exact origin.change trivial origin.trace origin.unused
  | writing i xs =>
    cases xs with
    | cons w ws =>
      obtain ⟨rfl,next⟩ := step.unique_worker (writing_step p w ws h)
      let g : Frame N p.total.val := if (h.cells w.key).isNone then .writing i ws else .failed i
      left
      refine ⟨done,g,?_,inv.store,evidence.replace ?_,?_,?_,?_,?_,origin.store⟩
      · cases e : h.cells w.key <;> simpa [g,e,Frame.code] using next
      · have old := evidence.live (.writing i (w::ws)) (by simp)
        cases e : h.cells w.key <;> simp [g,e,Dispatch.admitted]; exact old
      · cases e : h.cells w.key <;> simpa [Capacity,g,e,put,slot,write,Frame.retiredFlag,List.countP_append] using cap
      · cases e : h.cells w.key <;> simpa [put,slot,e,write] using low
      · cases e : h.cells w.key <;> simpa [Exhausted,g,e,put,slot,write] using exited
      · cases e : h.cells w.key <;> simp [put,slot,e]
    | nil =>
      have before := inv.ownership
      simp [State.ledger,Frame.owner] at before
      obtain ⟨missing,_⟩ := Ledger.complete i before
      have below : h.counts .phase1Done < p.total.val := by
        have card := Finset.card_le_univ (insert i done)
        rw [Finset.card_insert_of_notMem missing,Fintype.card_fin] at card
        rw [inv.count]; exact card
      obtain ⟨n,add,value⟩ := completed_add below
      obtain ⟨rfl,next⟩ := step.unique_worker (finished_job p h [] n add)
      have capacity := n.bv.isLt
      have incRoom : h.counts .phase1Done+1 < 2^System.Platform.numBits := by rw [←value]; exact capacity
      obtain ⟨valid,all⟩ := inv.finish incRoom
      have ev : Evidence d ⟨insert i done,left ++ .claim :: right⟩ := by
        refine ⟨?_,(evidence.replace (g:=.claim) trivial).live⟩
        intro j member
        rcases Finset.mem_insert.mp member with rfl|m
        · exact evidence.live (.writing j []) (by simp)
        · exact evidence.paid j m
      by_cases same : n=p.total
      · right
        have last : (increment h .phase1Done 1#usize).counts .phase1Done=p.total.val := by
          rw [increment_exact _ _ incRoom,←value,same]
        have idle := valid.exclusive last
        refine ⟨by simpa [same] using next,last,fun i => ⟨Ledger.at_reduction (s:=⟨0,insert _ done,[]⟩) (valid.count.symm.trans last) _ ev.paid i,all last i⟩,idle.1,?_,rfl,origin.unused,origin.trace,?_⟩
        · intro x mem; apply idle.2 x; simpa using List.mem_append.mp mem |>.imp id Or.inr
        · exact cap.trans (Nat.add_le_add_left List.countP_le_length _)
      · refine Or.inl ⟨_,.claim,by simpa [same,Frame.code] using next,valid,ev,?_,?_,?_,rfl,origin.change trivial origin.trace origin.unused⟩
        · simpa [Capacity,increment,Frame.retiredFlag,List.countP_append] using cap
        · have ne : n.val≠p.total.val := fun e => same (UScalar.eq_of_val_eq e)
          rw [increment_exact _ _ incRoom]; omega
        · simpa [Exhausted,increment] using exited
  | stalled i prog stuck =>
    obtain ⟨stuck',counts,ready,keep⟩ := stuck.step step
    refine Or.inl ⟨_,.stalled i q stuck',rfl,inv.replace rfl counts (fun w => keep w.key w.value) trivial,evidence.replace trivial,?_,?_,?_,ready,?_⟩
    · simpa [Capacity,counts,Frame.retiredFlag,List.countP_append] using cap
    · rwa [counts]
    · simpa [Exhausted,counts] using exited
    · have none := origin.suffix (.stalled i prog stuck) (by simp)
      exact origin.change none (fun stable => False.elim (none (stable i))) (by rw [counts]; exact origin.unused)
  | failed i =>
    obtain ⟨_,_,eq,_,_⟩ := step.single_view
    simp only [Frame.code,liftResult,Result.match.fail] at eq
    cases vis_inj_effect eq
  | retired =>
    obtain ⟨_,_,eq,_,_⟩ := step.single_view
    exact False.elim (not_vis_ret eq)

end ParallelPhaseOne.Mixed
