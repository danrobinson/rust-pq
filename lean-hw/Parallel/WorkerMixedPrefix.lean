import Parallel.WorkerMixedSteps

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelDispatchWrites
open ParallelWorkerCounterSafety
namespace ParallelPhaseOne.Mixed

structure State (N : Usize) (n : Nat) where
  finished : Finset (Fin n)
  frames : List (Frame N n)

def State.ledger (s : State N n) (h : Shared N) : Ledger n :=
  ⟨h.counts .phase1Next,s.finished,s.frames.map Frame.owner⟩

structure Invariant (writes : Fin n → List (Publication N)) (h : Shared N) (s : State N n) : Prop where
  ownership : (s.ledger h).Valid
  count : h.counts .phase1Done = s.finished.card
  finishedWrites : ∀ i ∈ s.finished, ∀ w ∈ writes i, Present w h
  runningWrites : ∀ frame ∈ s.frames, frame.Accounted writes h

theorem Invariant.initial (N : Usize) (n workers : Nat) (writes : Fin n → List (Publication N)) :
    Invariant writes (fresh N) ⟨∅, List.replicate workers .claim⟩ := by
  constructor
  · simpa [State.ledger,Frame.owner,fresh,empty] using Ledger.initial n workers
  · simp [fresh,empty]
  · simp
  · intro f hf
    obtain rfl := List.eq_of_mem_replicate hf
    trivial

private theorem transportPeers (writes : Fin n → List (Publication N)) {left right : List (Frame N n)}
    {h h' : Shared N} {f g : Frame N n} (valid : ∀ x ∈ left ++ f :: right, x.Accounted writes h)
    (keeps : ∀ w, Present w h → Present w h') (newFrame : g.Accounted writes h') :
    ∀ x ∈ left ++ g :: right, x.Accounted writes h' := by
  intro x mem
  simp only [List.mem_append,List.mem_cons] at mem
  rcases mem with l|rfl|r
  · exact Frame.advance writes keeps _ (valid x (by simp [l]))
  · exact newFrame
  · exact Frame.advance writes keeps _ (valid x (by simp [r]))

theorem Invariant.claim {writes : Fin n → List (Publication N)} {h : Shared N} {done left right}
    (inv : Invariant writes h ⟨done,left ++ .claim :: right⟩)
    (i : Fin n) (old : i.val=h.counts .phase1Next)
    (room : h.counts .phase1Next+1 < 2^System.Platform.numBits) :
    Invariant writes (increment h .phase1Next 1#usize) ⟨done,left ++ .writing i (writes i) :: right⟩ := by
  constructor
  · have prev := inv.ownership
    simp [State.ledger,Frame.owner] at prev ⊢
    rw [increment_exact _ _ room]
    exact Ledger.claim i old prev
  · exact inv.count
  · exact inv.finishedWrites
  · exact transportPeers writes inv.runningWrites (fun _ x => x) (fun w mem => Or.inr mem)

theorem Invariant.replace {writes : Fin n → List (Publication N)} {h h' : Shared N} {done left right f g}
    (inv : Invariant writes h ⟨done,left ++ f :: right⟩)
    (same : g.owner=f.owner) (counts : h'.counts=h.counts)
    (keep : ∀ w, Present w h → Present w h') (next : g.Accounted writes h') :
    Invariant writes h' ⟨done,left ++ g :: right⟩ := by
  constructor
  · simpa only [State.ledger,counts,List.map_append,List.map_cons,same] using inv.ownership
  · rw [counts]; exact inv.count
  · intro i hi w hw; exact keep w (inv.finishedWrites i hi w hw)
  · exact transportPeers writes inv.runningWrites keep next

theorem Invariant.exhaust {writes : Fin n → List (Publication N)} {h : Shared N} {done left right}
    (inv : Invariant writes h ⟨done,left ++ .claim :: right⟩)
    (limit : n ≤ h.counts .phase1Next) (room : h.counts .phase1Next+1 < 2^System.Platform.numBits) :
    Invariant writes (increment h .phase1Next 1#usize) ⟨done,left ++ .retired :: right⟩ := by
  constructor
  · have prev := inv.ownership
    simp [State.ledger,Frame.owner] at prev ⊢
    rw [increment_exact _ _ room]; exact Ledger.exhausted limit prev
  · exact inv.count
  · exact inv.finishedWrites
  · exact transportPeers writes inv.runningWrites (fun _ x => x) trivial

theorem Invariant.store {writes : Fin n → List (Publication N)} {h : Shared N} {done left right i w ws}
    (inv : Invariant writes h ⟨done,left ++ .writing i (w::ws) :: right⟩) :
    let next : Frame N n := if (h.cells w.key).isNone then .writing i ws else .failed i
    Invariant writes (put w.key w.value h) ⟨done,left ++ next :: right⟩ := by
  intro next
  have owner : next.owner = some i := by cases e : h.cells w.key <;> simp [next,e,Frame.owner]
  have counts : (put w.key w.value h).counts=h.counts := by cases e : h.cells w.key <;> simp [put,slot,e,write]
  constructor
  · simp only [State.ledger,List.map_append,List.map_cons,owner,counts]
    simpa [State.ledger,Frame.owner] using inv.ownership
  · rw [counts]; exact inv.count
  · intro j hj v hv; exact put_keeps w v h (inv.finishedWrites j hj v hv)
  · apply transportPeers writes inv.runningWrites (put_keeps w · h)
    cases e : h.cells w.key with
    | some v => simp [next,e,Frame.Accounted]
    | none =>
      simp only [next,e,Option.isNone_none,ite_true,Frame.Accounted]
      intro v hv
      have old := inv.runningWrites (.writing i (w::ws)) (by simp) v hv
      rcases old with present|mem
      · exact Or.inl (put_keeps _ _ _ present)
      · rcases List.mem_cons.mp mem with rfl|tail
        · exact Or.inl (by simp [Present,put,slot,e,read_after_write])
        · exact Or.inr tail

/-- The final RMW can be justified even when work completed out of issue order.
Every queue entry's exact receipt is already physically present. -/
theorem Invariant.finish {writes : Fin n → List (Publication N)} {h : Shared N} {done left right i}
    (inv : Invariant writes h ⟨done,left ++ .writing i [] :: right⟩)
    (room : h.counts .phase1Done+1 < 2^System.Platform.numBits) :
    let h' := increment h .phase1Done 1#usize
    Invariant writes h' ⟨insert i done,left ++ .claim :: right⟩ ∧
      (h'.counts .phase1Done=n → ∀ j, ∀ w ∈ writes j, Present w h') := by
  intro h'
  have prev := inv.ownership
  simp [State.ledger,Frame.owner] at prev
  obtain ⟨absent,owned⟩ := Ledger.complete i prev
  have complete : ∀ j ∈ insert i done, ∀ w ∈ writes j, Present w h' := by
    intro j member w hw
    rcases Finset.mem_insert.mp member with rfl|mem
    · have paid := inv.runningWrites (.writing j []) (by simp) w hw
      change Present w h
      simpa only [List.not_mem_nil,or_false] using paid
    · exact inv.finishedWrites j mem w hw
  have count : h'.counts .phase1Done=(insert i done).card := by
    rw [Finset.card_insert_of_notMem absent,← inv.count]
    exact increment_exact _ _ room
  refine ⟨⟨?_,count,complete,transportPeers writes inv.runningWrites (fun _ x => x) trivial⟩,?_⟩
  · simpa [State.ledger,Frame.owner,h',increment] using owned
  · intro reached
    exact Ledger.at_reduction (s:=⟨0,insert i done,[]⟩) (count.symm.trans reached) _ complete

theorem Invariant.exclusive {writes : Fin n → List (Publication N)} {h : Shared N} {s : State N n}
    (inv : Invariant writes h s) (fullCount : h.counts .phase1Done=n) :
    n ≤ h.counts .phase1Next ∧ ∀ f ∈ s.frames, f=.claim ∨ f=.retired := by
  have all : ∀ i, i∈s.finished := fun i =>
    Ledger.at_reduction (s:=s.ledger h) (inv.count.symm.trans fullCount) (·∈s.finished) (fun _ hit => hit) i
  have issued : ∀ i : Fin n, i.val<h.counts .phase1Next := fun i =>
    (inv.ownership.issued i).mpr (Or.inr (all i))
  constructor
  · by_contra! short
    exact (Nat.lt_irrefl _) (issued ⟨_,short⟩)
  · intro f existsFrame
    have free : f.owner=none := by
      cases obs : f.owner with
      | none => rfl
      | some i =>
        have owned : i∈(s.ledger h).active := List.mem_filterMap.mpr
          ⟨f.owner,List.mem_map_of_mem existsFrame,obs⟩
        exact False.elim (inv.ownership.separate i owned (all i))
    cases f <;> simp_all [Frame.owner]

end ParallelPhaseOne.Mixed
