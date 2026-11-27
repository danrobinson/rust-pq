import Parallel.Fused

namespace ParallelSigning.Publication

/-- Positions in the modification order of the single phase-one completion counter.
A job can write several cells before its one completion increment. Each WOTS worker
reads the shared phase-two cells only after acquiring READY. -/
inductive Event where
  | slot (ticket cell : Nat)
  | increment (position : Nat)
  | reduce
  | ready
  | acquireReady (worker : Nat)
  | readRoots (worker : Nat)
  deriving DecidableEq

/-- Program order, adjacent AcqRel RMWs on phase1_done, and the reads-from
edge of a worker whose acquire of phase2_state observes READY. The indices
enumerate completion order, independently of the allocation of job tickets. -/
inductive Edge (completed : List Nat) (owns : Nat → Nat → Prop) : Event → Event → Prop
  | write {pos ticket cell} : completed[pos]? = some ticket → owns ticket cell →
      Edge completed owns (.slot ticket cell) (.increment pos)
  | next {pos} : pos + 1 < completed.length →
      Edge completed owns (.increment pos) (.increment (pos+1))
  | last {pos} : pos + 1 = completed.length → Edge completed owns (.increment pos) .reduce
  | publish : Edge completed owns .reduce .ready
  | observe (w) : Edge completed owns .ready (.acquireReady w)
  | read (w) : Edge completed owns (.acquireReady w) (.readRoots w)

abbrev Before (completed : List Nat) (owns : Nat → Nat → Prop) :=
  Relation.TransGen (Edge completed owns)

private theorem chain {order : List Nat} {owns i j} (le : i ≤ j) (valid : j < order.length) :
    Relation.ReflTransGen (Edge order owns) (.increment i) (.increment j) := by
  induction le with
  | refl => exact .refl
  | step bound ih => exact .tail (ih (by omega)) (.next valid)

/-- The last finisher sees every produced phase-one cell. Every worker that
enters the WOTS phase inherits that ordering, including a worker waking after a
spurious notification. Merely receiving a notification supplies no reads-from edge. -/
theorem ready_sees_cells {jobs issued pending done} (trace : Trace jobs issued pending done)
    (last : done.length=jobs) (owns : Nat → Nat → Prop) {ticket cell}
    (existsJob : ticket<jobs) (written : owns ticket cell) (worker : Nat) :
    Before done.reverse owns (.slot ticket cell) .reduce ∧
    Before done.reverse owns (.slot ticket cell) (.readRoots worker) := by
  have perm := (ParallelFused.phase_one_ready trace last).2
  have member : ticket ∈ done.reverse := by simpa using perm.mem_iff.mpr (List.mem_range.mpr existsJob)
  obtain ⟨i,read⟩ := List.mem_iff_getElem?.mp member
  have hi : i < done.reverse.length := List.getElem?_eq_some_iff.mp read |>.1
  let lastPos := done.reverse.length - 1
  have hl : lastPos+1=done.reverse.length := by dsimp [lastPos];omega
  have prior : Before done.reverse owns (.slot ticket cell) (.increment i) := .single (.write read written)
  have path := chain (owns:=owns) (by omega : i≤lastPos) (by omega : lastPos<done.reverse.length)
  have toLast := prior.trans_left path
  have reduced := toLast.tail (Edge.last hl)
  exact ⟨reduced,((reduced.tail .publish).tail (.observe worker)).tail (.read worker)⟩

end ParallelSigning.Publication
