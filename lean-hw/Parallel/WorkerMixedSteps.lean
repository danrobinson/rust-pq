import Parallel.WorkerMixedLedger
import Parallel.WorkerDispatchWrites

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelDispatchWrites
open ParallelWorkerCounterSafety
set_option backward.isDefEq.respectTransparency false
namespace ParallelPhaseOne.Mixed

variable {N : Usize} {J : Type}

def Present (w : Publication N) (h : Shared N) := h.cells w.key = some w.value

inductive Frame (N : Usize) (n : Nat) where
  | claim
  | writing (i : Fin n) (rest : List (Publication N))
  | stalled (i : Fin n) (prog : Program (Shared N) Unit) (stuck : Stalled prog)
  | failed (i : Fin n)
  | retired

def Frame.owner : Frame N n → Option (Fin n)
  | .writing i _ | .stalled i _ _ | .failed i => some i
  | .claim | .retired => none

def Frame.code (p : Plan N J) : Frame N n → Program (Shared N) Unit
  | .claim => p.worker
  | .writing _ xs => prepend xs p.counter
  | .stalled _ prog _ => prog
  | .failed _ => liftResult (fail .panic)
  | .retired => pure ()

def Frame.Accounted (writes : Fin n → List (Publication N)) (h : Shared N) : Frame N n → Prop
  | .writing i xs => ∀ w ∈ writes i, Present w h ∨ w ∈ xs
  | _ => True

theorem Frame.advance {h h' : Shared N} (writes : Fin n → List (Publication N))
    (keeps : ∀ w, Present w h → Present w h') (frame : Frame N n)
    (valid : frame.Accounted writes h) : frame.Accounted writes h' := by
  cases frame with
  | writing i xs =>
    intro w mem
    exact (valid w mem).imp (keeps w) id
  | _ => trivial

theorem put_keeps (w v : Publication N) (h : Shared N) (prior : Present v h) :
    Present v (put w.key w.value h) := by
  unfold Present at *
  unfold put
  simp only [slot]
  cases old : h.cells w.key with
  | some => exact prior
  | none =>
    by_cases same : w.key = v.key
    · rw [same] at old; rw [old] at prior; contradiction
    · exact (frame h.toHeap v.key w.key same w.value).trans prior

theorem writing_step (p : Plan N J) (w : Publication N) (ws : List (Publication N)) (h : Shared N) :
    Step h [prepend (w::ws) p.counter] (put w.key w.value h)
      [if (h.cells w.key).isNone then prepend ws p.counter else liftResult (fail .panic)] := by
  rw [prepend, action, vis_bind]
  have reject (k : Unit → Program (Shared N) Unit) :
      ((liftResult (fail .panic) : Program (Shared N) Unit) >>= k) = liftResult (fail .panic) := by
    simp [liftResult,vis_bind]; congr 1; funext e; cases e
  have atomic (k : Shared N → Program (Shared N) Unit) (q : Program (Shared N) Unit) (eq : k h = q) :
      Step h [ITree.vis (.atomic (put w.key w.value)) k] (put w.key w.value h) [q] := by
    subst q; exact Step.atomic h [] [] _ k
  apply atomic
  cases filled : h.cells w.key <;> simp only [Option.isNone_none,Option.isNone_some,Bool.false_eq_true,ite_false,ite_true,reject]
  exact itree_ret_bind _ _

theorem claiming_exhausted (p : Plan N J) (h : Shared N)
    (miss : p.jobs.val[(oldTicket h .phase1Next).val]? = none) :
    Step h [p.worker] (increment h .phase1Next 1#usize) [pure ()] := by
  have entry : p.worker = (p.body >>= p.resume) := by
    unfold Plan.worker; rw [runLoop_unfold]; congr 1; funext x; cases x <;> rfl
  rw [entry]
  unfold Plan.body
  simp only [bind_assoc]
  have fetch (k : Usize → Program (Shared N) Unit) (q : Program (Shared N) Unit)
      (eq : k (oldTicket h .phase1Next) = q) :
      Step h [rmw .phase1Next 1#usize >>= k] (increment h .phase1Next 1#usize) [q] := by
    subst q; exact rmw_step .phase1Next 1#usize h k [] []
  apply fetch
  simp only [miss]
  exact itree_ret_bind _ _

theorem increment_exact (c : Counter) (h : Shared N)
    (room : h.counts c+1 < 2^System.Platform.numBits) :
    (increment h c 1#usize).counts c = h.counts c+1 := by
  simp only [increment,ite_true,UScalar.wrapping_add_val_eq,current_ticket h c (by omega)]
  change (h.counts c+1) % UScalar.size .Usize = _
  exact Nat.mod_eq_of_lt (by simpa [UScalar.size_def] using room)

theorem completed_add {h : Shared N} {total : Usize} (below : h.counts .phase1Done < total.val) :
    ∃ n, oldTicket h .phase1Done + 1#usize = ok n ∧ n.val=h.counts .phase1Done+1 := by
  have bound : total.val < 2^System.Platform.numBits := total.bv.isLt
  have old := current_ticket h .phase1Done (by omega)
  have spec := UScalar.add_spec (x:=oldTicket h .phase1Done) (y:=1#usize) (by
    rw [UScalar.max_USize_eq,old]
    change h.counts .phase1Done+1 ≤ Usize.max
    refine below.trans_le ?_
    rw [Usize.max,Usize.numBits]; change total.val ≤ 2^System.Platform.numBits-1; omega)
  have extract {T} {m : Result T} {P : T → Prop} (hs : WP.spec m P) :
      ∃ v, m=ok v ∧ P v := by cases m <;> simp_all
  obtain ⟨v,r,e⟩ := extract spec
  change v.val = (oldTicket h .phase1Done).val + 1 at e
  exact ⟨v,r,by rwa [old] at e⟩

end ParallelPhaseOne.Mixed
