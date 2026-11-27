import Parallel.WorkerMixedHistory

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave ParallelDispatchWrites
open ParallelWorkerCounterSafety
set_option backward.isDefEq.respectTransparency false
namespace ParallelPhaseOne.Mixed

variable {N : Usize} {J : Type}

/-- Entry to the second half of an extracted worker. The clocked actions of
other workers continue while a retired phase-one worker polls READY. -/
def afterWait (next : Bool → Program (Shared N) Unit) : Program (Shared N) Unit := waitReady >>= next

def throughWait (code : Program (Shared N) Unit) (next : Bool → Program (Shared N) Unit) :=
  code >>= fun _ => afterWait next

private theorem wait_unfold {N : Usize} :
    (waitReady : Program (Shared N) Bool) =
      ITree.vis (E:=effects (Shared N)) (.atomic id) (fun s => if s.ready then pure true else waitReady) := by
  unfold waitReady
  conv => lhs; rw [ITree.iter]
  change (((poll : Program (Shared N) Bool) >>= _) >>= _) = _
  rw [bind_assoc]
  unfold poll
  rw [vis_bind]
  congr 1
  funext s
  have retBind {A B : Type} (v : A) (k : A → Program (Shared N) B) :
      (ITree.ret v >>= k) = k v := itree_ret_bind _ _
  cases s.ready <;> simp [retBind]

theorem waiting (next : Bool → Program (Shared N) Unit) (h : Shared N) (waiting : h.ready=false) :
    Step h [afterWait next] h [afterWait next] := by
  unfold afterWait
  nth_rw 1 [wait_unfold]
  rw [vis_bind]
  have atomic (k : Shared N → Program (Shared N) Unit) (q : Program (Shared N) Unit) (eq : k h=q) :
      Step h [ITree.vis (E:=effects (Shared N)) (.atomic id) k] h [q] := by subst q; exact Step.atomic h [] [] _ k
  apply atomic
  simp [waiting]


theorem accepted (next : Bool → Program (Shared N) Unit) (h : Shared N) (ready : h.ready=true) :
    Step h [afterWait next] h [next true] := by
  unfold afterWait
  rw [wait_unfold,vis_bind]
  have atomic (k : Shared N → Program (Shared N) Unit) (q : Program (Shared N) Unit) (eq : k h=q) :
      Step h [ITree.vis (.atomic id) k] h [q] := by subst q; exact Step.atomic h [] [] _ k
  apply atomic
  simp only [ready,ite_true,pure_bind]

private theorem project {H : Type} {h h' : H} {prog q : Program H Unit} (cont : Unit → Program H Unit)
    (step : Step h [prog >>= cont] h' [q]) :
    (prog=pure () ∧ Step h [cont ()] h' [q]) ∨
      ∃ q', Step h [prog] h' [q'] ∧ q=q' >>= cont := by
  cases prog using ITree.cases with
  | ret v => cases v; exact Or.inl ⟨rfl,by simpa only [pure_bind] using step⟩
  | div =>
    obtain ⟨_,_,bad,_,_⟩ := step.single_view
    rw [div_bind] at bad
    exact False.elim (not_div_vis bad)
  | vis op k =>
    cases op with
    | fail err =>
      obtain ⟨_,_,bad,_,_⟩ := step.single_view
      rw [vis_bind] at bad; cases vis_inj_effect bad
    | atomic f =>
      rw [vis_bind] at step
      have one := Step.atomic h ([] : List (Program H Unit)) [] f k
      obtain ⟨rfl,eq⟩ := step.unique_worker (Step.atomic h [] [] f _)
      exact Or.inr ⟨_,one,eq⟩

private theorem waiting_ne_returned {next : Bool → Program (Shared N) Unit} :
    afterWait next ≠ pure () := by
  unfold afterWait
  conv => lhs; rw [wait_unfold,vis_bind]
  exact fun bad => not_vis_ret bad.symm

private theorem through_ne_returned {next : Bool → Program (Shared N) Unit} (core : Program (Shared N) Unit) :
    throughWait core next ≠ pure () := by
  cases core using ITree.cases with
  | ret v => cases v; simpa only [throughWait,pure_bind] using (waiting_ne_returned (next:=next))
  | div => simp only [throughWait,div_bind]; exact fun e => not_ret_div e.symm
  | vis op k => simp only [throughWait,vis_bind]; exact fun e => not_vis_ret e.symm

/-- The full workers may poll at different times. Before publication those
polls stutter. Consequently every joined full-callback execution visits the
actual last-finisher branch with the exact physical receipts of all jobs. -/
theorem callback_joined {p : Plan N J} (d : Dispatch p) (next : Bool → Program (Shared N) Unit)
    {workers h out} (jobs : 0<p.total.val) (active : 0<workers)
    (room : p.total.val+workers<2^System.Platform.numBits)
    (run : Steps (fresh N) (List.replicate workers (throughWait p.worker next)) h out)
    (normal : ∀ x ∈ out, x=pure ()) :
    ∃ mid ts, Steps (fresh N) (List.replicate workers (throughWait p.worker next)) mid ts ∧
      ReadyAt (throughWait · next) d mid ts ∧ Steps mid ts h out := by
  have liftStep {s t : Shared N} {prog q : Program (Shared N) Unit} (hold : s.ready=false)
      (edge : Step s [throughWait prog next] t [q]) :
      (t=s ∧ q=throughWait prog next) ∨ ∃ u, Step s [prog] t [u] ∧ q=throughWait u next := by
    obtain ⟨rfl,atWait⟩ | core := project (fun _ => afterWait next) edge
    · obtain ⟨same,again⟩ := atWait.unique_worker (waiting next s hold)
      exact Or.inl ⟨same,by simpa only [throughWait,pure_bind] using again⟩
    · exact Or.inr core
  obtain pending|cut := reflectMap d (throughWait · next) (fun h s => liftStep h s) jobs room run
  · obtain ⟨s,eq,len,_⟩ := pending
    have nonempty : s.frames ≠ [] := by intro e; simp [e] at len; omega
    obtain ⟨f,mem⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact False.elim (through_ne_returned (f.code p) (normal _ (eq ▸ List.mem_map_of_mem mem)))
  · exact cut

end ParallelPhaseOne.Mixed
