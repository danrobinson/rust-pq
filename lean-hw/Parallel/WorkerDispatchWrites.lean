import Parallel.WorkerCounterSafety
import Parallel.WorkerScatter

open Aeneas Aeneas.Std Result ControlFlow Aeneas.Data.Coinductive
open ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerHeap ParallelWorkerCounterSafety
namespace ParallelDispatchWrites

structure Publication (N : Usize) where
  key : Key
  value : Payload N key

def action (w : Publication N) : Program (Shared N) Unit :=
  .vis (.atomic (put w.key w.value)) (fun h => match h.cells w.key with
    | none => pure () | some _ => liftResult (fail .panic))

def prepend (writes : List (Publication N)) (tail : Program (Shared N) A) : Program (Shared N) A :=
  match writes with
  | [] => tail
  | w :: ws => action w >>= fun _ => prepend ws tail

theorem prepend_append (xs ys : List (Publication N)) (tail : Program (Shared N) A) :
    prepend (xs ++ ys) tail = prepend xs (prepend ys tail) := by
  induction xs with
  | nil => rfl
  | cons w ws ih => simp only [List.cons_append,prepend,ih]

theorem prepend_bind (xs : List (Publication N)) (tail : Program (Shared N) A)
    (k : A → Program (Shared N) B) : (prepend xs tail >>= k) = prepend xs (tail >>= k) := by
  induction xs with
  | nil => rfl
  | cons w ws ih => simp only [prepend,bind_assoc,ih]

/-- The finite receipt is obtained without a heap. Its success yields an
equality of whole interaction trees, including the occupied-cell failure. -/
structure RecordedJob (N : Usize) (A : Type) where
  live : Certified N A
  receipt : Nat → Result (List (Publication N) × A)
  sound : ∀ fuel ws a, receipt fuel = ok (ws,a) → live.raw = prepend ws (pure a)

private theorem splitOk {A B} (x : Result A) (f : A → Result B) (y : B)
    (h : (x >>= f) = ok y) : ∃ z, x=ok z ∧ f z=ok y := by
  cases x with
  | ret z => exact ⟨z,rfl,by simpa only [bind_tc_ok] using h⟩
  | div => simp [bind_tc_eq] at h
  | vis e k =>
    cases e with
    | fail e =>
      have eq : k = PEmpty.elim := funext (fun v => nomatch v)
      subst k
      change (Result.fail e >>= f) = ok y at h
      simp [bind_tc_eq] at h

private def ret (x : A) : RecordedJob N A where
  live := pure x
  receipt := fun _ => ok ([],x)
  sound := by intro fuel ws a eq; cases Result.ok_injective eq; rfl

private def bindJob (j : RecordedJob N A) (f : A → RecordedJob N B) : RecordedJob N B where
  live := j.live >>= fun a => (f a).live
  receipt := fun fuel => do
    let (xs,a) ← j.receipt fuel
    let (ys,b) ← (f a).receipt fuel
    ok (xs++ys,b)
  sound := by
    intro fuel ws b eq
    obtain ⟨⟨xs,a⟩,first,rest⟩ := splitOk _ _ _ eq
    obtain ⟨⟨ys,b'⟩,second,done⟩ := splitOk _ _ _ rest
    cases Result.ok_injective done
    rw [raw_bind,j.sound _ _ _ first,prepend_bind,pure_bind,(f a).sound _ _ _ second,prepend_append]

instance : Monad (RecordedJob N) where
  pure := ret
  bind := bindJob

instance : MonadLift Result (RecordedJob N) where
  monadLift r := {
    live := liftM r
    receipt := fun _ => do let x ← r; ok ([],x)
    sound := by
      intro fuel ws a eq
      obtain ⟨x,okx,done⟩ := splitOk _ _ _ eq
      cases Result.ok_injective done
      rw [raw_lift,okx,lifted_ok]; rfl
  }

theorem live_bind (p : RecordedJob N A) (k : A → RecordedJob N B) :
    (p >>= k).live = (p.live >>= fun a => (k a).live) := rfl
theorem live_lift (r : Result A) : (liftM r : RecordedJob N A).live = (liftM r : Certified N A) := rfl

def checkedSet (ref : Physical N T) (v : T) (debug : core.fmt.Debug T) (msg : Str) : RecordedJob N Unit where
  live := do
    let r ← ParallelWorkerCounterSafety.set ref v
    liftM (core.result.Result.expect debug r msg)
  receipt := fun _ => ok ([⟨ref.key, ref.payloadType.symm ▸ v⟩],())
  sound := by
    intro fuel ws a eq
    cases Result.ok_injective eq
    obtain ⟨k,ty⟩ := ref
    subst T
    change ((ParallelWorkerCounterSafety.set (physicalSlot N k) v).raw >>= _) = _
    rw [set_slot]
    simp only [prepend,action,ParallelWorkerInterleave.set,vis_bind]
    congr 1
    · congr 1
      funext h; unfold put
      cases e : (slot N k).read h <;> simp [slot] at e ⊢
    · funext h
      cases empty : h.cells k <;>
        simp [slot,empty,core.result.Result.expect,raw_lift,lifted_ok,Bind.bind,itree_ret_bind,liftResult]
      change ITree.vis (E:=effects (Shared N)) (Operation.fail .panic) _ = ITree.vis _ _
      congr 1
      funext e; cases e


private def loopReceipt (body : A → RecordedJob N (ControlFlow A B)) (budget : Nat) :
    Nat → A → Result (List (Publication N) × B)
  | 0, _ => fail .panic
  | remaining+1, a => do
    let (xs,branch) ← (body a).receipt budget
    match branch with
    | done b => ok (xs,b)
    | cont a' =>
      let (ys,b) ← loopReceipt body budget remaining a'
      ok (xs++ys,b)

private theorem loop_sound (body : A → RecordedJob N (ControlFlow A B)) (budget remaining : Nat)
    (a : A) (ws : List (Publication N)) (b : B)
    (eq : loopReceipt body budget remaining a = ok (ws,b)) :
    runLoop (fun a => (body a).live.raw) a = prepend ws (pure b) := by
  induction remaining generalizing a ws with
  | zero => simp [loopReceipt] at eq
  | succ n ih =>
    unfold loopReceipt at eq
    obtain ⟨⟨xs,flow⟩,bodyOk,rest⟩ := splitOk _ _ _ eq
    rw [runLoop_unfold, (body a).sound _ _ _ bodyOk, prepend_bind, pure_bind]
    cases flow with
    | done b' => cases Result.ok_injective rest; rfl
    | cont a' =>
      obtain ⟨⟨ys,b'⟩,more,finish⟩ := splitOk _ _ _ rest
      cases Result.ok_injective finish
      simp only [ih _ _ more,prepend_append]

def loop (body : A → RecordedJob N (ControlFlow A B)) (a : A) : RecordedJob N B where
  live := ParallelWorkerCounterSafety.loop (fun a => (body a).live) a
  receipt := fun budget => loopReceipt body budget budget a
  sound fuel ws b eq := loop_sound body fuel fuel a ws b eq

theorem live_checkedSet (ref : Physical N T) (v : T) (d : core.fmt.Debug T) (msg : Str) :
    (checkedSet ref v d msg).live = (ParallelWorkerCounterSafety.set ref v >>= fun r =>
      liftM (core.result.Result.expect d r msg)) := rfl

theorem raw_record_loop (body : A → RecordedJob N (ControlFlow A B)) (a : A) :
    (ParallelDispatchWrites.loop body a).live.raw = runLoop (fun a => (body a).live.raw) a := rfl

theorem raw_cert_loop (body : A → Certified N (ControlFlow A B)) (a : A) :
    (ParallelWorkerCounterSafety.loop body a).raw = runLoop (fun a => (body a).raw) a := rfl

private theorem panic_bind (k : A → Program H B) :
    ((liftResult (fail .panic) : Program H A) >>= k) = liftResult (fail .panic) := by
  simp [liftResult,vis_bind]
  congr 1; funext e; cases e

private theorem panic_ne_return {H} : (liftResult (fail .panic) : Program H Unit) ≠ pure () := by
  intro eq
  simp only [liftResult, Result.match.fail] at eq
  exact not_vis_ret eq.symm

private theorem panic_stuck {H} {h h' : H} {next : Program H Unit}
    (step : Step h [liftResult (fail .panic)] h' [next]) : False := by
  obtain ⟨f,k,eq,_,_⟩ := step.single_view
  simp only [liftResult,Result.match.fail] at eq
  have tag := vis_inj_effect eq
  cases tag

private theorem cannot_resume {N i h p peers dest final}
    (trace : ParallelWorkerScatter.Observed (H:=Shared N) (fun _ _ => True) i h p peers dest final)
    (failed : p=liftResult (fail .panic)) : False := by
  induction trace with
  | returned => exact panic_ne_return failed.symm
  | own _ action _ _ => rw [failed] at action; exact panic_stuck action
  | peer _ _ ih => exact ih failed

private theorem first_step (w : Publication N) (ws : List (Publication N)) (h : Shared N) :
    Step h [prepend (w::ws) (pure ())] (put w.key w.value h)
      [match h.cells w.key with
       | none => prepend ws (pure ()) | some _ => liftResult (fail .panic)] := by
  rw [prepend,action,vis_bind]
  have step := Step.atomic h ([] : List (Program (Shared N) Unit)) [] (put w.key w.value)
    (fun s => (match s.cells w.key with
      | none => pure () | some _ => liftResult (fail .panic)) >>= fun _ => prepend ws (pure ()))
  cases eq : h.cells w.key <;>
    simpa only [List.nil_append,eq,pure_bind,panic_bind] using step

private theorem put_preserves (w : Publication N) (h : Shared N) (key : Key) (v : Payload N key)
    (old : h.cells key = some v) : (put w.key w.value h).cells key = some v := by
  cases state : h.cells w.key with
  | some prev => simpa [put,slot,state] using old
  | none =>
    have apart : w.key ≠ key := by rintro eq; subst key; rw [old] at state; contradiction
    simpa [put,slot,state,ParallelWorkerHeap.frame _ _ _ apart] using old

/-- Every normally completed job publishes the exact typed contents of its
receipt, with arbitrary interleavings of any certified peers. A second write
to an occupied cell takes the generated panic path and cannot finish. -/
theorem observed_writes {N i h p peers dest final}
    (run : ParallelWorkerScatter.Observed (H:=Shared N) (fun _ _ => True) i h p peers dest final)
    (ws : List (Publication N)) (shape : p = prepend ws (pure ())) (safe : All peers) :
    (∀ k v, h.cells k = some v → dest.cells k = some v) ∧
    ∀ w ∈ ws, dest.cells w.key = some w.value := by
  induction run generalizing ws with
  | returned =>
    cases ws with
    | nil => exact ⟨fun _ _ => id,by simp⟩
    | cons w ws =>
      simp only [prepend,action,vis_bind] at shape
      exact False.elim (not_vis_ret shape)
  | peer change rest ih =>
    have keep := (published_persists safe change.single).2
    obtain ⟨_,_,safe',_⟩ := all_interleavings .phase1Next safe change.single
    obtain ⟨after,writes⟩ := ih ws shape safe'
    exact ⟨fun k v old => after k v (keep k v old), writes⟩
  | @own i h p peers h' p' dest final _ step rest ih =>
    cases ws with
    | nil =>
      obtain ⟨_,_,e,_,_⟩ := step.single_view
      rw [shape] at e
      exact False.elim (not_vis_ret e)
    | cons w ws =>
      have expected := first_step w ws h
      rw [shape] at step
      obtain ⟨rfl,cont⟩ := step.unique_worker expected
      cases state : h.cells w.key with
      | some full =>
        simp only [state] at cont
        exact False.elim (cannot_resume rest cont)
      | none =>
        simp only [state] at cont
        obtain ⟨keep,recorded⟩ := ih ws cont safe
        refine ⟨fun key v old => keep key v (put_preserves w h key v old),?_⟩
        intro entry member
        rcases List.mem_cons.mp member with rfl|other
        · apply keep
          simp [put,slot,state,read_after_write]
        · exact recorded _ other

private theorem focusStep {H h dest} {p : Program H Unit} {peers out}
    (step : Step h (p::peers) dest out) :
    (∃ q, out=q::peers ∧ Step h [p] dest [q]) ∨
    (∃ others, out=p::others ∧ Step h peers dest others) := by
  generalize eq : p::peers = start at step
  cases step with
  | atomic left right f k =>
    cases left with
    | nil =>
      cases eq
      exact Or.inl ⟨_,rfl,Step.atomic h [] [] f k⟩
    | cons x xs =>
      cases eq
      exact Or.inr ⟨_,rfl,Step.atomic h xs right f k⟩

private theorem observeFromSteps {H : Type} {dest : H} {final : List (Program H Unit)}
    {start : H × List (Program H Unit)}
    (steps : Relation.ReflTransGen (fun (x y : H × List (Program H Unit)) => Step x.1 x.2 y.1 y.2)
      start (dest,pure ()::final)) :
    ∀ i p peers, start.2 = p::peers →
      ParallelWorkerScatter.Observed (fun _ _ => True) i start.1 p peers dest final := by
  induction steps using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro i p peers eq
    cases eq
    exact .returned
  | @head a c move _ ih =>
    intro i p peers eq
    change Step a.1 a.2 c.1 c.2 at move
    rw [eq] at move
    rcases focusStep move with ⟨q,out,own⟩|⟨rest,out,peer⟩
    · exact .own trivial own (ih (i+1) q peers out)
    · exact .peer peer (ih i p rest out)

theorem RecordedJob.completed {N h peers dest final} (job : RecordedJob N Unit) (fuel : Nat)
    (writes : List (Publication N)) (receipt : job.receipt fuel = ok (writes,()))
    (safe : All peers)
    (run : Steps h (job.live.raw::peers) dest (pure ()::final)) :
    ∀ w ∈ writes, dest.cells w.key = some w.value :=
  (observed_writes (observeFromSteps run 0 _ _ rfl) writes (job.sound fuel _ _ receipt) safe).2

end ParallelDispatchWrites
