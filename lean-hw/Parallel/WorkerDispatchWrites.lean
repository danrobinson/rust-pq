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

/-- Erase the allocation certificate while keeping the physical cell used by
the independently proved scalar and SIMD lane schedules. -/
def referenceVector (xs : alloc.vec.Vec (Physical N T)) :
    alloc.vec.Vec (ParallelWorkerCells.Ref (Shared N) T) :=
  alloc.vec.Vec.from (xs.val.map Physical.ref) (by simp)

theorem reference_table (N : Usize) (key : Nat → Key) (T : Type)
    (ty : ∀ i, Payload N (key i) = T) (count : Usize) :
    referenceVector (physicalTable N key T ty count) = table N key T ty count := by
  apply alloc.vec.Vec.ext
  simp only [referenceVector,physicalTable,table,alloc.vec.Vec.from_val,List.map_map]
  rfl

theorem reference_index (xs : alloc.vec.Vec (Physical N T)) (i : Usize) :
    (liftM ((referenceVector xs).index_usize i) : Program (Shared N) _) =
      (liftM (xs.index_usize i) >>= fun cell => pure cell.ref) := by
  have index : (referenceVector xs).index_usize i = (xs.index_usize i >>= fun r => ok r.ref) := by
    simp only [alloc.vec.Vec.index_usize,alloc.vec.Vec.getElem?_Nat_eq,
      referenceVector,alloc.vec.Vec.from_val,List.getElem?_map]
    cases xs.val[i.val]? <;> simp [bind_tc_eq]
  rw [index]
  change liftResult (_ >>= _) = _
  rw [lift_bind]
  simp only [lift_ok]; rfl

theorem reference_set (ref : Physical N T) (v : T) :
    (ParallelWorkerCounterSafety.set ref v).raw = ParallelWorkerInterleave.set ref.ref v := by
  obtain ⟨key,ty⟩ := ref
  subst T
  rfl

/-- A stable receipt permits a larger shared fuel bound for all nested loops. -/
def StableReceipt (evaluate : Nat → Result (List (Publication N) × A)) (a : A) : Prop :=
  ∃ ws bound, ∀ fuel ≥ bound, evaluate fuel = ok (ws,a)

theorem StableReceipt.unique {evaluate : Nat → Result (List (Publication N) × A)} {a : A}
    {xs ys : List (Publication N)} {n m : Nat}
    (left : ∀ fuel ≥ n, evaluate fuel = ok (xs,a)) (right : ∀ fuel ≥ m, evaluate fuel = ok (ys,a)) :
    xs = ys := by
  have equal := (left (max n m) (by omega)).symm.trans (right (max n m) (by omega))
  exact congrArg Prod.fst (Result.ok_injective equal)

/-- Phase-one dispatch has only typed OnceLock stores as shared effects. -/
def writeSemantics (N : Usize) : EffectWP (effects (Shared N)) where
  State := Unit
  wp op post _ := match op with
    | .atomic f => (∃ w : Publication N, f = put w.key w.value) ∧ ∀ h, post h ()
    | .fail _ => True

instance : (writeSemantics N).Monotonic where
  wp_monotonic := by
    intro op q r implies _ pre
    cases op with
    | fail => exact trivial
    | atomic f => exact ⟨pre.1,fun h => implies h () (pre.2 h)⟩

instance : (writeSemantics N).Conjunctive where
  wp_conj := by
    intro op _ requires nonempty all
    obtain ⟨q,inhabited⟩ := nonempty
    cases op with
    | fail => exact trivial
    | atomic f => exact ⟨(all q inhabited).1,fun h p wanted => (all p wanted).2 h⟩

def ReturnsWith (p : Program (Shared N) A) (post : A → Prop) : Prop :=
  DWLP (writeSemantics N) p (fun x _ => post x) ()

/-- The finite receipt is obtained without a heap. Its success yields an
equality of whole interaction trees, including the occupied-cell failure. -/
structure RecordedJob (N : Usize) (A : Type) where
  live : Certified N A
  receipt : Nat → Result (List (Publication N) × A)
  complete : ReturnsWith live.raw (StableReceipt receipt)
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
  complete := DWLP.ret_iff.mpr ⟨[],0,fun _ _ => rfl⟩
  sound := by intro fuel ws a eq; cases Result.ok_injective eq; rfl

private def bindJob (j : RecordedJob N A) (f : A → RecordedJob N B) : RecordedJob N B where
  live := j.live >>= fun a => (f a).live
  receipt := fun fuel => do
    let (xs,a) ← j.receipt fuel
    let (ys,b) ← (f a).receipt fuel
    ok (xs++ys,b)
  complete := by
    apply DWLP.bind j.complete
    intro a _ ha
    apply DWLP.mono (f a).complete
    intro b _ hb
    obtain ⟨xs,n,hx⟩ := ha
    obtain ⟨ys,m,hy⟩ := hb
    refine ⟨xs++ys,max n m,?_⟩
    intro fuel enough
    simp [hx fuel (by omega),hy fuel (by omega)]
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
    complete := by
      change DWLP (writeSemantics _) (liftResult r) _ ()
      cases r with
      | ret a => exact DWLP.ret_iff.mpr ⟨[],0,fun _ _ => by simp only [bind_ok]⟩
      | div => exact DWLP.div
      | vis e k =>
        cases e with
        | fail err => exact DWLP.vis trivial
    sound := by
      intro fuel ws a eq
      obtain ⟨x,okx,done⟩ := splitOk _ _ _ eq
      cases Result.ok_injective done
      rw [raw_lift,okx,lifted_ok]; rfl
  }

theorem live_bind (p : RecordedJob N A) (k : A → RecordedJob N B) :
    (p >>= k).live = (p.live >>= fun a => (k a).live) := rfl
theorem live_lift (r : Result A) : (liftM r : RecordedJob N A).live = (liftM r : Certified N A) := rfl

/-- Lifted native computations contribute no publications. Their failure or
divergence is retained in the heap-independent receipt evaluation. -/
theorem receipt_lift_bind (r : Result A) (k : A → RecordedJob N B) (fuel : Nat) :
    ((liftM r : RecordedJob N A) >>= k).receipt fuel = (r >>= fun a => (k a).receipt fuel) := by
  change Aeneas.Std.bind (Aeneas.Std.bind r (fun a => ok ([],a))) _ = _
  simp only [bind_tc_eq,Aeneas.Std.bind_assoc,bind_ok]
  congr 1
  funext a
  generalize e : (k a).receipt fuel = tail
  cases tail with
  | ret v => rcases v with ⟨ws,b⟩; simp [e]
  | div => simp [e]
  | vis eff cont =>
    cases eff with
    | fail err =>
      have impossible : cont = PEmpty.elim := funext (fun x => nomatch x)
      subst cont
      simp [e,bind_vis]
      congr 1; funext x; cases x

private def checkedLive (ref : Physical N T) (v : T) (debug : core.fmt.Debug T) (msg : Str) :
    Certified N Unit := do
  let r ← ParallelWorkerCounterSafety.set ref v
  liftM (core.result.Result.expect debug r msg)

private theorem checkedLive_action (ref : Physical N T) (v : T) (debug : core.fmt.Debug T) (msg : Str) :
    (checkedLive ref v debug msg).raw = action ⟨ref.key, ref.payloadType.symm ▸ v⟩ := by
    obtain ⟨k,ty⟩ := ref
    subst T
    change ((ParallelWorkerCounterSafety.set (physicalSlot N k) v).raw >>= _) = _
    rw [set_slot]
    simp only [action,ParallelWorkerInterleave.set,vis_bind]
    congr 1
    · congr 1
      funext h; unfold put
      cases e : (slot N k).read h <;> simp [slot] at e ⊢
    · funext h
      cases empty : h.cells k <;>
        simp [slot,empty,core.result.Result.expect,raw_lift,lifted_ok,Bind.bind,itree_ret_bind,liftResult]
      rfl


def checkedSet (ref : Physical N T) (v : T) (debug : core.fmt.Debug T) (msg : Str) : RecordedJob N Unit where
  live := checkedLive ref v debug msg
  receipt := fun _ => ok ([⟨ref.key, ref.payloadType.symm ▸ v⟩],())
  complete := by
    unfold ReturnsWith
    rw [checkedLive_action]
    apply DWLP.vis
    refine ⟨⟨_,rfl⟩,fun h => ?_⟩
    dsimp only
    cases h.cells ref.key
    · apply DWLP.ret_iff.mpr
      exact ⟨_,0,fun _ _ => rfl⟩
    · apply DWLP.vis
      trivial
  sound := by
    intro fuel ws a eq
    cases Result.ok_injective eq
    rw [checkedLive_action]
    simp only [prepend]
    exact (bind_pure (action _) : _).symm

theorem receipt_checkedSet (ref : Physical N T) (v : T) (debug : core.fmt.Debug T) (msg : Str) (fuel : Nat) :
    (checkedSet ref v debug msg).receipt fuel = ok ([⟨ref.key,ref.payloadType.symm ▸ v⟩],()) := rfl

theorem receipt_lift_return (x : A) (fuel : Nat) :
    (liftM (ok x) : RecordedJob N A).receipt fuel = ok ([],x) := by
  change (Aeneas.Std.bind (ok x) _) = _
  simp only [bind_ok]

theorem receipt_set_then (r : Physical N T) (v : T) (d : core.fmt.Debug T) (msg : Str)
    (next : Unit → RecordedJob N B) (fuel : Nat) :
    (checkedSet r v d msg >>= next).receipt fuel =
      (do let (ws,b) ← (next ()).receipt fuel; ok (⟨r.key,r.payloadType.symm ▸ v⟩::ws,b)) := by
  change Aeneas.Std.bind (ok (_,())) _ = _
  simp [bind_ok]

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

private def StableLoop (body : A → RecordedJob N (ControlFlow A B)) (a : A) (b : B) : Prop :=
  ∃ ws bound, ∀ budget ≥ bound, ∀ depth ≥ bound,
    loopReceipt body budget depth a = ok (ws,b)

private theorem loop_complete (body : A → RecordedJob N (ControlFlow A B)) (a : A) :
    ReturnsWith (runLoop (fun x => (body x).live.raw) a) (StableLoop body a) := by
  let f := fun x => do
    match ← (body x).live.raw with
    | cont x' => return Sum.inl x'
    | done b => return Sum.inr b
  suffices all : ∀ x, ReturnsWith (ITree.iter f x) (StableLoop body x) from all a
  apply ITree.iter.fixpoint_induct f (fun g => ∀ x, ReturnsWith (g x) (StableLoop body x))
  · exact Lean.Order.admissible_pi_apply _ (fun x => DWLP.admissible (writeSemantics N) _ ())
  · intro g ih x
    change ReturnsWith (((body x).live.raw >>= _) >>= _) _
    rw [bind_assoc]
    apply DWLP.bind (body x).complete
    intro flow _ event
    obtain ⟨xs,n,hx⟩ := event
    cases flow with
    | done b =>
      simp only [pure_bind]
      apply DWLP.ret_iff.mpr
      refine ⟨xs,n+1,?_⟩
      intro budget enough depth more
      cases depth with
      | zero => omega
      | succ depth => simp [loopReceipt,hx budget (by omega)]
    | cont y =>
      simp only [pure_bind]
      apply DWLP.mono (ih y)
      intro b _ more
      obtain ⟨ys,m,hy⟩ := more
      refine ⟨xs++ys,max n m+1,?_⟩
      intro budget enough depth more
      cases depth with
      | zero => omega
      | succ depth => simp [loopReceipt,hx budget (by omega),hy budget (by omega) depth (by omega)]

def loop (body : A → RecordedJob N (ControlFlow A B)) (a : A) : RecordedJob N B where
  live := ParallelWorkerCounterSafety.loop (fun a => (body a).live) a
  receipt := fun budget => loopReceipt body budget budget a
  complete := by
    apply DWLP.mono (loop_complete body a)
    intro b _ h
    obtain ⟨ws,bound,proof⟩ := h
    exact ⟨ws,bound,fun fuel enough => proof fuel enough fuel enough⟩
  sound fuel ws b eq := loop_sound body fuel fuel a ws b eq

/-- Closed write-list formula for a generated Rust range loop. An iteration
may emit a whole nested loop's writes, with a common lower bound on its fuel. -/
theorem range_receipt {N ty} (body : core.ops.range.Range (UScalar ty) →
    RecordedJob N (ControlFlow (core.ops.range.Range (UScalar ty)) Unit))
    (limit : UScalar ty) (emit : Nat → List (Publication N)) (bound : Nat)
    (step : ∀ (it : core.ops.range.Range (UScalar ty)), it.end=limit → it.start.val<limit.val →
      ∃ next : core.ops.range.Range (UScalar ty), next.start.val=it.start.val+1 ∧ next.end=limit ∧
        ∀ fuel ≥ bound, (body it).receipt fuel = ok (emit it.start.val,cont next))
    (done : ∀ (it : core.ops.range.Range (UScalar ty)), it.end=limit → limit.val ≤ it.start.val →
      ∀ fuel ≥ bound, (body it).receipt fuel = ok ([],ControlFlow.done ()))
    (it : core.ops.range.Range (UScalar ty)) (stop : it.end=limit) (fuel : Nat)
    (enough : limit.val-it.start.val < fuel) (nested : bound ≤ fuel) :
    (loop body it).receipt fuel =
      ok ((List.range' it.start.val (limit.val-it.start.val)).flatMap emit,()) := by
  suffices all : ∀ depth (it : core.ops.range.Range (UScalar ty)), it.end=limit →
      limit.val-it.start.val < depth → loopReceipt body fuel depth it =
        ok ((List.range' it.start.val (limit.val-it.start.val)).flatMap emit,()) from all fuel it stop enough
  intro depth
  induction depth with
  | zero => intro it eq lt; omega
  | succ d ih =>
    intro cur same enough
    by_cases live : cur.start.val < limit.val
    · obtain ⟨next,inc,ends,run⟩ := step cur same live
      have rest := ih next ends (by omega)
      have len : limit.val-cur.start.val = (limit.val-next.start.val)+1 := by omega
      simp [loopReceipt,run fuel nested,rest,len,List.range'_succ,inc]
    · have exhausted : limit.val ≤ cur.start.val := by omega
      simp [loopReceipt,done cur same exhausted fuel nested,Nat.sub_eq_zero_of_le exhausted]

theorem receipt_bind (job : RecordedJob N A) (k : A → RecordedJob N B) (fuel : Nat) :
    (job >>= k).receipt fuel = (do
      let (xs,a) ← job.receipt fuel
      let (ys,b) ← (k a).receipt fuel
      ok (xs++ys,b)) := rfl

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

/-- A residual worker with no path to a normal return, whose only shared
effects are typed stores. Arbitrary code after the failed job is unreachable. -/
def Stalled (p : Program (Shared N) A) : Prop := ReturnsWith p (fun _ => False)

theorem RecordedJob.stalled_bind (job : RecordedJob N Unit) (missing : ¬ StableReceipt job.receipt ())
    (k : Unit → Program (Shared N) A) : Stalled (job.live.raw >>= k) := by
  apply DWLP.bind job.complete
  intro u _ possible
  exact (missing possible).elim

theorem Stalled.not_returned {p : Program (Shared N) A} (inv : Stalled p) (a : A) :
    p ≠ pure a := by
  intro equal
  subst p
  exact DWLP.ret_iff.mp inv

theorem Stalled.step {p q : Program (Shared N) A} {h h'} (inv : Stalled p)
    (step : Step h [p] h' [q]) :
    Stalled q ∧ h'.counts = h.counts ∧ h'.ready = h.ready ∧
    ∀ key v, h.cells key = some v → h'.cells key = some v := by
  obtain ⟨f,k,rfl,rfl,rfl⟩ := step.single_view
  obtain ⟨⟨w,rfl⟩,next⟩ := inv.vis_view
  refine ⟨next h,?_,?_,put_preserves w h⟩ <;> unfold put <;> split <;> rfl

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

private theorem observed_returns {N i h p peers dest final} {Q : Unit → Prop}
    (run : ParallelWorkerScatter.Observed (H:=Shared N) (fun _ _ => True) i h p peers dest final)
    (guarantee : ReturnsWith p Q) : Q () := by
  induction run with
  | returned => exact DWLP.ret_iff.mp guarantee
  | peer _ _ ih => exact ih guarantee
  | own _ step _ ih =>
    obtain ⟨_,_,rfl,_,rfl⟩ := step.single_view
    exact ih (guarantee.vis_view.2 _)

private theorem put_origin (w : Publication N) (h : Shared N) (key : Key) (value : Payload N key)
    (existsAfter : (put w.key w.value h).cells key = some value) :
    h.cells key = some value ∨ w = ⟨key,value⟩ := by
  rcases w with ⟨k,v⟩
  cases state : h.cells k with
  | some => exact Or.inl (by simpa [put,slot,state] using existsAfter)
  | none =>
    by_cases same : k = key
    · subst k
      have eq : v = value := by simpa [put,slot,state,read_after_write] using existsAfter
      exact Or.inr (by cases eq; rfl)
    · exact Or.inl (by simpa [put,slot,state,ParallelWorkerHeap.frame _ _ _ same] using existsAfter)

private theorem observed_origin {N i h p peers dest final}
    (run : ParallelWorkerScatter.Observed (H:=Shared N) (fun _ _ => True) i h p peers dest final)
    (alone : peers=[]) (ws : List (Publication N)) (shape : p=prepend ws (pure ())) :
    ∀ key value, dest.cells key = some value → h.cells key = some value ∨ ⟨key,value⟩ ∈ ws := by
  induction run generalizing ws with
  | returned => exact fun _ _ mem => Or.inl mem
  | peer move _ _ =>
    cases move with
    | atomic left => cases left <;> simp at alone
  | own _ step rest ih =>
    cases ws with
    | nil =>
      obtain ⟨_,_,eq,_,_⟩ := step.single_view
      rw [shape] at eq
      exact False.elim (not_vis_ret eq)
    | cons w ws =>
      rw [shape] at step
      obtain ⟨rfl,cont⟩ := step.unique_worker (first_step w ws _)
      split at cont
      · intro key value after
        rcases ih alone ws cont key value after with atStep|inRest
        · rcases put_origin w _ key value atStep with before|rfl
          · exact Or.inl before
          · exact Or.inr List.mem_cons_self
        · exact Or.inr (List.mem_cons_of_mem _ inRest)
      · exact False.elim (cannot_resume rest cont)

/-- An isolated execution on fresh cells gives the exact contents denoted by
the canonical write list. In particular an independently proved native slot
in the isolated result must be covered by that list. -/
theorem RecordedJob.solo_coverage {N dest} (job : RecordedJob N Unit)
    (run : Steps (fresh N) [job.live.raw] dest [pure ()]) :
    ∃ ws bound, (∀ fuel ≥ bound, job.receipt fuel = ok (ws,())) ∧
      ∀ key value, dest.cells key = some value ↔ ⟨key,value⟩ ∈ ws := by
  have observed := observeFromSteps run 0 _ _ rfl
  obtain ⟨ws,bound,evaluate⟩ := observed_returns observed job.complete
  have shape := job.sound bound ws () (evaluate bound (by omega))
  have origin := observed_origin observed rfl ws shape
  have publishes := (observed_writes observed ws shape (by intro p mem; simp at mem)).2
  refine ⟨ws,bound,evaluate,fun key value => ⟨?_,?_⟩⟩
  · intro full
    rcases origin key value full with impossible|member
    · contradiction
    · exact member
  · exact publishes ⟨key,value⟩

theorem StableReceipt.solo_membership {N dest} {job : RecordedJob N Unit}
    (s : StableReceipt job.receipt ())
    (run : Steps (fresh N) [job.live.raw] dest [pure ()]) (key : Key) (v : Payload N key) :
    ⟨key,v⟩ ∈ s.choose ↔ dest.cells key = some v := by
  obtain ⟨ws,n,eval,exactCoverage⟩ := job.solo_coverage run
  obtain ⟨m,selected⟩ := s.choose_spec
  rw [StableReceipt.unique selected eval]
  exact (exactCoverage key v).symm

theorem RecordedJob.return_receipt {N h peers dest final} (job : RecordedJob N Unit)
    (run : Steps h (job.live.raw::peers) dest (pure ()::final)) :
    StableReceipt job.receipt () :=
  observed_returns (observeFromSteps run 0 _ _ rfl) job.complete

theorem RecordedJob.completed {N h peers dest final} (job : RecordedJob N Unit) (fuel : Nat)
    (writes : List (Publication N)) (receipt : job.receipt fuel = ok (writes,()))
    (safe : All peers)
    (run : Steps h (job.live.raw::peers) dest (pure ()::final)) :
    ∀ w ∈ writes, dest.cells w.key = some w.value :=
  (observed_writes (observeFromSteps run 0 _ _ rfl) writes (job.sound fuel _ _ receipt) safe).2

/-- Every normal schedule determines the same finite, input-derived writes.
The budget only controls evaluation; every sufficiently large budget returns
the complete list, whose typed values the completed job has published. -/
theorem RecordedJob.completed_writes {N h peers dest final} (job : RecordedJob N Unit)
    (safe : All peers) (run : Steps h (job.live.raw::peers) dest (pure ()::final)) :
    ∃ ws bound, (∀ fuel ≥ bound, job.receipt fuel = ok (ws,())) ∧
      ∀ w ∈ ws, dest.cells w.key = some w.value := by
  obtain ⟨ws,bound,evaluate⟩ := job.return_receipt run
  exact ⟨ws,bound,evaluate,job.completed bound ws (evaluate bound (by omega)) safe run⟩

end ParallelDispatchWrites
