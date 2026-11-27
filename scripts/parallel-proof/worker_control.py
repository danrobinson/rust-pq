"""Check the extracted full worker with one effect interface shared across both phases."""

import re

from worker_effects import CELL, PREFIX

COUNTER = r"core\.sync\.atomic\.Atomic Std\.Usize\s+\(core\.sync\.atomic\.private\.Align8 Std\.Usize\)"
PHASE = r"core\.sync\.atomic\.Atomic Std\.U8\s+\(core\.sync\.atomic\.private\.Align1 Std\.U8\)"
MUTEX = "std.sync.poison.mutex.Mutex Unit"
CONDVAR = "std.sync.poison.condvar.Condvar"
FAMILIES = ("flat_worker", "phase_two")


def control_witness(generated):
    source = """
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
structure Sync (Count Phase Lock Cv : Type) (M : Type → Type) where
  fetch : Count → Std.Usize → core.sync.atomic.Ordering → M Std.Usize
  wait : Phase → Lock → Cv → M Bool
  publish : Phase → Lock → Cv → M Unit

def extractedSync := Sync.mk core.sync.atomic.AtomicUsizeAlign8Usize.fetch_add
  shake.slh.parallel.wait shake.slh.parallel.publish
"""
    pattern = re.compile(
        r"^def shake\.slh\.parallel\.((?:phase_two|flat_worker)(?:_loop\d*)?(?:\.body)?)\n"
        r"(.*?)\n  := do\n(.*?)(?=\n\n|\Z)",
        re.MULTILINE | re.DOTALL,
    )
    matches = pattern.findall(generated)
    expected = {
        base + suffix for base in FAMILIES for suffix in ("", "_loop", "_loop.body")
    }
    if {name for name, _, _ in matches} != expected or len(matches) != len(expected):
        raise ValueError("unexpected worker entry or loop names")
    ref = re.compile(
        re.escape(PREFIX)
        + "("
        + "|".join(
            map(
                re.escape,
                sorted(expected | {"dispatch", "reduce"}, key=len, reverse=True),
            )
        )
        + r")(?![\w.])"
    )
    proofs = []
    for name, sig, body in matches:
        params, ret = sig.rsplit(" :\n  Result ", 1)
        generalized = (
            re.sub(COUNTER, "Count", re.sub(PHASE, "Phase", params))
            .replace(MUTEX, "Lock")
            .replace(CONDVAR, "Cv")
            .replace(CELL, "Cell")
        )
        deps = list(dict.fromkeys(m[1] for m in ref.finditer(body)))
        body = ref.sub(
            lambda m: (
                "interpreted." + m[1] + (" ops sync" if m[1] in expected else " ops")
            ),
            body,
        )
        body = (
            body.replace(CELL + ".set", "ops.set")
            .replace(CELL + ".get", "ops.get")
            .replace(CELL, "Cell")
        )
        body = body.replace(
            "core.sync.atomic.AtomicUsizeAlign8Usize.fetch_add", "sync.fetch"
        )
        body = body.replace(PREFIX + "publish", "sync.publish").replace(
            PREFIX + "wait", "sync.wait"
        )
        body = re.sub(r"(?m)^  loop$", "  ops.runLoop", body)
        source += f"""
def interpreted.{name} {{Cell M : Type → Type}} [Monad M] [MonadLiftT Result M]
    {{Count Phase Lock Cv : Type}} (ops : Ops Cell M) (sync : Sync Count Phase Lock Cv M)
{generalized} :
  M {ret}
  := do
{body}
"""
        args = " ".join(re.findall(r"\((\w+) :", params))
        ds = ", ".join(n.replace(".", "_") + "_extracted" for n in deps)
        proofs.append(f"""
theorem {name.replace(".", "_")}_extracted
{params} :
    interpreted.{name} extractedOps extractedSync {args} = {PREFIX}{name} {args} := by
  first | rfl | skip
  all_goals unfold interpreted.{name} {PREFIX}{name}
  all_goals try simp only [{ds}]
  all_goals first | rfl | (congr 1; funext i; congr 1; funext o; cases o <;> rfl)
""")
    return source + "".join(proofs) + "\nend\nend slhdsa.WorkerEffects\n"


def runtime_witness(generated):
    """Instantiate the complete callback including both queues and the reducer."""
    sig = generated.split("def " + PREFIX + "flat_worker\n", 1)[1].split(
        " :\n  Result Unit", 1
    )[0]
    params = sig.split("  (xmss_slots :", 1)[0]
    immutable = " ".join(re.findall(r"\((\w+) :", params))
    if not immutable.endswith("xmss_meta fors_split_meta"):
        raise ValueError("unexpected immutable worker arguments")
    increments = re.findall(
        r"AtomicUsizeAlign8Usize\.fetch_add (\w+) ([^\s]+)", generated
    )
    if sorted(increments) != [
        (c, "1#usize") for c in ("phase1_done", "phase1_next", "phase2_next")
    ]:
        raise ValueError(
            "the signing callback no longer issues exactly three unit increment sites"
        )
    return (
        f"""
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow ParallelWorkerRuntime ParallelWorkerHeap
open ParallelWorkerInterleave
noncomputable section

def concurrentSync (N : Std.Usize) : Sync Counter Unit Unit Unit (Program (Shared N)) where
  fetch := fun counter amount _ordering => rmw counter amount
  wait := fun _ _ _ => waitReady
  publish := fun _ _ _ => ParallelWorkerRuntime.publish

def certifiedOps (N : Std.Usize) :
    Ops (ParallelWorkerCounterSafety.Physical N) (ParallelWorkerCounterSafety.Certified N) where
  get := ParallelWorkerCounterSafety.get
  set := ParallelWorkerCounterSafety.set
  tree := fun refs seed addr root sub height => do
    let values ← refs.val.mapM ParallelWorkerCounterSafety.get
    if bound : values.length ≤ Std.Usize.max then
      liftM (shakeReduction (Slice.from values bound) seed addr root sub height)
    else liftM (fail .panic)
  runLoop := ParallelWorkerCounterSafety.loop

def certifiedSync (N : Std.Usize) :
    Sync Counter Unit Unit Unit (ParallelWorkerCounterSafety.Certified N) where
  fetch := fun c n _ => if n = 1#usize then ParallelWorkerCounterSafety.unitFetch c else liftM (fail .panic)
  wait := fun _ _ _ => ParallelWorkerCounterSafety.wait
  publish := fun _ _ _ => ParallelWorkerCounterSafety.publish

def certifiedCallback
{params}  (xmssCount leafCount directCount splitCount wotsCount : Std.Usize) : ParallelWorkerCounterSafety.Certified N Unit :=
  interpreted.flat_worker (certifiedOps N) (certifiedSync N) {immutable}
    (ParallelWorkerCounterSafety.physicalTable N Key.xmssSlots _ (fun _ => rfl) xmssCount)
    (ParallelWorkerCounterSafety.physicalTable N Key.leafPks _ (fun _ => rfl) leafCount)
    (ParallelWorkerCounterSafety.physicalTable N Key.forsDirect _ (fun _ => rfl) directCount)
    (ParallelWorkerCounterSafety.physicalTable N Key.forsSplit _ (fun _ => rfl) splitCount)
    .phase1Next .phase1Done .phase2Next () () ()
    (ParallelWorkerCounterSafety.physicalSlot N .sigFors) (ParallelWorkerCounterSafety.physicalSlot N .xmssAuth) (ParallelWorkerCounterSafety.physicalSlot N .roots)
    (ParallelWorkerCounterSafety.physicalTable N Key.wotsSigs _ (fun _ => rfl) wotsCount)

def signingCallback
{params}  (xmssCount leafCount directCount splitCount wotsCount : Std.Usize) : Program (Shared N) Unit :=
  (certifiedCallback {immutable} xmssCount leafCount directCount splitCount wotsCount).raw

theorem signing_callback_counters
{params}  (xmssCount leafCount directCount splitCount wotsCount : Std.Usize)
    (workers : Nat) (c : Counter) (initial final : Shared N) (out : List (Program (Shared N) Unit)) :
    let callback := signingCallback {immutable} xmssCount leafCount directCount splitCount wotsCount
    Steps initial (List.replicate workers callback) final out →
    ∃ log, ParallelWorkerCounterSafety.Recorded c (initial,List.replicate workers callback) (final,out) log ∧
      ParallelWorkerCounterSafety.All out ∧
      (initial.counts c + log.length < 2^System.Platform.numBits →
        final.counts c = initial.counts c + log.length ∧
        log = List.range' (initial.counts c) log.length ∧ log.Nodup) := by
  intro callback run
  apply ParallelWorkerCounterSafety.all_interleavings _ _ run
  intro t member
  have same := List.eq_of_mem_replicate member
  subst t
  exact (certifiedCallback {immutable} xmssCount leafCount directCount splitCount wotsCount).safe

theorem signing_callback_publications
{params}  (xmssCount leafCount directCount splitCount wotsCount : Std.Usize)
    (workers : Nat) (initial final : Shared N) (out : List (Program (Shared N) Unit)) :
    let callback := signingCallback {immutable} xmssCount leafCount directCount splitCount wotsCount
    Steps initial (List.replicate workers callback) final out →
      (initial.ready = true → final.ready = true) ∧
      ∀ (k : Key) (v : Payload N k), initial.cells k = some v → final.cells k = some v := by
  intro callback run
  apply ParallelWorkerCounterSafety.published_persists _ run
  intro t member
  have same := List.eq_of_mem_replicate member
  subst t
  exact (certifiedCallback {immutable} xmssCount leafCount directCount splitCount wotsCount).safe

theorem callback_first_fetch
{params}  (xmssCount leafCount directCount splitCount wotsCount : Std.Usize)
    (h : Shared N) (left right : List (Program (Shared N) Unit)) :
    ∃ after, Step h (left ++ signingCallback {immutable} xmssCount leafCount directCount splitCount wotsCount :: right)
      (increment h .phase1Next 1#usize) (left ++ after :: right) := by
  apply Starts.step
  unfold signingCallback certifiedCallback interpreted.flat_worker
  apply Starts.bind
  unfold interpreted.flat_worker_loop certifiedOps
  apply Starts.loop
  unfold interpreted.flat_worker_loop.body
  apply Starts.bind
  exact ⟨_,rfl⟩

end
end slhdsa.WorkerEffects
"""
        + WOTS
    )


WOTS = """
set_option backward.isDefEq.respectTransparency false
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow Error ParallelWorkerRuntime ParallelWorkerHeap
open ParallelWorkerInterleave
noncomputable section

/-- All native computations for successful tickets, including the layer
address construction and the host WOTS primitive. -/
def WotsValues {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8) : Prop :=
  ∀ j : Std.Usize, j.val < len.val → ∃ addr index root typed keyed,
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) layers j = ok (addr,index) ∧
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) roots j = ok root ∧
    address.Adrs.with_type addr address.WOTS_HASH = ok typed ∧
    address.Adrs.with_keypair typed index = ok keyed ∧
    shake.wots.wots_sign root sk seed keyed = ok (values j)

def wotsBody (N : Std.Usize) (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8) :
    Program (Shared N) (ControlFlow Unit Unit) := do
  let j ← rmw .phase2Next 1#usize
  if j.val < len.val then
    let cell : ParallelWorkerCells.Ref (Shared N) (alloc.vec.Vec Std.U8) := slot N (.wotsSigs j.val)
    let result ← ParallelWorkerInterleave.set cell (values j)
    let _ ← (liftM (core.result.Result.expect (core.fmt.DebugVec core.fmt.DebugU8) result
      (toStr "unique WOTS sign job")) : Program (Shared N) Unit)
    pure (cont ())
  else pure (done ())

theorem wots_body_eq {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8)
    (computes : WotsValues sk seed layers roots len values) :
    interpreted.phase_two_loop.body concurrentOps (concurrentSync N) sk seed layers .phase2Next
      (table N Key.wotsSigs _ (fun _ => rfl) len) roots = wotsBody N len values := by
  unfold interpreted.phase_two_loop.body wotsBody
  dsimp only [concurrentSync]
  congr 1
  funext j
  rw [wots_lookup]
  by_cases live : j.val < len.val
  · obtain ⟨a,i,r,t,k,layer,root,tag,key,sig⟩ := computes j live
    simp only [ite_eq_left live, lifted_ok, pure_bind, layer, root, tag, key, sig]
    rfl
  · simp only [ite_eq_right live, lifted_ok, pure_bind]

/-- Equality of whole interaction trees transfers every interleaving,
including failed stores and every counter value visible to a peer. -/
theorem wots_loop_eq {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8)
    (computes : WotsValues sk seed layers roots len values) :
    interpreted.phase_two_loop concurrentOps (concurrentSync N) sk seed layers .phase2Next
      (table N Key.wotsSigs _ (fun _ => rfl) len) roots =
    runLoop (fun () => wotsBody N len values) () := by
  unfold interpreted.phase_two_loop
  rw [wots_body_eq sk seed layers roots len values computes]
  rfl

theorem wots_worker_eq {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8)
    (computes : WotsValues sk seed layers roots len values) :
    interpreted.phase_two_loop concurrentOps (concurrentSync N) sk seed layers .phase2Next
      (table N Key.wotsSigs _ (fun _ => rfl) len) roots = Wots.worker N len values := by
  rw [wots_loop_eq sk seed layers roots len values computes]
  unfold Wots.worker
  congr 1
  funext u
  unfold wotsBody Wots.body
  congr 1
  funext j
  split
  · dsimp only
    congr 1
    funext r
    cases r with
    | Ok v => cases v; simp [core.result.Result.expect,lifted_ok,Bind.bind,Aeneas.Data.Coinductive.itree_ret_bind]
    | Err _ =>
      change (liftResult (H:=Shared N) (fail .panic : Result Unit) >>= _) = liftResult (fail .panic)
      simp [liftResult,Aeneas.Data.Coinductive.vis_bind]
      congr 1; funext o; exact PEmpty.elim o
  · rfl

open ParallelWorkerCounterSafety in
theorem certified_wots_body {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) :
    (interpreted.phase_two_loop.body (certifiedOps N) (certifiedSync N) sk seed layers .phase2Next
      (ParallelWorkerCounterSafety.physicalTable N Key.wotsSigs _ (fun _ => rfl) len) roots).raw =
    interpreted.phase_two_loop.body concurrentOps (concurrentSync N) sk seed layers .phase2Next
      (table N Key.wotsSigs _ (fun _ => rfl) len) roots := by
  unfold interpreted.phase_two_loop.body
  simp only [raw_bind, raw_lift, certifiedSync, concurrentSync, ite_true, unitFetch]
  congr 1
  funext j
  rw [physical_lookup,wots_lookup]
  by_cases live : j.val < len.val
  · simp only [ite_eq_left live, lifted_ok, pure_bind,raw_bind,raw_lift]
    congr 1
  · simp only [ite_eq_right live, lifted_ok, pure_bind,raw_lift]

theorem certified_wots_loop {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) :
    (interpreted.phase_two_loop (certifiedOps N) (certifiedSync N) sk seed layers .phase2Next
      (ParallelWorkerCounterSafety.physicalTable N Key.wotsSigs _ (fun _ => rfl) len) roots).raw =
    interpreted.phase_two_loop concurrentOps (concurrentSync N) sk seed layers .phase2Next
      (table N Key.wotsSigs _ (fun _ => rfl) len) roots := by
  unfold interpreted.phase_two_loop
  change runLoop (fun () => _) () = runLoop (fun () => _) ()
  congr 1
  funext u
  cases u
  exact certified_wots_body sk seed layers roots len

theorem all_wots_schedules {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8)
    (computes : WotsValues sk seed layers roots len values) (h h' : Shared N) (workers : Nat)
    (threads : List (Program (Shared N) Unit))
    (run : Steps h (List.replicate workers
      (interpreted.phase_two_loop concurrentOps (concurrentSync N) sk seed layers .phase2Next
        (table N Key.wotsSigs _ (fun _ => rfl) len) roots)) h' threads)
    (initial : Wots.Correct len values h) : Wots.Correct len values h' := by
  rw [wots_worker_eq sk seed layers roots len values computes] at run
  exact Wots.all_schedules values h h' workers threads run initial

/-- The continuation after a WOTS ticket has linearized keeps the returned
index while other workers run. Its sole shared action on a valid ticket is
the typed set at that index. -/
theorem wots_interleaving {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32))
    (roots : alloc.vec.Vec (Array Std.U8 N)) (len : Std.Usize)
    (h : Shared N) (left right : List (Program (Shared N) (ControlFlow Unit Unit))) :
    let slots := table N Key.wotsSigs _ (fun _ => rfl) len
    let j := oldTicket h .phase2Next
    ∃ continuation : Program (Shared N) (ControlFlow Unit Unit),
      Step h (left ++ interpreted.phase_two_loop.body concurrentOps (concurrentSync N)
        sk seed layers .phase2Next slots roots :: right)
        (increment h .phase2Next 1#usize) (left ++ continuation :: right) ∧
      (∀ addr index root typed keyed sig, j.val < len.val →
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) layers j = ok (addr,index) →
        alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) roots j = ok root →
        address.Adrs.with_type addr address.WOTS_HASH = ok typed →
        address.Adrs.with_keypair typed index = ok keyed →
        shake.wots.wots_sign root sk seed keyed = ok sig →
        ∀ (later : Shared N) (l r : List (Program (Shared N) (ControlFlow Unit Unit))),
        later.cells (.wotsSigs j.val) = none →
        Step later (l ++ continuation :: r) ((slot N (.wotsSigs j.val)).write sig later) (l ++ pure (cont ()) :: r)) ∧
      (len.val ≤ j.val →
        continuation = pure (done ())) := by
  intro slots j
  unfold interpreted.phase_two_loop.body
  refine ⟨_,rmw_step _ _ _ _ _ _,?_,?_⟩
  · intro addr index root typed keyed sig live layer source tag key signed later l r free
    let dest : ParallelWorkerCells.Ref (Shared N) (alloc.vec.Vec Std.U8) := slot N (.wotsSigs j.val)
    have found : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice _) slots.deref j = ok (some dest) := by
      simpa only [slots, dest, ite_eq_left live] using wots_lookup N len j
    change dest.read later = none at free
    have lifted {T : Type} (x : T) :
        (liftM (ok x) : Program (Shared N) T) = pure x := lift_ok x
    dsimp only
    dsimp only [j] at found layer source
    simp only [found, lifted, pure_bind, layer, source, tag, key, signed]
    simpa [concurrentOps, free, core.result.Result.expect, lifted, Bind.bind, Aeneas.Data.Coinductive.itree_ret_bind] using
      (set_step dest sig (fun v => do
        let _ ← (liftM (core.result.Result.expect (core.fmt.DebugVec core.fmt.DebugU8) v
          (toStr "unique WOTS sign job")) : Program (Shared N) Unit)
        pure (cont ())) later l r)
  · intro exhausted
    have missing : core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice _) slots.deref j = ok none := by
      simpa only [slots, ite_eq_right (Nat.not_lt.mpr exhausted)] using wots_lookup N len j
    have lifted {T : Type} (x : T) :
        (liftM (ok x) : Program (Shared N) T) = pure x := lift_ok x
    dsimp only
    dsimp only [j] at missing
    simp only [missing, lifted, pure_bind]
end
end slhdsa.WorkerEffects
"""


def completion_witness():
    return """
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow ParallelWorkerRuntime ParallelWorkerHeap ParallelWorkerInterleave
noncomputable section
theorem completed_wots_schedules {N : Std.Usize} (sk seed : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (roots : alloc.vec.Vec (Array Std.U8 N))
    (len : Std.Usize) (values : Std.Usize → alloc.vec.Vec Std.U8)
    (computes : WotsValues sk seed layers roots len values) (h h' : Shared N) (workers : Nat)
    (positive : 0 < workers) (capacity : len.val+workers < 2^UScalarTy.Usize.numBits)
    (threads : List (Program (Shared N) Unit))
    (run : Steps h (List.replicate workers
      ((interpreted.phase_two_loop (certifiedOps N) (certifiedSync N) sk seed layers .phase2Next
        (ParallelWorkerCounterSafety.physicalTable N Key.wotsSigs _ (fun _ => rfl) len) roots).raw)) h' threads)
    (initial : h.counts .phase2Next = 0) (fresh : ∀ i, h.cells (.wotsSigs i) = none)
    (retired : ∀ w ∈ threads, w = pure ()) :
    ∀ j : Std.Usize, j.val<len.val → h'.cells (.wotsSigs j.val) = some (values j) := by
  rw [certified_wots_loop, wots_worker_eq sk seed layers roots len values computes] at run
  obtain ⟨_,_,_,_,published⟩ := Wots.joined values workers positive capacity h h' initial fresh threads run retired
  exact published

end
end slhdsa.WorkerEffects
"""
