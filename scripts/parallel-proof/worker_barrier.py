"""Check phase observations on every normal path through the production wait MIR."""

import re
from collections import deque

PHASES = {
    "PHASE1_RUNNING": "running",
    "PHASE2_READY": "ready",
    "PHASE_ABORTED": "aborted",
}


def classify(lines):
    body = "\n".join(lines)
    if "Atomic::<u8>::load" in body:
        load = re.fullmatch(
            r"(v\d+) = core::sync::atomic::Ordering::Acquire;\n"
            r"v(\d+) = Atomic::<u8>::load\(arg \$phase2_state, move \1\) -> \[return: target\];",
            body,
        )
        if not load:
            raise ValueError(
                "phase observation is no longer an acquire on phase2_state"
            )
        return ("acquire", int(load[2]))
    if "const shake::slh::parallel::PHASE" in body:
        test = re.fullmatch(
            r"(v\d+) = (Eq|Ne)\((?:copy|move) v(\d+), const shake::slh::parallel::(PHASE\w+)\);\n"
            r"switchInt\(move \1\) -> \[0: target, otherwise: target\];",
            body,
        )
        if not test:
            raise ValueError("unknown phase predicate or switch convention")
        return ("compare", int(test[3]), PHASES[test[4]], test[2] == "Eq")
    return {("ready;",): ("accept",), ("aborted;",): ("reject",)}.get(
        tuple(lines), ("other",)
    )


def outcomes(op, seen, branch):
    if op[0] == "acquire":
        return [(op[1], phase) for phase in PHASES.values()]
    if (
        op[0] == "compare"
        and seen is not None
        and seen[0] == op[1]
        and int((seen[1] == op[2]) == op[3]) != branch
    ):
        return []
    return [seen]


def lean_op(op):
    if op[0] == "compare":
        return f".compare {op[1]} .{op[2]} {str(op[3]).lower()}"
    if op[0] == "acquire":
        return f".acquire {op[1]}"
    return "." + op[0]


def witness(graph):
    # Same label dictionary as graph_witness. Individual statements of an
    # unclassified block may not clobber any observed register.
    alphabet = dict.fromkeys(tuple(lines) for lines, _ in graph)
    decoded = {lines: classify(lines) for lines in alphabet}
    registers = {op[1] for op in decoded.values() if op[0] == "acquire"}
    for lines, _ in graph:
        for line in lines:
            assign = re.match(r"v(\d+) = ", line)
            if (
                assign
                and int(assign[1]) in registers
                and decoded[tuple(lines)][0] != "acquire"
            ):
                raise ValueError("wait MIR overwrites an observed register")
    if not any(op[0] == "accept" for op in decoded.values()):
        raise ValueError("wait has no successful return")
    facts = [[] for _ in graph]
    facts[0].append(None)
    pending = deque([(0, None)])
    while pending:
        pc, old = pending.popleft()
        lines, edges = graph[pc]
        for edge, dest in enumerate(edges):
            for after in outcomes(decoded[tuple(lines)], old, edge):
                if after not in facts[dest]:
                    facts[dest].append(after)
                    pending.append((dest, after))
    passing = [
        row
        for (lines, _), row in zip(graph, facts)
        if decoded[tuple(lines)][0] == "accept"
    ]
    if not all(row and all(x and x[1] == "ready" for x in row) for row in passing):
        raise ValueError("successful wait reachable without acquiring READY")
    ops = "\n".join(
        f"  | {i} => {lean_op(op)}" for i, op in enumerate(decoded.values())
    )
    rows = [
        "["
        + ",".join("none" if x is None else f"some ({x[0]},.{x[1]})" for x in row)
        + "]"
        for row in facts
    ]
    return f"""
open slhdsa.WorkerBarrierMir
private def waitMeaning : Nat → Op
{ops}
  | _ => .other
private def waitFacts : Facts := [{",".join(rows)}]
set_option maxRecDepth 16384 in
private theorem waitChecked : Certified waitProd waitMeaning waitFacts := by decide
theorem wait_acquires_ready {{pc seen}} (r : Trace waitProd waitMeaning pc seen)
    (h : pc < waitProd.length) (ok : waitMeaning waitProd[pc].ops = .accept) :
    isReady seen = true := accepts_after_ready waitChecked r h ok
theorem wait_reads_installed {{F A R : Type}} {{f : F}} {{a : A}} {{r : R}} {{h pc seen}}
    (run : Interleaved f a r waitProd waitMeaning h pc seen)
    (within : pc < waitProd.length) (ok : waitMeaning waitProd[pc].ops = .accept) :
    h.cells = ⟨some f,some a,some r⟩ := accepts_installed waitChecked run within ok
theorem wait_passes {{F A R : Type}} (f : F) (a : A) (r : R) :
    ∃ h seen, Interleaved f a r waitProd waitMeaning h 4 seen ∧
      waitMeaning waitProd[4].ops = .accept ∧ h.cells = ⟨some f,some a,some r⟩ := by
  obtain ⟨h,heap,published⟩ := slhdsa.WorkerBarrier.can_publish f a r
  have begin_ := Interleaved.on_published_heap waitProd waitMeaning heap
  have loaded : Interleaved f a r waitProd waitMeaning h 1 none :=
    .block begin_ (by decide) ⟨0,by decide⟩ (by decide) (by intro _ obs; cases obs)
  have tested : Interleaved f a r waitProd waitMeaning h 2 (some (2,.ready)) :=
    .block loaded (by decide) ⟨0,by decide⟩ (by decide) (by intro _ _ _; rw [published]; rfl)
  have passed : Interleaved f a r waitProd waitMeaning h 4 (some (2,.ready)) :=
    .block tested (by decide) ⟨1,by decide⟩ (by decide) (by intro _ obs; cases obs)
  exact ⟨_,_,passed,rfl,wait_reads_installed passed (by decide) rfl⟩
theorem wait_accepts_values (N : Aeneas.Std.Usize) :
    slhdsa.WorkerPayload.Accepting N waitProd waitMeaning := by
  intro f a r
  obtain ⟨h,seen,exec,ok,_⟩ := wait_passes f a r
  exact ⟨h,4,seen,exec,by decide,ok⟩

theorem wait_native_signature (N : Aeneas.Std.Usize) :
    type_of% (slhdsa.WorkerPayload.native_signature waitChecked (wait_accepts_values N)) :=
  slhdsa.WorkerPayload.native_signature waitChecked (wait_accepts_values N)

#print axioms wait_accepts_values
#print axioms wait_native_signature
open ParallelWorkerHeap slhdsa in
theorem wait_to_wots_heap {{N : Aeneas.Std.Usize}} (base : ParallelWorkerHeap.Heap N)
    {{f a r}} {{h : Monitor N}} {{pc seen}}
    (exec : Interleaved f a r waitProd waitMeaning h pc seen)
    (valid : pc < waitProd.length) (ok : waitMeaning waitProd[pc].ops = .accept)
    (fc : base.cells .sigFors = none) (ac : base.cells .xmssAuth = none)
    (rc : base.cells .roots = none) (zero : base.counts .phase2Next = 0)
    (fresh : ∀ j, base.cells (.wotsSigs j) = none) {{jobs workers m log}}
    (run : WorkerPayload.Execution jobs workers m log) :
    let joined := wotsHeap (barrierHeap base h) m
    Relation.ReflTransGen BarrierAction base (barrierHeap base h) ∧
    Relation.ReflTransGen WotsAction (barrierHeap base h) joined ∧
    joined.cells .sigFors = some f ∧ joined.cells .xmssAuth = some a ∧
    joined.cells .roots = some r ∧ ∀ j, joined.cells (.wotsSigs j) = m.cells j :=
  wait_to_wots base waitChecked exec valid ok fc ac rc zero fresh run
open ParallelWorkerHeap ParallelWorkerInterleave ParallelWorkerRuntime slhdsa in
theorem wait_runtime {{N : Aeneas.Std.Usize}} (base : ParallelWorkerHeap.Heap N)
    {{f a r}} {{h : Monitor N}} {{pc seen}}
    (exec : Interleaved f a r waitProd waitMeaning h pc seen)
    (valid : pc < waitProd.length) (ok : waitMeaning waitProd[pc].ops = .accept)
    {{B : Type}} (k : Bool → Program (Shared N) B) (l rt : List (Program (Shared N) B)) :
    let runtime : Shared N := ⟨barrierHeap base h,h.writer.released⟩
    Step runtime (l ++ (waitReady >>= k) :: rt) runtime (l ++ k true :: rt) ∧
    runtime.cells .sigFors = some f ∧ runtime.cells .xmssAuth = some a ∧ runtime.cells .roots = some r :=
  wait_runtime_step base waitChecked exec valid ok k l rt
#print axioms wait_runtime
#print axioms wait_to_wots_heap
#print axioms wait_passes
#print axioms wait_acquires_ready
#print axioms wait_reads_installed
"""


def check_writer(graph, region):
    """Check the order of the monitor's sender effects on *every* returning branch."""
    if region == "reduce":
        sites = (
            ("OnceLock", "::set(arg $sig_fors_cell,"),
            ("OnceLock", "::set(arg $xmss_auth_cell,"),
            ("OnceLock", "::set(arg $roots_cell,"),
        )
    elif region == "publish":
        # Resolve the guard produced by recovering this lock result and the
        # ordering operand consumed by the release, rather than accepting a
        # drop of any temporary or an unused Release constant.
        text = "\n".join(line for ops, _ in graph for line in ops)
        locks = re.findall(
            r"(v\d+) = std::sync::Mutex::<\(\)>::lock\(arg \$phase2_lock\)", text
        )
        if len(locks) != 1:
            raise ValueError("publish: expected the phase mutex acquisition")
        guard = re.findall(
            rf"(v\d+) = Result::<[^\n]*>::unwrap_or_else::<callback\d+>\(move {locks[0]},",
            text,
        )
        release = re.findall(
            r"(v\d+) = core::sync::atomic::Ordering::Release;\n"
            r"v\d+ = Atomic::<u8>::store\(arg \$phase2_state, const shake::slh::parallel::PHASE2_READY, move \1\)",
            text,
        )
        if len(guard) != 1 or len(release) != 1:
            raise ValueError(
                "publish: expected the mutex guard and READY release operand"
            )
        sites = (
            ("std::sync::Mutex", "::lock(arg $phase2_lock)"),
            (f"PHASE2_READY, move {release[0]})",),
            ("std::sync::Condvar::notify_all(arg $phase2_cv)",),
            (f"drop({guard[0]})",),
        )
    else:
        raise ValueError(region)
    alphabet = dict.fromkeys(tuple(lines) for lines, _ in graph)
    meaning = {}
    for ops in alphabet:
        matching = [
            i
            for i, words in enumerate(sites)
            if all(w in "\n".join(ops) for w in words)
        ]
        if len(matching) > 1:
            raise ValueError(f"{region}: ambiguous sender block {ops}")
        meaning[ops] = matching[0] if matching else None
    queue = deque([(0, 0)])
    visited = set()
    returned = False
    while queue:
        pc, stage = queue.popleft()
        if (pc, stage) in visited:
            continue
        visited.add((pc, stage))
        ops, edges = graph[pc]
        tag = meaning[tuple(ops)]
        if tag is not None:
            if stage != tag:
                raise ValueError(
                    f"{region}: sender effect {tag} reached after {stage} effects"
                )
            stage += 1
        if ops == ["return;"]:
            if stage != len(sites):
                raise ValueError(f"{region}: return bypasses sender effects")
            returned = True
        queue.extend((nxt, stage) for nxt in edges)
    if not returned:
        raise ValueError(f"{region}: no reachable normal return")
    facts = [[] for _ in graph]
    for pc, stage in sorted(visited):
        facts[pc].append(list(reversed(range(stage))))
    meanings = []
    for i, (ops, tag) in enumerate(meaning.items()):
        op = (
            f".effect {tag}"
            if tag is not None
            else ".finish"
            if ops == ("return;",)
            else ".other"
        )
        meanings.append(f"  | {i} => {op}")
    cases = "\n".join(meanings)
    order = list(range(len(sites)))
    return f"""
open slhdsa.WorkerBarrierMir in
private def {region}Sender : Nat → SenderOp
{cases}
  | _ => .other
open slhdsa.WorkerBarrierMir in
theorem {region}_sender_order {{pc prior}} (run : SenderTrace {region}Prod {region}Sender pc prior)
    (h : pc < {region}Prod.length) (ok : {region}Sender {region}Prod[pc].ops = .finish) :
    prior.reverse = {order} :=
  sender_returns (facts := {facts}) (by decide) run h ok
#print axioms {region}_sender_order
"""


def pool_witness(generated):
    """Apply the pool job/borrow proof to this extraction's concrete callback."""
    header = generated.split("def shake.slh.parallel.flat_worker\n", 1)[1]
    immutable_params = header.split("  (xmss_slots :", 1)[0]
    arguments = " ".join(re.findall(r"\((\w+) :", immutable_params))
    if not arguments.endswith("xmss_meta fors_split_meta"):
        raise ValueError("pool callback: unexpected immutable captures")
    return f"""
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std ParallelWorkerRuntime ParallelWorkerInterleave ParallelWorkerPool
open ParallelPool.Borrow ParallelPool.Lease

theorem signing_pool_first_fetch
{immutable_params}  (xmssCount leafCount directCount splitCount wotsCount : Std.Usize)
    (epochs : (e : Nat) → Epoch e) (co : Coherent epochs) (object : Nat → Object) (e : Nat)
    (source : Fin (epochs e).workers → Option Write)
    (visible : ∀ w : Fin (epochs e).workers, Visible epochs (.copyJob e w) (source w))
    (worker : Fin ((epochs e).workers + 1)) (h : Shared N) :
    let callback := signingCallback {arguments} xmssCount leafCount directCount splitCount wotsCount
    ∃ l right after, l.length = worker.val ∧
      participants object e (epochs e).workers callback source = some (l ++ callback :: right) ∧
      Step h (l ++ callback :: right) (increment h .phase1Next 1#usize) (l ++ after :: right) ∧
      ∀ w : Fin (epochs e).workers, HB epochs (.useClosure e w) (.endBorrow e) := by
  intro callback
  let l := List.replicate worker.val callback
  let rt := List.replicate ((epochs e).workers - worker.val) callback
  have split : List.replicate ((epochs e).workers + 1) callback = l ++ callback :: rt := by
    dsimp [l,rt]
    rw [← List.replicate_succ, ← List.replicate_add]
    congr 1
    have bound := worker.isLt
    omega
  obtain ⟨after, step⟩ := callback_first_fetch {arguments} xmssCount leafCount directCount
    splitCount wotsCount h l rt
  refine ⟨l,rt,after,by simp [l],(exact_callbacks epochs co object e callback source visible).trans
    (congrArg some split),step,?_⟩
  intro w
  exact (dispatched_closure epochs co object e w w.isLt (source w) (visible w) 0).2.1

end slhdsa.WorkerEffects
"""


def certified_phase1_witness(generated):
    """Identify the canonical callback's entire phase-one control tree with its job plan."""
    header = generated.split("def shake.slh.parallel.flat_worker_loop.body\n", 1)[1]
    immutable = header.split("  (xmss_slots :", 1)[0]
    operands = " ".join(re.findall(r"\((\w+) :", immutable))
    if not operands.endswith("xmss_meta fors_split_meta"):
        raise ValueError("unexpected phase-one closure parameters")
    tables = "xmss_slots leaf_pks fors_direct fors_split"
    outputs = "sig_fors_cell xmss_auth_cell roots_cell"
    params = (
        immutable
        + """
  (xmss_slots leaf_pks fors_direct fors_split : alloc.vec.Vec (Physical N (Array Std.U8 N)))
  (sig_fors_cell : Physical N (alloc.vec.Vec Std.U8))
  (xmss_auth_cell roots_cell : Physical N (alloc.vec.Vec (Array Std.U8 N)))"""
    )
    program = f"(certifiedOps N) (certifiedSync N) {operands} {tables} .phase1Next .phase1Done () () () {outputs}"
    plan = f"certifiedPlan {operands} {tables} {outputs}"
    return f"""
namespace slhdsa.WorkerEffects
open Aeneas Aeneas.Std Result ControlFlow ParallelWorkerHeap ParallelWorkerRuntime
open ParallelWorkerInterleave ParallelWorkerCounterSafety ParallelPhaseOne
noncomputable section
def certifiedPlan
{params} : Plan N shake.slh.parallel.WorkItem where
  jobs := jobs
  total := total_phase1
  dispatch := fun job => (interpreted.dispatch (certifiedOps N) fors_stride a fors_addr sk seed layers
    fors_indices {tables} job).raw
  reduce := (interpreted.reduce (certifiedOps N) d hp leaf_pk_count fors_stride fors_addr p md seed layers
    xmss_meta fors_split_meta {tables} {outputs}).raw

theorem certified_phase1_body
{params} : (interpreted.flat_worker_loop.body {program}).raw = ({plan}).body := by
  unfold interpreted.flat_worker_loop.body Plan.body
  simp only [raw_bind,raw_lift,certifiedSync,ite_true,unitFetch]
  congr 1
  funext i
  simp only [core.slice.Slice.get,core.slice.index.Usize.get,Slice.getElem?_Usize_eq,
    alloc.vec.Vec.deref,Slice.from_val,lifted_ok,pure_bind,certifiedPlan]
  cases chosen : jobs.val[i.val]? with
  | none => rfl
  | some item =>
    simp only [raw_bind,raw_lift,Plan.finished,certifiedPlan]
    congr 1
    funext u
    cases u
    congr 1
    funext old
    congr 1
    funext newCount
    split <;> rfl

theorem certified_phase1_loop
{params} : (interpreted.flat_worker_loop {program}).raw = ({plan}).worker := by
  unfold interpreted.flat_worker_loop Plan.worker
  change runLoop (fun () => _) () = runLoop (fun () => _) ()
  congr 1
  funext u
  cases u
  exact certified_phase1_body {operands} {tables} {outputs}

end
end slhdsa.WorkerEffects
"""
