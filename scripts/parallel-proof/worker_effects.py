"""Generate Lean equations for the shared effects of extracted dispatch and reduction."""

import re
from pathlib import Path

from worker_lane_effects import simd_lane_witness
from worker_scalar_effects import scalar_witness

PREFIX = "shake.slh.parallel."
CELL = "std.sync.once_lock.OnceLock"
FUNCTIONS = re.compile(
    r"^def shake\.slh\.parallel\.((?:reduce|dispatch)(?:_loop\d+)*(?:\.body)?)\n"
    r"(.*?)\n  := do\n(.*?)(?=\n\n|\Z)",
    re.MULTILINE | re.DOTALL,
)

PREAMBLE = """
open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
noncomputable section
namespace slhdsa.WorkerEffects
open slhdsa

structure Ops (Cell M : Type → Type) where
  get : {T : Type} → Cell T → M (Option T)
  set : {T : Type} → Cell T → T → M (core.result.Result Unit T)
  tree : {N : Std.Usize} → Slice (Cell (Array Std.U8 N)) → Array Std.U8 N →
    address.Adrs → Std.U32 → Std.U32 → Std.U32 → M (Array Std.U8 N)
  runLoop : {A B : Type} → (A → M (ControlFlow A B)) → A → M B

/-- The Rust reducer ignores the return values of these three publications. -/
def publishOutputs {Cell M : Type → Type} [Monad M] (ops : Ops Cell M) {A B C : Type}
    (sig : Cell A) (auth : Cell B) (roots : Cell C) (x : A) (y : B) (z : C) : M Unit := do
  let _ ← ops.set sig x
  let _ ← ops.set auth y
  let _ ← ops.set roots z
  pure ()

def extractedOps : Ops std.sync.once_lock.OnceLock Result where
  get := std.sync.once_lock.OnceLock.get
  set := std.sync.once_lock.OnceLock.set
  tree := shake.slh.parallel.reduce_tree
  runLoop := loop
"""


def effects_witness(generated, package_name):
    matches = FUNCTIONS.findall(generated)
    names = [name for name, _, _ in matches]
    # Every local loop, including both the inner and outer SIMD loops, must
    # participate. Top-level equalities below check the full transitive body.
    required = {"dispatch", "reduce"}
    for root, suffixes in (
        ("reduce", ("0", "1", "2_loop0", "2", "3_loop0", "3")),
        ("dispatch", ("0", "1", "2_loop0", "2", "3", "4")),
    ):
        for suffix in suffixes:
            loop = root + "_loop" + suffix
            required.update((loop, loop + ".body"))
    if set(names) != required or len(names) != len(required):
        raise ValueError(
            f"unexpected extracted worker loops: {required.symmetric_difference(names)}"
        )
    reference = re.compile(
        re.escape(PREFIX)
        + "("
        + "|".join(map(re.escape, sorted(names, key=len, reverse=True)))
        + r")(?![\w.])"
    )
    statements = []
    proofs = []
    for name, sig, body in matches:
        original_body = body
        params, ty = sig.rsplit(" :\n  Result ", 1)
        # Retain Aeneas's emitted control flow, indexing, arithmetic, scalars,
        # error handling and pure helper calls. Replace only cell representation,
        # effect operations, recursion driver, and calls to sibling definitions.
        body = reference.sub(lambda m: "interpreted." + m[1] + " ops", body)
        body = body.replace(CELL + ".set", "ops.set").replace(CELL + ".get", "ops.get")
        body = body.replace(PREFIX + "reduce_tree", "ops.tree").replace(CELL, "Cell")
        # Keep the conditional inside one bind. Otherwise Lean distributes
        # its continuation into both branches of this generated expression.
        body = body.replace("←\n      if ", "← id <|\n      if ")
        body = re.sub(r"(?m)^  loop$", "  ops.runLoop", body)
        if name == "reduce":
            stores = (
                "  let _ ← ops.set sig_fors_cell sig_fors1\n"
                "  let _ ← ops.set xmss_auth_cell xmss_auth1\n"
                "  let _ ← ops.set roots_cell roots2\n"
                "  ok ()"
            )
            if not body.endswith(stores):
                raise ValueError("reducer publication tail changed")
            body = body[: -len(stores)] + (
                "  publishOutputs ops sig_fors_cell xmss_auth_cell roots_cell sig_fors1 xmss_auth1 roots2"
            )
        vars_ = re.findall(r"\((\w+) :", params)
        statements.append(
            f"def interpreted.{name} {{Cell M : Type → Type}} [Monad M] [MonadLiftT Result M]\n"
            f"  (ops : Ops Cell M)\n{params.replace(CELL, 'Cell')} :\n  M {ty.replace(CELL, 'Cell')}\n"
            f"  := do\n{body}\n"
        )
        args = " ".join(vars_)
        dependencies = [m[1] for m in reference.finditer(original_body)]
        simp = ", ".join(
            [d.replace(".", "_") + "_extracted" for d in dict.fromkeys(dependencies)]
        )
        proofs.append(
            f"theorem {name.replace('.', '_')}_extracted\n{params} :\n"
            f"    interpreted.{name} extractedOps {args} = {PREFIX}{name} {args}  := by\n"
            f"  first | rfl | skip\n  all_goals unfold interpreted.{name} {PREFIX}{name}\n"
            f"  all_goals try simp only [{simp}]\n"
            "  all_goals first | rfl | (congr 1; funext p; rcases p with ⟨o, iter⟩; cases o <;> rfl)\n"
        )
    # The staged package defines its own slhdsa.address.Adrs. Elaborate
    # the independently extraction-checked reducer in that environment.
    program = (
        Path(__file__).resolve().parents[2]
        / "lean-hw/Parallel/ReduceNativeProgram.lean"
    ).read_text()
    reducer = program[program.index("open Aeneas Aeneas.Std") :]
    return (
        f"import {package_name}.Funs\nimport Parallel.WorkerScatterHeap\nimport Parallel.WorkerScalarLow\nset_option linter.unusedVariables false\nset_option linter.concreteInstances false\n"
        + reducer
        + PREAMBLE
        + "\n".join(statements + proofs)
        + HEAP
        + simd_lane_witness(generated)
        + Path(__file__).with_name("worker-scalar-low.lean").read_text()
        + scalar_witness(generated)
        + "\nend slhdsa.WorkerEffects\n"
    )


HEAP = """
/-- The opaque tree helper sees the currently published input cells in slice
order. Its hash computation is a function of these values and its explicit
arguments. It has no reference to the shared heap. -/
abbrev ReduceValues := {N : Std.Usize} → Slice (Option (Array Std.U8 N)) →
  Array Std.U8 N → address.Adrs → Std.U32 → Std.U32 → Std.U32 → Result (Array Std.U8 N)

def heapOps {H : Type} (reduceValues : ReduceValues) :
    Ops (ParallelWorkerCells.Ref H) (StateT H Result) where
  get := ParallelWorkerCells.get
  set := ParallelWorkerCells.set
  tree := fun refs seed addr root sub height h => do
    let values := refs.val.map (fun ref => ref.read h)
    let input := Slice.from values (by simp [values])
    let out ← reduceValues input seed addr root sub height
    ok (out,h)
  runLoop := ParallelWorkerCells.runLoop

/-- The same native reducer that appears in the public SHAKE tree proof,
instantiated with the staged package's native hash interface. -/
def shakeReduction : ReduceValues :=
  @ParallelReduceNative.reduce_tree ⟨fun N => Array Std.U8 N, shake.xmss.hash2⟩

def signerOps {H : Type} : Ops (ParallelWorkerCells.Ref H) (StateT H Result) :=
  heapOps shakeReduction

/-- The scheduler may switch workers at every set/get, including the
individual reads performed by the native tree reducer's initial collect. -/
def concurrentOps {H : Type} :
    Ops (ParallelWorkerCells.Ref H) (ParallelWorkerInterleave.Program H) where
  get := ParallelWorkerInterleave.get
  set := ParallelWorkerInterleave.set
  tree := fun refs seed addr root sub height => do
    let values ← refs.val.mapM ParallelWorkerInterleave.get
    if bound : values.length ≤ Std.Usize.max then
      ParallelWorkerInterleave.liftResult
        (shakeReduction (Slice.from values bound) seed addr root sub height)
    else ParallelWorkerInterleave.liftResult (fail .panic)
  runLoop := ParallelWorkerInterleave.runLoop

/-- Dispatch of a single direct FORS node publishes the computed bytes in
the indexed lens. The equation retains the generated hash and Vec access. -/
theorem direct_store {N : Std.Usize} {H : Type} (reduceValues : ReduceValues)
    (fors_stride : Std.Usize) (a idx height : Std.U32) (slot : Std.Usize)
    (addr : address.Adrs) (sk seed node : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (indices : alloc.vec.Vec Std.U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array Std.U8 N)))
    (ref : ParallelWorkerCells.Ref H (Array Std.U8 N)) (h : H)
    (item : shake.slh.parallel.WorkItem) (kind : item.kind = .ForsNodeDirect idx height slot)
    (computed : shake.fors.fors_node sk idx height seed addr = ok node)
    (indexed : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) direct slot = ok ref)
    (empty : ref.read h = none) :
    interpreted.dispatch (heapOps reduceValues) fors_stride a addr sk seed layers indices
      xmss leaves direct split item h = ok ((),ref.write node h) := by
  simp only [interpreted.dispatch, kind, computed, indexed]
  have lifted {T : Type} (x : T) : (liftM (ok x) : StateT H Result T) = pure x := by
    funext s
    change (Aeneas.Std.bind (ok x) (fun v => ok (v,s))) = ok (x,s)
    rw [bind_ok]
  simp only [lifted, pure_bind]
  change (do
    let (r,h') ← ParallelWorkerCells.set ref node h
    let v ← core.result.Result.expect (Array.Insts.CoreFmtDebug N core.fmt.DebugU8) r
      (toStr "unique FORS direct slot")
    ok (v,h')) = _
  rw [ParallelWorkerCells.set_empty ref node h empty]
  simp [bind_tc_eq, bind_ok, core.result.Result.expect]

/-- One visible publication from the final reducer sequence. Its continuation
still contains the other two writes, making them separate scheduler steps. -/
theorem output_first_step {H A B C : Type}
    (sig : ParallelWorkerCells.Ref H A) (auth : ParallelWorkerCells.Ref H B)
    (roots : ParallelWorkerCells.Ref H C) (x : A) (y : B) (z : C) (h : H)
    (l r : List (ParallelWorkerInterleave.Program H Unit)) (empty : sig.read h = none) :
    ParallelWorkerInterleave.Step h (l ++ publishOutputs concurrentOps sig auth roots x y z :: r)
      (sig.write x h) (l ++ (do
        let _ ← ParallelWorkerInterleave.set auth y
        let _ ← ParallelWorkerInterleave.set roots z
        pure ()) :: r) := by
  simpa [publishOutputs, concurrentOps, empty] using
    ParallelWorkerInterleave.set_step sig x (fun _ => do
      let _ ← ParallelWorkerInterleave.set auth y
      let _ ← ParallelWorkerInterleave.set roots z
      pure ()) h l r

theorem output_three_steps {H A B C : Type}
    (sig : ParallelWorkerCells.Ref H A) (auth : ParallelWorkerCells.Ref H B)
    (roots : ParallelWorkerCells.Ref H C) (x : A) (y : B) (z : C) (h : H)
    (l r : List (ParallelWorkerInterleave.Program H Unit)) (emptySig : sig.read h = none)
    (emptyAuth : auth.read (sig.write x h) = none)
    (emptyRoots : roots.read (auth.write y (sig.write x h)) = none) :
    ParallelWorkerInterleave.Steps h (l ++ publishOutputs concurrentOps sig auth roots x y z :: r)
      (roots.write z (auth.write y (sig.write x h))) (l ++ pure () :: r) := by
  apply ParallelWorkerInterleave.Steps.follow
  · apply ParallelWorkerInterleave.Steps.follow
    · exact (output_first_step sig auth roots x y z h l r emptySig).single
    · simpa [emptyAuth] using ParallelWorkerInterleave.set_step auth y
        (fun _ => do let _ ← ParallelWorkerInterleave.set roots z; pure ()) (sig.write x h) l r
  · simpa [emptyRoots] using ParallelWorkerInterleave.set_step roots z
      (fun _ => pure ()) (auth.write y (sig.write x h)) l r

theorem direct_step {N : Std.Usize} {H : Type}
    (stride : Std.Usize) (a idx height : Std.U32) (slot : Std.Usize)
    (addr : address.Adrs) (sk seed node : Array Std.U8 N)
    (layers : alloc.vec.Vec (address.Adrs × Std.U32)) (indices : alloc.vec.Vec Std.U32)
    (xmss leaves direct split : alloc.vec.Vec (ParallelWorkerCells.Ref H (Array Std.U8 N)))
    (ref : ParallelWorkerCells.Ref H (Array Std.U8 N)) (h : H)
    (l r : List (ParallelWorkerInterleave.Program H Unit))
    (item : shake.slh.parallel.WorkItem) (kind : item.kind = .ForsNodeDirect idx height slot)
    (computed : shake.fors.fors_node sk idx height seed addr = ok node)
    (indexed : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) direct slot = ok ref)
    (empty : ref.read h = none) :
    ParallelWorkerInterleave.Step h
      (l ++ interpreted.dispatch concurrentOps stride a addr sk seed layers indices
        xmss leaves direct split item :: r) (ref.write node h) (l ++ pure () :: r) := by
  simp only [interpreted.dispatch, kind, computed, indexed]
  have lifted {T : Type} (x : T) :
      (liftM (ok x) : ParallelWorkerInterleave.Program H T) = pure x :=
    ParallelWorkerInterleave.lift_ok x
  simp only [lifted, pure_bind]
  exact (by
    simpa [concurrentOps, empty, core.result.Result.expect, lifted] using
      ParallelWorkerInterleave.set_step ref node
        (fun v => (liftM (core.result.Result.expect (Array.Insts.CoreFmtDebug N core.fmt.DebugU8) v
          (toStr "unique FORS direct slot")) : ParallelWorkerInterleave.Program H Unit)) h l r)
"""
