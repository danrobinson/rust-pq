#!/usr/bin/env python3
"""Check the staged SHAKE signer against production MIR and typecheck its Aeneas extraction."""

import os
import re
import runpy
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
import worker_barrier
import worker_mir as mir
from worker_allocations import (
    allocation_graphs,
    allocation_sites,
    allocation_witness,
    check_captures,
)
from worker_control import control_witness, runtime_witness
from worker_dispatch_receipt import dispatch_receipt_witness
from worker_effects import effects_witness
from worker_native import native_package
from worker_phase_one import phase_one_witness
from worker_source import stage

probe = runpy.run_path(str(HERE / "probe-parallel-sign-borrows.py"))
common = probe["common"]
ROOT = common["ROOT"]
TARGETS = (
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-gnu",
)
SIGN = "shake::slh::parallel::sign"
HELPER = "shake::slh::parallel::dispatch"


def require(test, reason):
    if not test:
        raise ValueError(reason)


def compile_mir(crate, tmp, target):
    path = tmp / (target + crate.parent.name + ".mir")
    subprocess.run(
        [
            "cargo",
            "rustc",
            "--locked",
            "--lib",
            "--features",
            "parallel,platform-sha2",
            "--target",
            target,
            "--",
            "--emit=mir=" + str(path),
        ],
        cwd=crate,
        check=True,
    )
    return path.read_text()


def check_target(prod, crate, tagged, tmp, target):
    text = compile_mir(prod, tmp, target)
    staged = compile_mir(crate, tmp, target)
    worker = mir.only(
        body
        for label in re.findall(r"\nfn (" + SIGN + r"::\{closure#\d+\})\(", text)
        if "WorkKind));" in (body := mir.function(text, label))
    )
    wrapper = mir.only(
        b
        for label in re.findall(r"\nfn (" + SIGN + r"::\{closure#\d+\})\(", staged)
        if "::flat_worker::<N>(" in (b := mir.function(staged, label))
    )
    mir.call_arguments(staged, wrapper)
    mir.check_wait_exit(mir.function(staged, "shake::slh::parallel::flat_worker"))
    original, original_callbacks = mir.normal_graph(worker, False)
    helper = mir.function(staged, HELPER)
    lifted, lifted_callbacks = mir.normal_graph(helper, True)
    require(
        original == lifted,
        "MIR blocks, operations, or branch targets differ after closure conversion",
    )
    require(
        len(original_callbacks) == len(lifted_callbacks) == 4, "missing SIMD callback"
    )
    require(
        mir.callbacks(text, original_callbacks)
        == mir.callbacks(staged, lifted_callbacks),
        "nested SIMD callback bodies differ",
    )

    # Mutate only the helper side; a wrong capture, operation or control edge must remain visible.
    def mutant(old, new):
        require(old in helper, "mutation site missing")
        return mir.normal_graph(helper.replace(old, new, 1), True)[0]

    require(
        original != mutant("as ForsNodeSplit).0:", "as ForsNodeSplit).1:"),
        "accepted swapped ticket field",
    )
    require(
        original != mutant("::fors_node::<N>", "::xmss_node::<N>"),
        "accepted wrong native primitive",
    )
    require(
        original != mutant("0: bb9, 1: bb8", "0: bb8, 1: bb9"),
        "accepted reversed work dispatch",
    )

    source = "import Parallel.WorkerPrepared\nopen ParallelWorkerMir\nset_option maxRecDepth 16384\n"
    source += mir.graph_witness(original, lifted, "dispatch")
    labelled = compile_mir(tagged, tmp, target)
    a, b = allocation_graphs(staged, labelled)
    source += mir.graph_witness(a, b, "allocation")
    names = ["dispatch", "allocation"]
    require(
        re.findall(
            r"const shake::slh::parallel::sign::(PHASE\w+): u8 = const (\d+)_u8;", text
        )
        == re.findall(
            r"const shake::slh::parallel::(PHASE\w+): u8 = const (\d+)_u8;", staged
        )
        == [("PHASE1_RUNNING", "0"), ("PHASE2_READY", "1"), ("PHASE_ABORTED", "2")],
        "phase constants changed",
    )
    for region, fn in (
        ("reduce", "reduce"),
        ("wots", "phase_two"),
        ("controller", "flat_worker"),
        ("publish", "publish"),
        ("wait", "wait"),
        ("caller", "sign"),
    ):
        production, c = mir.normal_graph(
            mir.function(text, SIGN) if region == "caller" else worker, False, region
        )
        body = mir.function(staged, "shake::slh::parallel::" + fn)
        extracted, e = mir.normal_graph(body, True, region)
        wrong = {
            "reduce": ("shake::fors::fors_pk_from_sig", "shake::fors::wrong_root"),
            "wots": (
                "core::sync::atomic::Ordering::Relaxed",
                "core::sync::atomic::Ordering::Release",
            ),
            "controller": (" = Eq(", " = Ne("),
            "publish": (
                "core::sync::atomic::Ordering::Release",
                "core::sync::atomic::Ordering::Relaxed",
            ),
            "wait": (
                "core::sync::atomic::Ordering::Acquire",
                "core::sync::atomic::Ordering::Relaxed",
            ),
            "caller": ("const 2_usize", "const 3_usize"),
        }
        old, new = wrong[region]
        require(old in body, f"missing {region} mutation site")
        bad, _ = mir.normal_graph(body.replace(old, new, 1), True, region)
        require(bad != production, f"accepted {region} mutation")
        require(
            production == extracted,
            f"{region} differs: "
            + str(
                next(
                    (
                        (i, x, y)
                        for i, (x, y) in enumerate(zip(production, extracted))
                        if x != y
                    ),
                    "graph size",
                )
            ),
        )
        if region == "caller":
            # The run callback is the outlined function checked separately.
            original_run = mir.CLOSURE.search(worker)[0]
            staged_run = mir.CLOSURE.search(wrapper)[0]
            require(
                c.index(original_run) == e.index(staged_run),
                "pool uses another callback",
            )
            c.remove(original_run)
            e.remove(staged_run)
        require(
            mir.callbacks(text, c) == mir.callbacks(staged, e),
            f"{region} callback mismatch",
        )
        names.append(region)
        source += mir.graph_witness(production, extracted, region)
        if region in ("publish", "reduce"):
            source += worker_barrier.check_writer(production, region)
        if region == "wait":
            source += worker_barrier.witness(production)
            # Invert the fast-path predicate on just the represented production
            # graph. Even though wait still contains an acquire, acceptance on
            # RUNNING must invalidate the certificate.
            inverted = [
                (
                    [
                        op.replace(" = Eq(", " = Ne(") if "PHASE2_READY" in op else op
                        for op in ops
                    ],
                    edges,
                )
                for ops, edges in production
            ]
            try:
                worker_barrier.witness(inverted)
            except ValueError as err:
                require("without acquiring READY" in str(err), str(err))
            else:
                raise ValueError("accepted wait that admits an early reader")
    checked = subprocess.run(
        ["lake", "env", "lean", "--stdin"],
        cwd=ROOT / "lean-hw",
        input=source,
        check=False,
        text=True,
        capture_output=True,
    )
    require(
        checked.returncode == 0 and "sorryAx" not in checked.stdout,
        checked.stdout + checked.stderr,
    )
    for name in names:
        require(
            f"'{name}_runs' depends on axioms: [propext]" in checked.stdout.splitlines()
            or f"'{name}_runs' does not depend on any axioms"
            in checked.stdout.splitlines(),
            f"unexpected axiom dependency for {name}",
        )
    for name in (
        "wait_acquires_ready",
        "wait_reads_installed",
        "wait_accepts_values",
        "wait_native_signature",
        "wait_passes",
        "wait_to_wots_heap",
        "wait_runtime",
        "publish_sender_order",
        "reduce_sender_order",
    ):
        require(
            f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
            in checked.stdout.splitlines(),
            f"unexpected kernel assumptions for {name}",
        )
    package = tmp / target / "Worker"
    package.mkdir(parents=True)
    llbc = package.parent / "worker.llbc"
    cuts = probe["CUTS"] + [
        probe["SIGN"] + "::" + n for n in ("abort", "wait", "publish")
    ]
    subprocess.run(
        [
            common["CHARON"],
            "cargo",
            "--preset=aeneas",
            "--start-from",
            "crate::" + SIGN,
            *(arg for cut in cuts for arg in ("--opaque", cut)),
            "--include",
            "core::sync::atomic::Ordering",
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "parallel,platform-sha2",
            "--target",
            target,
        ],
        cwd=tagged,
        check=True,
    )
    subprocess.run(
        [
            common["AENEAS"],
            "-backend",
            "lean",
            "-sequential",
            "-abort-on-error",
            "-no-progress-bar",
            "-split-files",
            "-filter-trait-methods",
            "-dest",
            package,
            llbc,
        ],
        cwd=package.parent,
        check=True,
    )
    output = (package / "Funs.lean").read_text()
    variants = re.findall(
        r"^  \| shake\.slh\.parallel\.WorkKind\.(\w+)", output, re.MULTILINE
    )
    require(
        len(variants) == len(set(variants)) == 8
        and output.count("← std.sync.once_lock.OnceLock.set ") >= 14,
        "missing worker variant or store site",
    )
    for fn in ("dispatch", "reduce", "phase_two", "flat_worker", "sign"):
        require(
            "def shake.slh.parallel." + fn + "\n" in output,
            "absent extracted function " + fn,
        )
    check_captures(output)
    # The previous pure extraction reused these same-typed objects. Keep both
    # failures as regression controls at the actual callback boundary.
    for old in ("phase1_done", "roots_cell"):
        wrong = "phase1_next" if old == "phase1_done" else "xmss_auth_cell"
        bad, n = re.subn(r"(?<=, )" + old + r"(?=,)", wrong, output)
        require(n > 0, "missing shared-identity mutation site")
        try:
            check_captures(bad)
        except ValueError:
            pass
        else:
            raise ValueError("accepted an aliased shared allocation: " + old)
    check_package(package, target)
    print(
        f"{target}: full staged signer typechecked; {len(names)} normal MIR graph comparisons passed",
        flush=True,
    )


def iteration_witness(generated, package_name):
    name = mir.only(
        re.findall(
            r"^def (shake\.slh\.parallel\.flat_worker_loop\d*\.body)\n",
            generated,
            re.MULTILINE,
        )
    )

    def signature(fn):
        header = generated.split("def " + fn + "\n", 1)[1].split(
            " :\n  Result (ControlFlow", 1
        )[0]
        return header, " ".join(re.findall(r"\((\w+) :", header))

    header, args = signature(name)
    wots_name = mir.only(
        re.findall(
            r"^def (shake\.slh\.parallel\.phase_two_loop\d*\.body)\n",
            generated,
            re.MULTILINE,
        )
    )
    wots_header, wots_args = signature(wots_name)
    return f"""import {package_name}.Funs
import Parallel.WorkerIteration
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa
theorem extracted_iteration {header} :
    {name} {args} =
    ParallelWorkerIteration.iteration
      (core.sync.atomic.AtomicUsizeAlign8Usize.fetch_add phase1_next 1#usize core.sync.atomic.Ordering.Relaxed)
      (fun i => core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice shake.slh.parallel.WorkItem)
        (alloc.vec.Vec.deref jobs) i)
      (fun item => shake.slh.parallel.dispatch fors_stride a fors_addr sk seed layers
        fors_indices xmss_slots leaf_pks fors_direct fors_split item)
      (core.sync.atomic.AtomicUsizeAlign8Usize.fetch_add phase1_done 1#usize core.sync.atomic.Ordering.AcqRel)
      (fun i => i + 1#usize) total_phase1
      (shake.slh.parallel.reduce d hp leaf_pk_count fors_stride fors_addr p md seed layers xmss_meta
        fors_split_meta xmss_slots leaf_pks fors_direct fors_split sig_fors_cell xmss_auth_cell roots_cell)
      (shake.slh.parallel.publish phase2_state phase2_lock phase2_cv) := by
  unfold {name} ParallelWorkerIteration.iteration
  dsimp only
  congr 1
  funext i
  congr 1
  funext o
  cases o <;> rfl

theorem extracted_wots {wots_header} :
    {wots_name} {wots_args} =
    ParallelWorkerIteration.wots
      (core.sync.atomic.AtomicUsizeAlign8Usize.fetch_add phase2_next 1#usize core.sync.atomic.Ordering.Relaxed)
      (fun j => core.slice.Slice.get (core.slice.index.SliceIndexUsizeSlice
        (std.sync.once_lock.OnceLock (alloc.vec.Vec Std.U8))) (alloc.vec.Vec.deref wots_sigs) j)
      (fun j => alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (address.Adrs × Std.U32)) layers j)
      (fun j => alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice (Array Std.U8 N)) roots j)
      (fun addr => address.Adrs.with_type addr address.WOTS_HASH) address.Adrs.with_keypair
      (fun r addr => shake.wots.wots_sign r sk seed addr) std.sync.once_lock.OnceLock.set
      (fun r => core.result.Result.expect (core.fmt.DebugVec core.fmt.DebugU8) r (toStr "unique WOTS sign job")) := by
  unfold {wots_name} ParallelWorkerIteration.wots
  dsimp only
  congr 1
  funext i
  congr 1
  funext o
  cases o <;> rfl
end slhdsa
"""


def check_package(package, target):
    # Unimplemented library interfaces are explicit parameters of this typecheck.
    # Only the independent MIR trace theorems are audited as assumption-free.
    allowed = {
        "core.sync.atomic.private.Align1",
        "core.sync.atomic.private.Align8",
        "core.sync.atomic.Atomic",
        "std.sync.once_lock.OnceLock",
        "std.sync.poison.condvar.Condvar",
        "std.sync.poison.mutex.Mutex",
        "core.array.Array.map",
        "core.iter.traits.iterator.Iterator.map.default",
        "core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next",
        "core.slice.Slice.sort_unstable_by",
        "core.sync.atomic.AtomicU8Align1U8.new",
        "core.sync.atomic.AtomicUsizeAlign8Usize.new",
        "core.sync.atomic.AtomicUsizeAlign8Usize.fetch_add",
        "std.sync.once_lock.OnceLock.new",
        "std.sync.once_lock.OnceLock.get",
        "std.sync.once_lock.OnceLock.set",
        "std.sync.poison.condvar.Condvar.new",
        "std.sync.poison.mutex.Mutex.new",
        "SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter",
        "pool.available_threads",
        "pool.execute",
        "shake.slh.parallel.reduce_tree",
        "shake.slh.parallel.shake_fors_simd.secrets",
        "shake.slh.parallel.shake_fors_simd.nodes_active",
        "util.base_2b",
        "shake.batch.available",
        "shake.wots.wots_sign",
        "shake.slh.parallel.wait",
        "shake.slh.parallel.publish",
        "shake.fors.fors_pk_from_sig",
        "shake.xmss.hash2",
        "shake.fors.fors_node",
        "shake.fors.fors_sk_gen",
        "shake.xmss.xmss_node",
        "shake.slh.parallel.abort",
    }
    for file in package.glob("*External_Template.lean"):
        provided = set(re.findall(r"^axiom ([\w.]+)", file.read_text(), re.MULTILINE))
        require(
            provided <= allowed, "new external contracts: " + str(provided - allowed)
        )
    base = subprocess.check_output(
        ["lake", "env", "printenv", "LEAN_PATH"], cwd=ROOT / "lean-hw", text=True
    ).strip()
    env = {
        **os.environ,
        "LEAN_PATH": str(package.parent) + os.pathsep + base,
        "ELAN_TOOLCHAIN": (ROOT / "lean-hw/lean-toolchain").read_text().strip(),
    }
    for module in ("TypesExternal", "Types", "FunsExternal", "Funs"):
        path = package / (module + ".lean")
        if module.endswith("External"):
            path.write_text((package / (module + "_Template.lean")).read_text())
        if module == "Funs":
            generated = path.read_text()
            # Aeneas erases a unit component of this generated FnMut body.
            # Restore exactly that component at its trait-interface adapter.
            pattern = r"(  call_mut :=\n    )(shake\.slh\.parallel\.sign\.closure_\d+\.Insts\.CoreOpsFunctionFnMutTupleTuple\.call_mut)(\n})"
            generated, n3 = re.subn(
                pattern,
                r"\1fun c u => do let updated ← \2 c u; ok ((), updated)\3",
                generated,
            )
            require(n3 == 1, "unexpected Aeneas unit-tuple interface")
            path.write_text(generated)
        subprocess.run(
            ["lean", "-o", package / (module + ".olean"), path],
            cwd=package.parent,
            env=env,
            check=True,
        )
    check_witnesses(package, env, target)


def check_witnesses(package, env, target):
    generated = (package / "Funs.lean").read_text()
    witnesses = [
        iteration_witness(generated, package.name) + allocation_witness(generated),
        "import Parallel.WorkerDispatchWrites\nimport Parallel.WorkerPhaseOne\nimport Parallel.WorkerWotsLoop\nimport Parallel.WorkerPoolRuntime\nimport Parallel.WorkerCounterSafety\n"
        + effects_witness(generated, package.name)
        + control_witness(generated)
        + runtime_witness(generated)
        + dispatch_receipt_witness(generated)
        + worker_barrier.pool_witness(generated)
        + phase_one_witness(generated)
        + worker_barrier.certified_phase1_witness(generated),
    ]
    witnesses.append(native_package(package, target))
    for witness in witnesses:
        checked = subprocess.run(
            ["lean", "--stdin"],
            cwd=package.parent,
            env=env,
            capture_output=True,
            check=False,
            text=True,
            input=witness,
        )
        output = checked.stdout + checked.stderr
        require(checked.returncode == 0, output)
        require(
            "declaration uses 'sorry'" not in output and "sorryAx" not in output,
            "unfinished generated proof",
        )
        for theorem in re.findall(
            r"^#print axioms (NativeSigner[.\w]+)$", witness, re.MULTILINE
        ):
            reports = re.findall(
                r"^'"
                + re.escape(theorem)
                + r"' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])$",
                output,
                re.MULTILINE,
            )
            allowed = {"propext", "Classical.choice", "Quot.sound"}
            require(
                len(reports) == 1
                and {a.strip() for a in reports[0].split(",") if a.strip()} <= allowed,
                f"unexpected native theorem assumptions for {theorem}: {reports}",
            )


def main():
    import argparse

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", choices=TARGETS)
    selected = parser.parse_args().target
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".cargo/bin"),
            str(Path.home() / ".elan/bin"),
            os.environ["PATH"],
        ]
    )
    subprocess.run(
        [
            "lake",
            "build",
            "Parallel.WorkerFetchPublic",
            "Parallel.WorkerIteration",
            "Parallel.WorkerPoolRuntime",
            "Parallel.WorkerCounterSafety",
            "Parallel.WorkerDispatchWrites",
            "Parallel.WorkerPhaseOne",
            "Parallel.WorkerScalarLow",
            "Parallel.WorkerScatterHeap",
            "Parallel.WorkerIterators",
            "Parallel.WorkerActualReturn",
            "Parallel.WorkerCrypto",
            "Parallel.WorkerWotsHistory",
            "Parallel.WorkerPrepared",
        ],
        cwd=ROOT / "lean-hw",
        check=True,
    )
    roots = [
        "WorkerFetchSigning." + host + ".shake_" + str(bits) + shape + "." + op
        for host in ("ParallelAppleAPI", "ParallelX86API", "ParallelLinuxArmAPI")
        for bits in (128, 192, 256)
        for shape in ("s", "f")
        for op in ("roundtrip", "worker_returns")
    ]
    common["facade"]["audit_theorems"](
        "Parallel.WorkerFetchPublic",
        roots
        + [
            "slhdsa.WorkerFetch." + n
            for n in (
                "Execution.history",
                "realize",
                "fromMax",
                "session_orders",
                "decreases",
                "signing_from_prefixes",
            )
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerIteration",
        [
            "ParallelWorkerIteration." + n
            for n in (
                "exhausted",
                "claimed",
                "wots_store",
                "wots_exhausted",
                "wots_duplicate",
            )
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerBarrier",
        [
            "slhdsa.WorkerBarrier." + n
            for n in ("read_at_last_finisher", "no_lost_notification", "wake_to_reader")
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerPoolRuntime",
        [
            "ParallelWorkerPool." + name
            for name in ("exact_callbacks", "dispatched_steps", "caller_only")
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerWaitHeap",
        [
            "ParallelWorkerHeap." + name
            for name in ("wait_runtime_step", "publish_runtime_step", "wait_to_wots")
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerRuntime",
        [
            "ParallelWorkerRuntime." + name
            for name in (
                "index_table",
                "rmw_step",
                "publish_step",
                "Starts.loop",
                "Starts.step",
            )
        ]
        + [
            "ParallelWorkerHeap." + name
            for name in ("read_after_write", "frame", "fetch_frame")
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerPrepared",
        [
            "slhdsa.WorkerPayload." + name
            for name in (
                "native_signature",
                "wait_to_native_signature",
                "prepare_native",
                "wait_to_signature",
                "joined_native_heap",
                "native_run",
                "Execution.replay",
                "Execution.erase",
            )
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerWotsHistory",
        [
            "ParallelWorkerRuntime.Wots." + name
            for name in ("reflect_step", "reflect_run", "joined", "all_schedules")
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerCounterSafety",
        [
            "ParallelWorkerCounterSafety.all_interleavings",
            "ParallelWorkerCounterSafety.last_finisher",
            "ParallelWorkerCounterSafety.published_persists",
            "ParallelWorkerCounterSafety.set_slot",
        ],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerDispatchWrites", ["ParallelDispatchWrites.RecordedJob.completed"]
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerPhaseOne",
        ["ParallelPhaseOne.Schedule.executes", "ParallelPhaseOne.direct_plan"],
    )
    common["facade"]["audit_theorems"](
        "Parallel.WorkerScatterHeap",
        [
            "ParallelWorkerInterleave.Step.unique_worker",
            "ParallelWorkerScatter.realize",
            "ParallelWorkerScatter.reflect",
            "ParallelWorkerScatter.serial_fors",
        ],
    )
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        prod = common["copy_rust_crate"](tmp / "original")
        crate = common["copy_rust_crate"](tmp / "staged")
        path = crate / "src/slh/parallel.rs"
        path.write_text(stage(path.read_text()))
        tagged = common["copy_rust_crate"](tmp / "tagged")
        (tagged / "src/slh/parallel.rs").write_text(allocation_sites(path.read_text()))
        for target in (selected,) if selected else TARGETS:
            check_target(prod, crate, tagged, tmp, target)


if __name__ == "__main__":
    main()
