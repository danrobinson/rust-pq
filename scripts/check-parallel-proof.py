# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Replay the parallel sign, subtree and single-state permutation proofs."""

import re
import runpy
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
common = facade["common"]
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
sys.path.insert(0, str(HERE / "parallel-proof"))
import active
import build
import signer
import cached_mutations
import subtree


def check_dispatch(scratch):
    llbc = scratch / "fast.llbc"
    generated = scratch / "fast"
    cuts = (
        "crate::shake256::round",
        "crate::sha256::x86::avx512_available",
        "crate::shake256::stream_x86::blocks",
    )
    run(
        [
            ROOT / ".tools/aeneas/charon/bin/charon",
            "cargo",
            "--preset=aeneas",
            "--start-from",
            "crate::shake256::permute",
            *(arg for name in cuts for arg in ("--opaque", name)),
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "parallel",
            "--target",
            "x86_64-unknown-linux-gnu",
        ],
        ROOT / "rust",
    )
    run(
        [
            ROOT / ".tools/aeneas/bin/aeneas",
            "-backend",
            "lean",
            "-abort-on-error",
            "-no-progress-bar",
            "-split-files",
            "-dest",
            generated,
            llbc,
        ],
        ROOT,
    )

    def decls(file, namespace):
        return set(common["declarations"](common["body"](file, namespace)))

    scalar = decls(LEAN / "Keccakscalar/Funs.lean", "KeccakScalarRust")
    entry = (
        (LEAN / "Parallel/Dispatch.lean")
        .read_text()
        .split("def shake256.permute\n", 1)[1]
        .split("\ntheorem ", 1)[0]
    )
    expected = {
        d
        for d in scalar
        if d.startswith(
            (
                "@[global_simps, irreducible]\ndef shake256.RC",
                "@[rust_loop_body]\ndef shake256.permute_loop.body",
                "@[rust_loop]\ndef shake256.permute_loop",
            )
        )
    }
    if len(expected) != 3 or decls(generated / "Types.lean", "slhdsa"):
        raise ValueError("unexpected scalar declarations or nominal input types")
    if decls(generated / "Funs.lean", "slhdsa") != expected | {
        "def shake256.permute\n" + entry.strip("\n")
    }:
        raise ValueError(
            "feature-selected permutation no longer matches the proved caller"
        )
    bindings = {
        "sha256.x86.avx512_available": "GatherRust.sha256.x86.avx512_available",
        "shake256.stream_x86.blocks": "KgridbulkRust.shake256.stream_x86.blocks",
        "shake256.round": "KeccakScalarRust.shake256.round",
    }
    checks = ["import Parallel.Dispatch", "open Aeneas Aeneas.Std Result"]
    external = (
        (generated / "FunsExternal_Template.lean")
        .read_text()
        .split("open slhdsa", 1)[1]
    )
    for declaration in common["declarations"](external):
        name, signature = re.fullmatch(
            r"axiom\s+(\S+)\s*:\s*(.*)", declaration, re.DOTALL
        ).groups()
        checks.append(f"example : {signature} := {bindings.pop(name)}")
    if bindings:
        raise ValueError("missing permutation dependencies")
    for family in ("sha2", "shake"):
        for level in (128, 192, 256):
            for variant in ("s", "f"):
                p = f"Spec.{family}_{level}{variant}"
                checks.append(f"example : {p}.a ≤ 14 ∧ {p}.hp ≤ 9 := by decide")
                if family == "shake":
                    checks.append(
                        f"example : {p}.len = 2*{p}.n+3 ∧ {p}.w=16 := by decide"
                    )
    run(["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(checks), text=True)


def check_entry_calls():
    def single(file, fragment, count=1):
        source = re.sub(r"//[^\n]*|\s+", "", (build.SRC / file).read_text())
        if source.count(re.sub(r"\s+", "", fragment)) != count:
            raise ValueError(f"review the feature-selected call in {file}")

    single(
        "xmss.rs",
        """shake_only! {
        #[cfg(all(feature = "platform-sha2", any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        )))]
        if z >= 1 && super::batch::available::<N>() {
            return super::batch::xmss_subtree(sk_seed, seed, i, z, adrs);
        }
    }""",
    )
    single("shake/batch.rs", "matches!(N, 16 | 24 | 32) && parallel::available()")
    single(
        "slh.rs",
        """#[cfg(all(feature = "parallel", not(target_os = "none")))]
        if let Some(sig) = parallel::sign($p, md, &$sk_seed, &seed, adrs, &$r, idx_tree, idx_leaf) {
            return sig;
        }""",
    )
    for file in ("slh.rs", "slh/message.rs"):
        single(
            file,
            "sign_digest!(N, p, sk_seed, pk_seed, r, digest)",
            2 if file == "slh.rs" else 1,
        )


def check_pool():
    # Match the production branches modeled by Parallel.Pool and reject new raw
    # accesses to the borrowed job. Atomic/CV semantics remain a trust boundary.
    source = (build.SRC / "pool.rs").read_text().split("#[cfg(test)]", 1)[0]
    stripped = re.sub(r"//[^\n]*|\s+", "", source)
    if stripped.count(".job.get()") != 3:
        raise ValueError("review the raw worker job access set")

    def ordered(body, markers):
        text = re.sub(r"//[^\n]*|\s+", "", body)
        start = 0
        for marker in markers:
            marker = re.sub(r"\s+", "", marker)
            if marker not in text[start:]:
                raise ValueError(f"review worker pool event {marker}")
            start = text.index(marker, start) + len(marker)

    ordered(
        source[source.index("impl<'a> PoolGuard") : source.index("impl Drop for PoolGuard")],
        [
            "fn claim<F:Fn()+Sync>(pool:&'a Pool,n_workers:usize,scrub:bool,f:&'a F,)->Option<Self>",
            ".compare_exchange(false,true,Ordering::Acquire,Ordering::Relaxed).is_err(){return None;}",
            "unsafe fn trampoline<F:Fn()+Sync>(ptr:*const()){let f=&*(ptr as *const F);f();}",
            "*pool.job.get()=Some(Job{data:(f as *const F).cast::<()>(),call:trampoline::<F>,scrub,});",
            "pool.remaining.store(n_workers*2,Ordering::Relaxed);",
            "pool.caller_parked.store(false,Ordering::Relaxed);",
            "Some(Self{pool})",
        ],
    )
    ordered(
        source[source.index("pub(crate) fn execute") :],
        [
            "let n_workers = (max_threads - 1).min(spawned);dispatch(pool,n_workers,scrub,f);",
            "if n_workers==0{f();return;}",
            "let Some(_guard)=PoolGuard::claim(pool,n_workers,scrub,f)else{f();return;};",
            "for slot in &pool.workers[..n_workers]",
            "slot.state.swap(WORK_PENDING,Ordering::AcqRel);if prev==IDLE_PARKED{need_notify=true;}",
            "if need_notify{let _lock=pool.park_lock.lock().unwrap_or_else(|e|e.into_inner());pool.park_cv.notify_all();}",
            "f();",
        ],
    )
    ordered(
        source[source.index("fn worker_once") : source.index("fn worker_loop")],
        [
            "let s=slot.state.load(Ordering::Acquire);if s==WORK_PENDING{break;}",
            "slot.state.compare_exchange(IDLE_SPIN,IDLE_PARKED,Ordering::AcqRel,Ordering::Acquire,)",
            "Ok(_)=>{let mut guard=pool.park_lock.lock().unwrap_or_else(|e|e.into_inner());",
            "while slot.state.load(Ordering::Acquire)==IDLE_PARKED{guard=pool.park_cv.wait(guard)",
            "break;}Err(WORK_PENDING)=>break,",
            "let job=unsafe{(*pool.job.get()).expect(",
            "std::panic::catch_unwind(",
            "run_worker_job(job.call,job.data);",
            "if let Err(payload)=result{pool.remaining.fetch_or(1,Ordering::Relaxed);",
            "if let Err(second)=std::panic::catch_unwind(std::panic::AssertUnwindSafe(||drop(payload))){core::mem::forget(second);}",
            "slot.state.store(IDLE_SPIN,Ordering::Release);",
            "pool.remaining.fetch_sub(2,Ordering::SeqCst)<4&&pool.caller_parked.load(Ordering::SeqCst)",
            "let _g=pool.done_lock.lock().unwrap_or_else(|e|e.into_inner());pool.done_cv.notify_one();",
        ],
    )
    ordered(
        source[
            source.index("impl Drop for PoolGuard") : source.index("fn run_worker_job")
        ],
        [
            "let failed=loop{let state=self.pool.remaining.load(Ordering::Acquire);if state<2{break state==1;}",
            "self.pool.caller_parked.store(true,Ordering::SeqCst);",
            "if self.pool.remaining.load(Ordering::SeqCst)>=2{let mut g=self.pool.done_lock.lock()",
            "while self.pool.remaining.load(Ordering::Acquire)>=2{g=self.pool.done_cv.wait(g)",
            "self.pool.caller_parked.store(false,Ordering::Relaxed);",
            "*self.pool.job.get()=None;",
            "self.pool.busy.store(false,Ordering::Release);",
            "if failed && !thread::panicking(){panic!(",
        ],
    )


def main():
    check_entry_calls()
    check_pool()
    run([sys.executable, HERE / "check-uncached-parallel-caller.py"], ROOT)
    run([sys.executable, HERE / "check-parallel-keygen.py"], ROOT)
    run([sys.executable, HERE / "check-signing-schedules.py"], ROOT)
    run([sys.executable, HERE / "check-parallel-sign-join.py"], ROOT)
    run([sys.executable, HERE / "check-parallel-wots-ticket.py"], ROOT)
    run([sys.executable, HERE / "check-shake-fused-xmss.py"], ROOT)
    run([sys.executable, HERE / "parallel-proof" / "buffered_tree.py"], ROOT)
    modules = {
        "Parallel.Pool": "ParallelPool.join",
        "Parallel.LastFinisher": "ParallelFused.LastFinisher.signature_at_last",
        "Parallel.SigningSchedules": "ParallelFused.Schedules.signature_independent",
        "Parallel.SigningSlots": "ParallelFused.Slots.output_fips",
        "Parallel.SigningPublication": "ParallelSigning.Publication.ready_sees_cells",
        "Parallel.Cached": "ParallelCached.interleavings",
        "Parallel.FusedWots": "ParallelFusedWots.selected",
        "Parallel.Fused": "ParallelFused.context_sign_fips",
        "Parallel.SplitTree": "ParallelSplitTree.keygenRoot",
        "Parallel.Batch": "ParallelBatch.verify_all",
        "Parallel.Subtree": "ParallelSubtree.subtree_eq",
        "Parallel.Dispatch": "slhdsa.ParallelDispatch.permute_fips",
    }
    run(["lake", "build", *modules], LEAN)
    for module, theorem in modules.items():
        facade["audit_theorems"](module, [theorem])
    facade["audit_theorems"](
        "Parallel.Pool",
        [
            "ParallelPool.packed_join",
            "ParallelPool.safe_to_clear",
            "ParallelPool.join_wakeup_order",
            "ParallelPool.condvar_wakeup_order",
            "ParallelPool.Publication.published",
        ],
    )
    facade["audit_theorems"]("Parallel.LastFinisher", ["ParallelFused.LastFinisher.visibility", "ParallelFused.LastFinisher.can_finish"])
    facade["audit_theorems"]("Parallel.SigningSlots", ["ParallelFused.Slots.constructed"])
    facade["audit_theorems"]("Parallel.Fused", ["ParallelFused.phase_one_ready"])
    with tempfile.TemporaryDirectory() as tmp:
        check_dispatch(Path(tmp))
        signer.main()
        cached_mutations.main()
        build.check_tree_layout(Path(tmp))
        image = build.build(Path(tmp))
        for n in (16, 24, 32):
            for height in (1, 2, 3):
                subtree.check(image, n, height)
        # The larger streaming trees also use a full eight active parents.
        parents = active.project_for(active.image(Path(tmp), 8))
        for n in (16, 24, 32):
            for lanes in (2, 4, 8):
                active.check(8, parents, n, lanes, 1)
    run(["sh", HERE / "check-keccak-assembly.sh", "parallel"], ROOT)


if __name__ == "__main__":
    main()
