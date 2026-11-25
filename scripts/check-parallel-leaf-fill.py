#!/usr/bin/env python3
"""Check the constructor's complete worker protocol and extract the two real leaf payloads."""
import re
import runpy
import shutil
import tempfile
from pathlib import Path



facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
root, lean, run = (facade[k] for k in ("ROOT", "LEAN", "run"))
token = re.compile(r"::|\.\.|->|[a-zA-Z_0-9]+|[^\s]")

def tokens(s):
    return token.findall(re.sub(r"//[^\n]*", "", s))

def replace_workers(source):
    planner = """
    use core::sync::atomic::{AtomicUsize, Ordering};
    if num_leaves < 16 {return false;}
    let workers = crate::pool::available_threads().min(num_leaves / 4);
    if workers < 2 {return false;}
    let chunk = (num_leaves / (workers * 4)).max(4);
    let num_chunks = (num_leaves + chunk - 1) / chunk;
    let slots: Vec<std::sync::OnceLock<Vec<[u8; N]>>> =
        (0..num_chunks).map(|_| std::sync::OnceLock::new()).collect();
    let next = AtomicUsize::new(0);
    let fill = || loop {
        let id = next.fetch_add(1, Ordering::Relaxed);
        let Some(slot) = slots.get(id) else { break };
        let start = id * chunk;
        let end = (start + chunk).min(num_leaves);
    """
    join = """
        let _ = slot.set(out);
    };
    crate::pool::execute(workers, true, &fill);
    for (id, slot) in slots.into_iter().enumerate() {
        let start = id * chunk;
        let batch = slot.into_inner().expect("all leaf chunks completed");
        leaves[start..start + batch.len()].copy_from_slice(&batch);
    }
    true
    """
    pattern = re.compile(r"(    fn build_leaves_parallel<const N: usize>\()(.*?)(    \) -> bool \{)(.*?)(\n    \})", re.S)
    count = 0
    def expose(match):
        nonlocal count
        count += 1
        head, args, sigend, body, end = match.groups()
        begin = body.index("let mut out =")
        stop = body.index("let _ = slot.set(out);")
        if tokens(body[:begin]) != tokens(planner) or tokens(body[stop:]) != tokens(join):
            raise ValueError("constructor allocation, ticket claim, publication or ordered join changed")
        args = args.replace("num_leaves: usize,", "start: usize, end: usize,").replace("leaves: &mut [[u8; N]],", "")
        helper = head.replace("build_leaves_parallel", "proof_leaf_batch") + args + "    ) -> Vec<[u8; N]> {\n" + body[begin:stop] + "out" + end
        geometry = ""
        if count == 1:
            common = body[body.index("if num_leaves <"):body.index("let slots:")]
            common = common.replace("return false;", "return None;").replace("crate::pool::available_threads()", "threads")
            geometry = "\n    fn proof_leaf_plan(num_leaves: usize, threads: usize) -> Option<(usize,usize)> {" + common + "Some((chunk,num_chunks))\n    }"
        return match.group() + "\n" + helper + geometry
    output = pattern.sub(expose, source)
    if count != 2:
        raise ValueError(f"expected both constructor workers, found {count}")
    return output

def extract(tmp, target):
    crate = tmp / "crate"
    crate.mkdir()
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        if (root / "rust" / name).exists():
            shutil.copy(root / "rust" / name, crate / name)
    shutil.copytree(root / "rust/src", crate / "src")
    (crate / "benches").mkdir()
    (crate / "benches/platforms.rs").touch()
    path = crate / "src/cache.rs"
    path.write_text(replace_workers(path.read_text()))
    lib, dest = tmp / "fill.llbc", tmp / "Fill"
    run([root / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         "--start-from", "crate::cache::sha2_ops::proof_leaf_plan",
         "--start-from", "crate::cache::sha2_ops::proof_leaf_batch", "--start-from", "crate::cache::shake_ops::proof_leaf_batch",
         "--opaque", "crate::wots::wots_pk_gen", "--opaque", "crate::cache::shake_ops::fill_leaves_chunk",
         "--opaque", "crate::address::Adrs::with_type", "--opaque", "crate::address::Adrs::with_keypair", "--dest-file", lib, "--", "--locked", "--features", "parallel,platform-sha2",
         "--target", target], crate)
    run([root / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar", "-split-files", "-dest", dest, lib], root)
    return (dest / "Funs.lean").read_text()

def check(target, scratch):
    output = extract(scratch, target)
    code = output.split("namespace slhdsa\n", 1)[1].rsplit("end slhdsa", 1)[0]
    code = re.sub(r"/\-\-.*?\-/", "", code, flags=re.S)
    code = code.replace("cache.sha2_ops.proof_leaf_plan", "runtimePlan")
    code = code.replace("cache.sha2_ops.proof_leaf_batch", "sha2Batch")
    code = code.replace("cache.shake_ops.proof_leaf_batch", "shakeBatch")
    code = code.replace("cache.shake_ops.fill_leaves_chunk", "nativeShake.fill_leaves_chunk")
    code = code.replace("def shakeBatch\n", "def shakeBatch [nativeShake.Backend]\n")
    program = [
        "import Cachepath.ParallelFillWorkers",
        "open Aeneas Aeneas.Std Result ControlFlow",
        "open slhdsa slhdsa.cache.builder",
        "namespace ConstructorPayload",
        code,
        "example : address.WOTS_HASH = slhdsa.address.WOTS_HASH := by rfl'",
        "example : address.Adrs.with_type = slhdsa.address.Adrs.with_type := by rfl'",
        "example : address.Adrs.with_keypair = slhdsa.address.Adrs.with_keypair := by rfl'",
    ]
    for name in ("sha2Batch_loop.body", "sha2Batch_loop", "sha2Batch", "shakeBatch", "runtimePlan"):
        program.append(f"example : @{name} = @workers.fill.{name} := by rfl'")
    run(["lake", "env", "lean", "--stdin"], lean, input="\n".join(program + ["end ConstructorPayload"]), text=True)
    print(f"{target}: matched planner and slot protocol, kernel matched both per-ticket Rust programs", flush=True)

def main():
    run(["lake", "build", "Cachepath.ParallelFillHosted"], lean)
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory(prefix="parallel-leaf-fill-") as work:
            check(target, Path(work))
    facade["audit_theorems"]("Cachepath.ParallelFill", [
        "slhdsa.cache.builder.workers.fill." + name for name in ("can_join", "assemble_join", "bounds")])
    facade["audit_theorems"]("Cachepath.ParallelFillHosted", [
        "CacheopsRust.NativeSession." + host + "_parallelBuild" for host in ("apple", "linuxArm", "linuxX86")])

if __name__ == "__main__":
    main()
