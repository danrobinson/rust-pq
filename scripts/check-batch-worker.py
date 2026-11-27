#!/usr/bin/env python3
"""Run the production generic batch workers and worker pool on verdict oracles.

The host pool and Rust atomics execute normally. Each fresh process fixes the
cached available CPU count before its first dispatch. Finite native executions
supplement the Lean scheduler model; they do not enumerate weak-memory histories.
"""
from pathlib import Path
import os
import runpy
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
function = runpy.run_path(str(HERE / "parallel-proof/build.py"))["function"]
mutations = (
    ("skip-first", "verify_batch_with", "AtomicUsize::new(0)", "AtomicUsize::new(1)", 2, "missing live ticket"),
    ("swap-slot", "verify_batch_with", "results[idx].store", "results[items.len()-1-idx].store", 2, "wrong ordered verdicts"),
    ("lose-rejection", "verify_batch_all_with", "all_ok.store(false", "all_ok.store(true", 2, "wrong conjunction"),
    ("serial-any", "verify_batch_all_with", "items.iter().all", "items.iter().any", 1, "serial short-circuit"),
    ("empty-false", "verify_batch_all_with", "return true;", "return false;", 1, "wrong conjunction"),
)


def harness(source):
    mutants = []
    for label, which, old, new, _, _ in mutations:
        original = function(source, which)
        if original.count(old) != 1:
            raise ValueError(f"{label}: expected exactly one worker mutation point")
        mutants.append(original.replace("fn " + which + "<", "fn " + label.replace("-", "_") + "<", 1).replace(old, new))
    probe = (HERE / "parallel-proof/batch-worker.rs").read_text()
    return probe.replace("// MUTATED_WORKERS", "\n\n".join(mutants))


def main():
    env = os.environ.copy()
    env["PATH"] = f"{Path.home()}/.cargo/bin:{env['PATH']}"
    with tempfile.TemporaryDirectory() as tmp:
        crate = Path(tmp) / "rust"
        shutil.copytree(ROOT / "rust", crate, ignore=shutil.ignore_patterns("target", ".git"))
        batch = crate / "src/batch_api.rs"
        production = batch.read_text()
        batch.write_text(production + "\n" + harness(production))
        # All production functions retain their bodies. This probe supplies the
        # host CPU count through the same OnceLock available_threads reads.
        with (crate / "src/pool.rs").open("a") as pool:
            pool.write("\npub(crate) fn configure_worker_replay(n: usize) { PARALLELISM.set(n).unwrap(); }\n")
        binary_source = crate / "src/bin/worker_replay.rs"
        binary_source.parent.mkdir(exist_ok=True)
        binary_source.write_text("""fn main() {
    let args: Vec<_> = std::env::args().collect();
    slhdsa::batch_api::worker_replay::run(args[1].parse().unwrap(), &args[2]);
}
""")
        env["CARGO_TARGET_DIR"] = str(Path(tmp) / "target")
        subprocess.run(["cargo", "build", "--locked", "--features", "parallel", "--release", "--bin", "worker_replay"],
                       cwd=crate, env=env, check=True)
        binary = Path(env["CARGO_TARGET_DIR"]) / "release/worker_replay"
        for threads in (1, 2, 4, 16):
            subprocess.run([binary, str(threads), "real"], env=env, check=True, timeout=120)
        for label, _, _, _, threads, diagnostic in mutations:
            result = subprocess.run([binary, str(threads), label], env=env, capture_output=True, text=True, timeout=30)
            if result.returncode == 0 or diagnostic not in result.stderr:
                raise RuntimeError(f"{label}: expected a verdict/ticket assertion failure, got {result.stderr}")
        print("Native batch workers passed four pool sizes, forced overlap, nested fallback, and five mutation controls.")


if __name__ == "__main__":
    main()
