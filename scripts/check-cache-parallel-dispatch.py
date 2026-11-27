#!/usr/bin/env python3
"""Re-extract both parallel signing callers and their fallbacks on every hosted target."""
from pathlib import Path
import runpy
import tempfile

endtoend = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
facade = endtoend["facade"]
lean = endtoend["LEAN"]
decls = endtoend["generated_declarations"]
module = "CacheopsRust.cache.parallelSign"
families = ("sha2", "shake")


def check(target, scratch):
    rust_modules = [f"crate::cache::{family}_ops::" for family in families]
    fresh = endtoend["extract_target"](
        target, scratch, [name + "sign_from_digest" for name in rust_modules],
        (*endtoend["OPAQUES"], *(name + "sign_parallel" for name in rust_modules)),
        features="parallel,platform-sha2",
    )
    checked = decls(lean / "Parallel/CacheDispatchProgram.lean", module)
    for kind in ("Types", "Funs"):
        extracted = decls(fresh / f"{kind}.lean", "CacheopsRust", strict=True)
        common = decls(lean / f"Cacheops/{kind}.lean", "CacheopsRust")
        for name, body in extracted.items():
            for family in families:
                entry = f"cache.{family}_ops."
                if name == entry + "sign_from_digest":
                    expected = body.replace("def " + name, "def " + family + "Caller")
                    expected = expected.replace("{N : Std.Usize}", "{N : Std.Usize} (worker : " + family + "Worker N)", 1)
                    expected = expected.replace(entry + "sign_parallel", "worker")
                    if expected != checked[family + "Caller"]:
                        raise ValueError(f"parallel dispatch changed on {target}: {name}")
                    break
            else:
                if common.get(name) != body:
                    raise ValueError(f"parallel caller dependency differs on {target}: {name}")
        if kind == "Funs" and any(f"cache.{f}_ops.sign_from_digest" not in extracted for f in families):
            raise ValueError(f"missing a parallel caller on {target}")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"]:
            check(target, Path(tmp) / target)
    facade["run"](["lake", "build", "Parallel.CacheJoinedCaller"], lean)
    facade["audit_theorems"]("Parallel.CacheDispatch", [f"{module}.{f}_dispatch" for f in families])
    facade["audit_theorems"]("Parallel.CacheAssembly", ["ParallelCached.complete_signature"])
    facade["audit_theorems"]("Parallel.CacheJoinedCaller", [
        f"{module}.published_fips", *(f"{module}.{f}_joined" for f in families),
    ])
    print("Both parallel-enabled Rust signing callers match the Lean dispatch proofs on all three targets.")
