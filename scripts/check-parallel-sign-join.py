#!/usr/bin/env python3
"""Extract the real worker's early return and post-join signature copy loops."""

from pathlib import Path
import ast
import os
import re
import runpy
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
import signer

common = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
facade, root, lean = (common[n] for n in ("facade", "ROOT", "LEAN"))


def project(directory):
    crate = directory / "crate"
    crate.mkdir(parents=True)
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        src = root / "rust" / name
        if src.exists():
            shutil.copy(src, crate / name)
    shutil.copytree(root / "rust/src", crate / "src")
    (crate / "benches").mkdir()
    (crate / "benches/platforms.rs").touch()
    file = crate / "src/slh/parallel.rs"
    text = file.read_text()
    sign = signer.function(text, "sign")
    start = "    let k = p.k as usize;"
    finish = "    crate::pool::execute(threads.min(total_phase1), true, &run);"
    if sign.count(start) != 1 or sign.count(finish) != 1:
        raise ValueError("parallel signer phase boundaries changed")
    before, middle = sign.split(start)
    work, after = middle.split(finish)
    signature = before[: before.index(") -> Option<Vec<u8>>")]
    joined = signature.replace("fn sign<", "fn joined_slots<")
    joined += "    threads: usize,\n) -> (OnceLock<Vec<u8>>, OnceLock<Vec<[u8; N]>>, Vec<OnceLock<Vec<u8>>>) { unreachable!() }"
    # The cut returns the exact three cells live across the pool join, retaining
    # OnceLock::get, Option::expect, all Vec indexing and the actual copies.
    names = ("sig_fors_cell", "xmss_auth_cell", "wots_sigs")
    if not all(f"let {name}:" in work for name in names):
        raise ValueError("worker result storage changed")
    call = (
        "    let ("
        + ", ".join(names)
        + ") = joined_slots(p, md, sk, seed, fors_addr, r, tree, leaf, threads);"
    )
    projected = before.replace("fn sign<", "fn signed_after_join<") + call + after
    file.write_text(text + "\n" + joined + "\n" + projected)
    return crate


def extract(folder, target):
    crate = project(folder)
    return common["extract_target"](
        target,
        folder / "generated",
        ["crate::shake::slh::parallel::signed_after_join"],
        [
            "crate::shake::slh::parallel::joined_slots",
            "crate::pool",
            "crate::params::Params::sig_bytes",
            "std::sync",
        ],
        crate=crate,
        features="parallel,platform-sha2",
    )


dest = lean / "Parallel/SignJoinProgram.lean"


def program(pkg):
    shared = runpy.run_path(str(HERE / "check-cache-construction.py"))
    decls = shared["decls"]
    prefix = """import Parallel.UncachedCaller
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.ParallelSignJoin
abbrev Cells (N : Usize) := Option (alloc.vec.Vec U8) × Option (alloc.vec.Vec (Array U8 N)) ×
  alloc.vec.Vec (Option (alloc.vec.Vec U8))
abbrev Join := {N : Usize} → params.Params → Slice U8 → Array U8 N → Array U8 N →
  address.Adrs → Array U8 N → U64 → U32 → Usize → Result (Cells N)
/-- Read-only view after the pool join. Unpublished slots still produce none. -/
def readCell {α : Type} (v : Option α) : Result (Option α) := ok v
variable (threadsAvailable : Result Usize) (join : Join)
"""
    decl = []
    portable = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    for item in decls(pkg / "Funs.lean", "CacheopsRust"):
        if "def shake.slh.parallel.signed_after_join" not in item:
            if item not in portable:
                raise ValueError("unexpected worker copy dependency: " + item)
            continue
        for old, new in (
            ("shake.slh.parallel.signed_after_join", "run"),
            ("std.sync.once_lock.OnceLock.get", "readCell"),
            ("std.sync.once_lock.OnceLock", "Option"),
            ("pool.available_threads", "threadsAvailable"),
            ("shake.slh.parallel.joined_slots", "join"),
        ):
            item = item.replace(old, new)
        decl.append(item)
    if len(decl) != 5:
        raise ValueError("expected both copy loops and the worker")
    calls = set(
        re.findall(
            r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M
        )
    )
    if calls != {
        "std.sync.once_lock.OnceLock.get",
        "pool.available_threads",
        "shake.slh.parallel.joined_slots",
    }:
        raise ValueError(f"unexpected joined worker calls {calls}")
    data_types = set(decls(pkg / "Types.lean", "CacheopsRust"))
    if not data_types.issubset(decls(lean.parent / "lean/Slhdsa/Types.lean", "slhdsa")):
        raise ValueError("unexpected worker argument types")
    external_types = re.findall(
        r"^axiom ([\w.]+)", (pkg / "TypesExternal_Template.lean").read_text(), re.M
    )
    if external_types != ["std.sync.once_lock.OnceLock"]:
        raise ValueError(f"unexpected worker storage types {external_types}")
    return prefix + "\n\n".join(decl) + "\nend slhdsa.ParallelSignJoin\n"


def symbolic_slots(folder, width=3):
    src = root / "rust/src"
    probe = signer.probe_source((src / "cache.rs").read_text())
    probe = signer.once(
        probe,
        "static CPUS:",
        (HERE / "parallel-proof/post-join-rows.rs").read_text() + "\nstatic CPUS:",
    )
    probe = signer.once(
        probe,
        "    let mut expected = r.to_vec();",
        "    let reference_forest = fors.chunks_exact(N).map(<[Token]>::to_vec).collect();\n"
        "    let mut ticket_inputs = Vec::new();\n    let mut reference_leaves = Vec::new();\n    let mut reference_chunks = Vec::new();\n    let mut reference_meta = Vec::new();\n"
        "    let (mut reference_auth, mut reference_wots) = (Vec::new(),Vec::new());\n"
        "    let mut expected = r.to_vec();",
    )
    probe = signer.once(
        probe,
        "        for h in 0..hp {\n            let idx = Word",
        "        if j+1 < p.d { reference_leaves.push(xmss_node(&sk, leaf, 0, &pk, a).to_vec()); }\n        ticket_inputs.push((a, leaf, root.to_vec()));\n        reference_wots.push(part.clone());\n        for h in 0..hp {\n            let idx = Word",
    )
    probe = signer.once(
        probe,
        "            part.extend(xmss_node(&sk, idx, h as u32, &pk, a));",
        "            let node = xmss_node(&sk, idx, h as u32, &pk, a);\n"
        "            let split = (h as u32).saturating_sub(if hp >= 6 { 3 } else { 2 });\n"
        "            reference_meta.push((reference_chunks.len(), split, idx, h as u32));\n"
        "            for c in 0..1u32 << split { reference_chunks.push(xmss_node(&sk, (idx << split) + c, h as u32 - split, &pk, a).to_vec()); }\n"
        "            reference_auth.push(node.to_vec());\n            part.extend(node);",
    )
    probe = signer.once(
        probe,
        "    cached::check(",
        "    *EXPECTED_RAW.lock().unwrap() = (reference_meta, reference_chunks);\n"
        "    *EXPECTED_LEAVES.lock().unwrap() = reference_leaves;\n"
        "    *EXPECTED_TICKETS.lock().unwrap() = ticket_inputs;\n"
        "    *EXPECTED_CELLS.lock().unwrap() = Some((reference_forest, reference_auth, reference_wots));\n    cached::check(",
    )
    pack_start = 'let mut sig_fors = Vec::with_capacity(p.fors_sig_bytes());'
    probe = signer.once(probe, pack_start,
        'observe_raw_rows(&fors_direct, &xmss_slots, xmss_meta.iter().map(|m| (m.slot_start, m.split, m.root_idx, m.height)));\n                ' + pack_start)
    root_start = 'let mut roots: Vec<[Token; N]> = Vec::with_capacity(d);'
    probe = signer.once(probe, root_start, 'observe_root_inputs(&sig_fors, &xmss_auth, &leaf_pks);\n                ' + root_start)
    barrier = 'let roots = roots_cell.get().expect("roots ready");'
    probe = signer.once(probe, barrier, barrier + "\n        observe_ticket_inputs(&layers, roots);")
    anchor = 'let xmss_auth = xmss_auth_cell.get().expect("XMSS auth assembled");'
    probe = signer.once(
        probe,
        anchor,
        anchor + "\n    observe_cells(p, sig_fors, xmss_auth, &wots_sigs);",
    )
    path = folder / "observed.rs"
    binary = folder / "observed"
    path.write_text(probe.replace("PROOF_WIDTH", str(width)))
    subprocess.run(
        [
            "rustc",
            "--edition=2021",
            "--cfg",
            "proof_simd",
            "-Awarnings",
            "-O",
            "-C",
            "overflow-checks=yes",
            path,
            "-o",
            binary,
        ],
        check=True,
    )
    lines = subprocess.check_output([binary], text=True)
    observed = {}
    for line in lines.splitlines():
        if line.startswith("JOIN "):
            _, n, d, arrays = line.split(" ", 3)
            case = int(n), int(d)
            rows = tuple(ast.literal_eval(raw) for raw in arrays.split("|"))
            observed.setdefault(case, []).append(rows)
    return observed


def segments(seq):
    runs = []
    for item in seq:
        if runs and runs[-1][0] + runs[-1][1] == item:
            start, length = runs[-1]
            runs[-1] = start, length + 1
        else:
            runs.append((item, 1))
    return "[" + ",".join(f"({start},{length})" for start, length in runs) + "]"


def table(observed):
    if len(observed) != 6 or any(
        len(witnesses) != 4 for witnesses in observed.values()
    ):
        raise ValueError(
            "expected all six SHAKE shapes and four positive scalar/SIMD thread configurations"
        )
    entries = []
    for (n, d), witnesses in sorted(observed.items()):
        f, a, w = witnesses[0]
        if not all(rows == witnesses[0] for rows in witnesses):
            raise ValueError("successful worker publications depend on CPU/worker mode")
        entries.append(f"  ⟨{n},{d},{segments(f)},{segments(a)},{segments(w)}⟩")
    return (
        "import Parallel.SignJoinValues\nnamespace slhdsa.ParallelSignJoin\n"
        "structure PhysicalRows where\n  n : Nat\n  d : Nat\n  forest : List (Nat × Nat)\n"
        "  auth : List (Nat × Nat)\n  wots : List (Nat × Nat)\n  deriving DecidableEq\n"
        "/-- Source replay after the real pool join. Each pair is (first reference row, count). -/\n"
        "def observed : List PhysicalRows := [\n" + ",\n".join(entries) + "]\n"
        "end slhdsa.ParallelSignJoin\n"
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        if (
            table(symbolic_slots(folder))
            != (lean / "Parallel/SignJoinTable.lean").read_text()
        ):
            raise ValueError("Linux Arm row certificates changed")
        pkg = extract(folder, "aarch64-unknown-linux-gnu")
        if program(pkg) != dest.read_text():
            raise ValueError("post-join assembly differs from Lean")
        print(
            "Linux Arm: matched 24 physical-cell runs and all five post-join Aeneas declarations",
            flush=True,
        )
    module = "Parallel.PhaseTwoLinuxCoverage"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](
        module,
        [
            "slhdsa.ParallelSignJoin." + name
            for name in (
                "auth_copy",
                "layer_copy",
                "worker_correct",
                "standard_lookup",
                "read_order",
                "interpreted_ready",
                "rust_supported",
                "enabled_returns",
                "enabled_bytes",
                "roundtrip",
                "linux_join_correct",
            )
        ] + [f"ParallelLinuxArmAPI.shake_{bits}{speed}.{op}"
            for bits in (128, 192, 256) for speed in ("s", "f")
            for op in ("slh_sign_internal", "slh_sign", "sign", "sign_deterministic", "roundtrip")],
    )


if __name__ == "__main__":
    main()
