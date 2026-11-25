#!/usr/bin/env python3
"""Replay the hosted keygen callers, fetched output slots and both split policies."""

import os
import re
import runpy
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE / "parallel-proof"))
sys.dont_write_bytecode = True
import keygen_subtrees

common = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
facade = common["facade"]
ROOT, LEAN = common["ROOT"], common["LEAN"]
split = runpy.run_path(str(HERE / "check-split-tree.py"))
FAMILIES = ("crate::", "crate::shake::")
SETS = tuple(
    f"{f}_{n}{mode}"
    for f in ("sha2", "shake")
    for n in (128, 192, 256)
    for mode in "sf"
)


def declarations(path, ns):
    return set(facade["common"]["declarations"](facade["common"]["body"](path, ns)))


def check_widths():
    source = (ROOT / "rust/src/shake256/parallel.rs").read_text()
    actual = re.findall(
        r"#\[cfg\(([^\n]+)\)\]\s*pub\(crate\) const WIDTH: usize = (\d+);", source
    )
    expected = [
        ('target_arch = "x86_64"', "8"),
        ('all(target_arch = "aarch64", target_vendor = "apple")', "8"),
        ('all(target_arch = "aarch64", not(target_vendor = "apple"))', "3"),
    ]
    if actual != expected:
        raise ValueError(
            "review the hosted CPU widths and their projected subtree schedules"
        )


def check_plan(target, directory):
    # Project the local arithmetic and its explicit queue invocation limit,
    # retaining both cfg arms verbatim. Only the OS call and queue are cut.
    crate = directory / "policy-crate"
    crate.mkdir(parents=True)
    source = ROOT / "rust"
    for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml"):
        if (source / name).exists():
            shutil.copy(source / name, crate / name)
    shutil.copytree(source / "src", crate / "src")
    (crate / "benches").mkdir()
    (crate / "benches/platforms.rs").touch()
    path = crate / "src/slh/parallel.rs"
    text = path.read_text()
    entry = split["function"](text, "keygen")
    policy = entry[entry.index("    if threads < 2") : entry.index("    let nodes:")]
    invocation = re.search(r"crate::pool::execute\((.*?), true, &fill\);", entry)
    if not invocation:
        raise ValueError("missing keygen pool invocation")
    path.write_text(
        text
        + "\nfn proof_keygen_plan(p: &Params, threads: usize) -> Option<(u32,usize,usize)> {\n"
        + policy
        + "    Some((sub_h, count, "
        + invocation[1]
        + "))\n}\n"
    )
    package = common["extract_target"](
        target,
        directory / "policy",
        ["crate::slh::parallel::proof_keygen_plan"],
        [],
        crate=crate,
        features="parallel,platform-sha2",
    )
    fresh = [
        x
        for x in declarations(package / "Funs.lean", "CacheopsRust")
        if x.startswith("def slh.parallel.proof_keygen_plan")
    ]
    arch = "X86" if target.startswith("x86_64-") else "Arm"
    checked = (
        (LEAN / "Parallel/KeygenPlan.lean")
        .read_text()
        .split("namespace " + arch + "\n")[1]
        .split("\nend " + arch)[0]
    )
    if fresh != [checked.strip()]:
        raise ValueError(f"{target}: keygen plan arithmetic differs from Lean")


def check_target(target, directory):
    api = tuple(
        f"crate::sets::{s}::{entry}"
        for s in SETS
        for entry in ("slh_keygen_internal", "keygen")
    )
    roots = [f + "slh::slh_keygen_internal" for f in FAMILIES] + list(api)
    cuts = [
        f + name
        for f in FAMILIES
        for name in ("slh::parallel::keygen", "xmss::xmss_node", "hash::seed_ctx")
    ]
    cuts.append("crate::util::block")
    package = common["extract_target"](
        target, directory / "caller", roots, cuts, features="parallel,platform-sha2"
    )
    model = (LEAN / "Parallel/KeygenProgram.lean").read_text()
    seen = set()
    for kind in ("Types", "Funs"):
        portable = declarations(LEAN / f"Slhdsa/{kind}.lean", "slhdsa")
        for declaration in declarations(package / f"{kind}.lean", "CacheopsRust"):
            name = re.search(r"\b(?:def|structure)\s+(\S+)", declaration)
            if declaration not in model and declaration not in portable:
                raise ValueError(
                    f"{target}: uncovered keygen declaration {declaration[:150]}"
                )
            if name:
                seen.add(name[1])
    expected = {
        f"sets.{s}.{entry}" for s in SETS for entry in ("slh_keygen_internal", "keygen")
    }
    for family in ("", "shake."):
        outer = family + "slh.slh_keygen_internal"
        expected.update(
            (
                outer,
                outer + ".closure",
                outer + ".closure.Insts.CoreOpsFunctionFnOnceTupleArrayU8N",
            )
        )
    if expected - seen:
        raise ValueError(f"{target}: missing keygen declarations {expected - seen}")
    package = common["extract_target"](
        target,
        directory / "node",
        ["crate::shake::xmss::xmss_node"],
        [
            "crate::shake::" + name
            for name in (
                "batch::available",
                "batch::xmss_subtree",
                "wots::wots_pk_gen",
                "xmss::hash2",
            )
        ],
        features="parallel,platform-sha2",
    )
    declaration = next(
        d
        for d in declarations(package / "Funs.lean", "CacheopsRust")
        if "def shake.xmss.xmss_node\n" in d
    )
    portable = declarations(LEAN / "Slhdsa/Funs.lean", "slhdsa")
    if declarations(package / "Funs.lean", "CacheopsRust") - portable - {declaration}:
        raise ValueError(f"{target}: unverified SHAKE node dependency")
    if declaration not in (LEAN / "Parallel/KeygenShake.lean").read_text():
        raise ValueError(f"{target}: recursive SHAKE node dispatch changed")
    print(
        f"{target}: source matches both parallel key writers, their serial closures, SHAKE node and all 24 typed entry points",
        flush=True,
    )


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".cargo/bin"),
            str(Path.home() / ".elan/bin"),
            os.environ["PATH"],
        ]
    )
    sysroot = subprocess.check_output(
        ["rustc", "--print", "sysroot"], cwd=ROOT / ".tools/aeneas/charon", text=True
    ).strip()
    option = (
        Path(sysroot) / "lib/rustlib/src/rust/library/core/src/option.rs"
    ).read_text()
    unwrap = option.split("fn unwrap_or_else<F>(self, f: F)", 1)[1].split("\n    }", 1)[
        0
    ]
    body = re.sub(r"\s+", "", unwrap.split("{", 1)[1])
    if body != "matchself{Some(x)=>x,None=>f(),}":
        raise ValueError(
            "core::option::Option::unwrap_or_else differs from the checked branch semantics"
        )
    check_widths()
    queue = (ROOT / "rust/src/slh/parallel.rs").read_text()
    split["check_keygen_queue"](queue)
    # Bind the participants calculation, including pool contention and spawn failure.
    pool = (ROOT / "rust/src/pool.rs").read_text()
    canonical = lambda text: re.sub(r"//[^\n]*|\s+", "", text)
    for effect in (
        "if max_threads <= 1 { f(); return; } let (pool, spawned) = ensure_workers(); let n_workers = (max_threads - 1).min(spawned); dispatch(pool, n_workers, scrub, f);",
        "if n_workers == 0 { f(); return; } let Some(_guard) = PoolGuard::claim(pool, n_workers, scrub, f) else { f(); return; };",
    ):
        if canonical(effect) not in canonical(pool):
            raise ValueError("pool participant selection changed")
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        for target in facade["TARGETS"]:
            check_target(target, root / target)
            check_plan(target, root / target)
        actual = keygen_subtrees.program(root)
        if actual != (LEAN / "Parallel/KeygenShapeTable.lean").read_text():
            raise ValueError(
                "SHAKE subtree source produces a different dependency tree"
            )
        text = (ROOT / "rust/src/shake/batch.rs").read_text()
        before = "&root_adrs, &lvl1[0], &lvl1[1]"
        after = "&root_adrs, &lvl1[1], &lvl1[0]"
        if text.count(before) != 1:
            raise ValueError("SHAKE height-two mutation control needs review")
        mutated = keygen_subtrees.program(root, text.replace(before, after))
        if mutated == actual:
            raise ValueError("subtree projection failed to detect a swapped child")
    # Includes the production parent-reduction loop, which is shared by both families.
    split["main"]()
    facade["run"](
        [
            "lake",
            "build",
            "Parallel.KeygenPublic",
            "Parallel.KeygenNativeHashes",
            "Parallel.KeygenDispatch",
        ],
        LEAN,
    )
    proof = mutated.replace(
        "end ParallelKeygen.Tree",
        "example : valid ((schedule true)[1]?.getD (.leaf 1 0)) 2 = false := by decide\nend ParallelKeygen.Tree",
    )
    facade["run"](["lake", "env", "lean", "--stdin"], LEAN, input=proof, text=True)
    for module, theorems in {
        "KeygenDispatch": [
            "slhdsa.ParallelKeygenHost.worker_from_plan",
            "slhdsa.ParallelKeygenHost.fetch_safe",
        ],
        "KeygenPlan": [
            "slhdsa.ParallelKeygenPlan.arm",
            "slhdsa.ParallelKeygenPlan.x86",
        ],
        "KeygenPublic": [
            "slhdsa.ParallelKeygenHost." + name + "_public"
            for name in ("s2_arm", "s2_x86", "sh_linux", "sh_apple", "sh_x86")
        ],
        "KeygenNativeHashes": [
            host + ".slhdsa.ParallelKeygenHost." + theorem
            for host, name in (
                ("KeygenLinuxHashes", "linux"),
                ("KeygenAppleHashes", "apple"),
                ("KeygenX86Hashes", "x86"),
            )
            for theorem in ("ShNode." + name + "_keys", "sh_" + name + "_public")
        ],
        "KeygenTickets": [
            "ParallelKeygen.geometry",
            "ParallelKeygen.joined_root",
            "ParallelKeygen.finished",
        ],
        "KeygenHost": [
            "slhdsa.ParallelKeygenHost.worker_value",
            "slhdsa.ParallelKeygenHost.S2.caller_fips",
            "slhdsa.ParallelKeygenHost.Sh.caller_fips",
        ],
        "KeygenTree": [
            "slhdsa.ParallelKeygenHost.table_valid",
            "slhdsa.ParallelKeygenHost.tree_spec",
        ],
        "KeygenSha2": [
            "slhdsa.ParallelKeygenHost.arm_keys",
            "slhdsa.ParallelKeygenHost.x86_keys",
        ],
        "KeygenPlatforms": [
            "slhdsa.ParallelKeygenHost.ShNode." + host
            for host in ("linux_keys", "apple_keys", "x86_keys")
        ],
    }.items():
        facade["audit_theorems"]("Parallel." + module, theorems)


if __name__ == "__main__":
    main()
