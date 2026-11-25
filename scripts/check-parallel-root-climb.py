#!/usr/bin/env python3
"""Extract the phase-one finisher's path walk directly from the production closure."""
from pathlib import Path
import os
import re
import runpy
import tempfile

ticket = runpy.run_path(str(Path(__file__).with_name("check-parallel-wots-ticket.py")))
common, lean = ticket["common"], ticket["lean"]


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    file = crate / "src/slh/parallel.rs"
    code = file.read_text()
    signer = ticket["shared"]["signer"].function(code, "sign")
    start = "                    let mut index = leaf_idx;"
    stop = "                    roots.push(node);"
    if signer.count(start)!=1 or signer.count(stop)!=1:
        raise ValueError("last-finisher root loop boundaries changed")
    body = start + signer.split(start)[1].split(stop)[0]
    expected_inputs = ("let hp = p.hp as usize;", "let (addr, leaf_idx) = layers[j];",
                       "let tree_addr = addr.with_type(TREE);", 'let mut node = *leaf_pks[j].get().expect("leaf PK filled");')
    before = signer.rsplit("for j in 0..leaf_pk_count {", 1)[1].split(start, 1)[0]
    if signer.count(expected_inputs[0]) != 1 or before.split() != " ".join(expected_inputs[1:]).split():
        raise ValueError("worker height, leaf, address or selected layer changed")
    roots_start = "                let mut roots: Vec<[u8; N]> ="
    roots_stop = "                let _ = sig_fors_cell.set"
    if signer.count(roots_start) != 1 or signer.count(roots_stop) != 1:
        raise ValueError("worker root table boundaries changed")
    for declaration in ("let d = p.d as usize;", "let leaf_pk_count = d.saturating_sub(1);",
                        "let _ = roots_cell.set(roots);"):
        if signer.count(declaration) != 1:
            raise ValueError("root count or published vector changed")
    table = roots_start + signer.split(roots_start)[1].split(roots_stop)[0]
    signatures = """
fn all_roots<const N: usize>(p: &Params, d: usize, hp: usize, sig_fors: Vec<u8>, md: &[u8],
    seed: &Seed<N>, fors_addr: Adrs, layers: Vec<(Adrs, u32)>, leaf_pks: Vec<OnceLock<[u8; N]>>,
    leaf_pk_count: usize, xmss_auth: Vec<[u8; N]>) -> Vec<[u8; N]> {
"""
    file.write_text(code + signatures + table + "\nroots\n}\n" + """
fn root_walk<const N: usize>(p: &Params, j: usize, hp: usize, tree_addr: Adrs, leaf_idx: u32,
    mut node: [u8; N], xmss_auth: &Vec<[u8; N]>, seed: &Seed<N>) -> [u8; N] {
""" + body + "\nnode\n}\n")
    return common["extract_target"](target, folder/"generated", ["crate::shake::slh::parallel::root_walk", "crate::shake::slh::parallel::all_roots"],
        ["crate::shake::xmss::hash2", "crate::shake::fors::fors_pk_from_sig", "std::sync"], crate=crate, features="parallel,platform-sha2")


def bodies(pkg):
    decls = runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))["decls"]
    original = set(decls(common["ROOT"]/"lean/Slhdsa/Funs.lean", "slhdsa"))
    funcs = decls(pkg/"Funs.lean", "CacheopsRust")
    imported = [d for d in funcs if "def shake.slh.parallel." not in d]
    if any(d not in original for d in imported):
        raise ValueError("unmatched address operation in phase-one root walk")
    if set(re.findall(r"^axiom ([\w.]+)", (pkg/"FunsExternal_Template.lean").read_text(), re.M)) != {
            "shake.xmss.hash2", "shake.fors.fors_pk_from_sig", "std.sync.once_lock.OnceLock.get"}:
        raise ValueError("unexpected external call in last-finisher root computation")
    return funcs


def program(pkg):
    body = "\n\n".join(d for d in bodies(pkg) if "def shake.slh.parallel.root_walk" in d)
    body = body.replace("shake.slh.parallel.", "").replace("shake.xmss.hash2", "hash")
    body = body.replace("{N : Std.Usize}", "{N : Std.Usize} (hash : Hash N)")
    for call in ("root_walk_loop.body ", "root_walk_loop "):
        body = body.replace(call, call + "hash ")
    return ("import Slhdsa.Proofs.ShakeXmss\nopen Aeneas Aeneas.Std Result ControlFlow\n"
            "namespace slhdsa.ParallelRootWalk\nabbrev Hash (N : Usize) := Array U8 N → address.Adrs → Array U8 N → Array U8 N → Result (Array U8 N)\n"
            + body.strip() + "\nend slhdsa.ParallelRootWalk\n")


def table_program(pkg):
    body = "\n\n".join(d for d in bodies(pkg) if "def shake.slh.parallel.all_roots" in d)
    body = body.replace("shake.slh.parallel.", "").replace("shake.xmss.hash2", "engine.hash")
    body = body.replace("shake.fors.fors_pk_from_sig", "engine.recover")
    body = body.replace("std.sync.once_lock.OnceLock.get", "ParallelSignJoin.readCell").replace("std.sync.once_lock.OnceLock", "Option")
    return ("""import Parallel.RootWalk
import Parallel.SignJoinProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelRootWalk
class Engine where
  hash {N : Usize} : Hash N
  recover {N : Usize} : params.Params → Slice U8 → Slice U8 → Array U8 N → address.Adrs → Result (Array U8 N)
set_option linter.concreteInstances false
variable [engine : Engine]
""" + body + "\nend slhdsa.ParallelRootWalk\n")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    target_file = lean/"Parallel/RootWalkProgram.lean"
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"):
            pkg = extract(Path(tmp)/target, target)
            if program(pkg).split()!=target_file.read_text().split():
                raise ValueError(f"phase-one root climb differs on {target}")
            if table_program(pkg).split() != (lean/"Parallel/RootTableProgram.lean").read_text().split():
                raise ValueError(f"phase-one root table differs on {target}")
            file = pkg/"Funs.lean"
            raw = file.read_text()
            for before, after in [("seed a_node node sibling", "seed a_node sibling node"),
                                  ("let i2 ← i + i1", "let i2 ← i + j")]:
                file.write_text(raw.replace(before, after))
                if program(pkg).split()==target_file.read_text().split() and table_program(pkg).split()==(lean/"Parallel/RootTableProgram.lean").read_text().split():
                    raise ValueError(f"mutation escaped root-walk check on {target}")
    module = "Parallel.RootTableHosted"
    common["facade"]["run"](["lake","build",module], lean)
    common["facade"]["audit_theorems"](module, ["slhdsa.ParallelRootWalk." + n for n in
        ("walk_spec", "root_spec", "shake_root", "table_spec", "hosted_table")])


if __name__ == "__main__":
    main()
