#!/usr/bin/env python3
"""Bind the full last-finisher XMSS authentication table to its native reducer."""

import os, re, runpy, tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
base = runpy.run_path(str(HERE / "check-parallel-forest-pack.py"))
common, lean, decls = base["common"], base["lean"], base["decls"]


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    path = crate / "src/slh/parallel.rs"
    source = path.read_text()
    sign = base["ticket"]["shared"]["signer"].function(source, "sign")
    start = "let mut xmss_auth: Vec<[u8; N]>"
    stop = "let mut roots: Vec<[u8; N]>"
    if sign.count(start) != 1 or sign.count(stop) != 1:
        raise ValueError("auth table region changed")
    body = start + sign.split(start)[1].split(stop)[0]
    path.write_text(
        source
        + """
fn auth_table<const N:usize>(d:usize,hp:usize,layers:&Vec<(Adrs,u32)>,xmss_meta:&Vec<XmssAuthMeta>,
    xmss_slots:&Vec<OnceLock<[u8;N]>>,seed:&Seed<N>)->Vec<[u8;N]> {
"""
        + body
        + "xmss_auth\n}\n"
    )
    return common["extract_target"](
        target,
        folder / "generated",
        ["crate::shake::slh::parallel::auth_table"],
        ["crate::shake::slh::parallel::reduce_tree", "std::sync"],
        crate=crate,
        features="parallel,platform-sha2",
    )


def program(pkg):
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    fs = decls(pkg / "Funs.lean", "CacheopsRust")
    ds = [d for d in fs if "def shake.slh.parallel.auth_table" in d]
    ts = decls(pkg / "Types.lean", "CacheopsRust")
    ms = [d for d in ts if "structure shake.slh.parallel.XmssAuthMeta" in d]
    if (
        len(ds) != 5
        or len(ms) != 1
        or set(ts)
        - set(ms)
        - set(decls(lean.parent / "lean/Slhdsa/Types.lean", "slhdsa"))
        or set(fs) - set(ds) - known
    ):
        raise ValueError("XMSS auth table dependencies changed")
    if set(
        re.findall(
            r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M
        )
    ) != {"std.sync.once_lock.OnceLock.get", "shake.slh.parallel.reduce_tree"}:
        raise ValueError("XMSS auth table cut points changed")
    body = (
        "\n\n".join(ms + ds)
        .replace(
            "shake.slh.parallel.reduce_tree",
            "@ParallelReduceNative.reduce_tree ParallelReduceNative.shakeFamily N",
        )
        .replace("shake.slh.parallel.", "")
        .replace("std.sync.once_lock.OnceLock.get", "ParallelSignJoin.readCell")
        .replace("std.sync.once_lock.OnceLock", "Option")
    )
    start = "    let node ←\n      if «meta».split"
    end = "    let xmss_auth1 ←"
    if body.count(start) != 1 or body.count(end) < 1:
        raise ValueError("XMSS metadata dispatch changed")
    nodes = body.split(start, 1)[1].split(end, 1)[0]
    node = "if «meta».split" + nodes.rstrip()
    helper = (
        """
def read_node {N : Usize} (xmss_slots : alloc.vec.Vec (Option (Array U8 N))) (seed : Array U8 N)
    (tree_addr : address.Adrs) («meta» : XmssAuthMeta) : Result (Array U8 N) :=
  """
        + node
        + "\n"
    )
    body = body.replace(
        "    let node ←\n      " + node,
        "    let node ← read_node xmss_slots seed tree_addr «meta»",
    ).replace("@[rust_loop_body]", helper + "\n@[rust_loop_body]", 1)
    return (
        "import Parallel.ReduceNative\nimport Parallel.SignJoinProgram\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace slhdsa.ParallelAuthTable\nnoncomputable section\n"
        + body
        + "\nend\nend slhdsa.ParallelAuthTable\n"
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    checked = (lean / "Parallel/AuthTableProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as folder:
        for target in (
            "aarch64-apple-darwin",
            "aarch64-unknown-linux-gnu",
            "x86_64-unknown-linux-gnu",
        ):
            pkg = extract(Path(folder) / target, target)
            if program(pkg).split() != checked:
                raise ValueError(f"{target}: XMSS auth table changed")
            path = pkg / "Funs.lean"
            original = path.read_text()
            for old, new in [
                ("let i ← j * hp", "let i ← j + hp"),
                ("if «meta».split = 0#u32", "if «meta».height = 0#u32"),
                (
                    "seed tree_addr «meta».root_idx i3",
                    "seed tree_addr «meta».height i3",
                ),
            ]:
                path.write_text(
                    base["ticket"]["shared"]["signer"].once(original, old, new)
                )
                try:
                    match = program(pkg).split() == checked
                except ValueError:
                    match = False
                if match:
                    raise ValueError("accepted changed auth table data flow")
            path.write_text(original)
    facade = base["ticket"]["shared"]["facade"]
    module = "Parallel.AuthTableHosted"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](
        module,
        [
            "slhdsa.ParallelAuthTable." + name
            for name in ["read_spec", "table_spec", "published_auth"]
        ]
        + [
            name + ".slhdsa.ParallelAuthTable.published_auth"
            for name in ["AuthTableApple", "AuthTableLinux", "AuthTableX86"]
        ],
    )


if __name__ == "__main__":
    main()
