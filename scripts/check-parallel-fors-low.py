#!/usr/bin/env python3
"""Check the scalar low FORS worker, including every indexed publication."""

import os
import re
import runpy
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
scalar = runpy.run_path(str(HERE / "check-parallel-scalar-fors.py"))
common, lean, decls = scalar["common"], scalar["lean"], scalar["decls"]
signer = scalar["ticket"]["shared"]["signer"]


def project(rust):
    sign = signer.function(rust, "sign")
    emit = sign.split("let run = ||")[0]
    for expression in (
        "let a = p.a;",
        "let k = p.k as usize;",
        "let fors_indices = base_2b(md, a, k);",
        "let fors_stride = a as usize + 1;",
        "kind: WorkKind::ForsTreeLow { tree: t, low_h },",
    ):
        if emit.count(expression) != 1:
            raise ValueError("scalar low FORS queue fields changed")
    if (
        emit.split("if !built_shake_simd_fors {")[1].count(
            "let low_h = a.min(fors_target);"
        )
        != 1
    ):
        raise ValueError("scalar fallback FORS height changed")
    worker = sign.split("match item.kind {")[-1]
    start = "WorkKind::ForsTreeLow { tree: t, low_h } => {"
    end = "WorkKind::ForsNodeDirect {"
    if worker.count(start) != 1 or worker.count(end) != 1:
        raise ValueError("scalar low work definition changed")
    arm = worker.split(start)[1].split(end)[0].strip()
    replacements = [
        (
            'fors_direct[base].set(secret).expect("unique FORS sk slot");',
            "let first = (base, secret);",
        ),
        (
            'fors_direct[base + 1 + j as usize]\n                            .set(node)\n                            .expect("unique FORS low node slot");',
            "journal[j as usize] = (base + 1 + j as usize, node);",
        ),
    ]
    for old, new in replacements:
        arm = signer.once(arm, old, new)
    if not arm.endswith("}"):
        raise ValueError("unexpected scalar low worker tail")
    return (
        rust
        + """
fn scalar_low_ticket<const N:usize>(sk:&[u8;N],seed:&Seed<N>,fors_addr:Adrs,
    fors_indices:&Vec<u32>,t:u32,a:u32,low_h:u32,fors_stride:usize,
    mut journal:[(usize,[u8;N]);14]) -> ((usize,[u8;N]),[(usize,[u8;N]);14]) {
    """
        + arm[:-1]
        + "(first,journal)\n}\n"
    )


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    path = crate / "src/slh/parallel.rs"
    rust = path.read_text()
    for old, new in [
        ("fors_direct[base].set(secret)", "fors_split[base].set(secret)"),
        ("fors_direct[base + 1 + j as usize]", "fors_direct[base + j as usize]"),
    ]:
        try:
            project(signer.once(rust, old, new))
        except (ValueError, AssertionError):
            pass
        else:
            raise ValueError("accepted changed scalar low publication")
    path.write_text(project(rust))
    return common["extract_target"](
        target,
        folder / "generated",
        ["crate::shake::slh::parallel::scalar_low_ticket"],
        ["crate::shake::fors::fors_node", "crate::shake::fors::fors_sk_gen"],
        crate=crate,
        features="parallel,platform-sha2",
    )


def program(pkg):
    known = set(decls(lean.parent / "lean/Slhdsa/Funs.lean", "slhdsa"))
    fs = decls(pkg / "Funs.lean", "CacheopsRust")
    gs = [d for d in fs if "def shake.slh.parallel.scalar_low_ticket" in d]
    ext = set(
        re.findall(
            r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M
        )
    )
    if ext != {"shake.fors.fors_node", "shake.fors.fors_sk_gen"} or any(
        d not in known for d in fs if d not in gs
    ):
        raise ValueError("unexpected dependency in extracted scalar low FORS")
    if not set(decls(pkg / "Types.lean", "CacheopsRust")).issubset(
        decls(lean.parent / "lean/Slhdsa/Types.lean", "slhdsa")
    ):
        raise ValueError("scalar low FORS type changed")
    return (
        """import Parallel.ScalarForsProgram
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelScalarFors
variable [host : Host]

"""
        + ("\n\n".join(gs))
        .replace("shake.slh.parallel.scalar_low_ticket", "low_ticket")
        .replace("shake.fors.fors_node", "node")
        + "\nend slhdsa.ParallelScalarFors\n"
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    checked = (lean / "Parallel/ScalarForsLowProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as tmp:
        for target in scalar["targets"]:
            pkg = extract(Path(tmp) / target, target)
            if program(pkg).split() != checked:
                raise ValueError("extracted scalar low FORS worker changed")
            path = pkg / "Funs.lean"
            body = path.read_text()
            for old, new in [
                ("let i ← idx >>> j", "let i ← idx >>> a"),
                ("fors_sk_gen sk seed fors_addr i3", "fors_sk_gen sk seed fors_addr t"),
            ]:
                path.write_text(signer.once(body, old, new))
                if program(pkg).split() == checked:
                    raise ValueError("accepted changed scalar FORS value input")
            path.write_text(body)
    module = "Parallel.ScalarForsLowHosted"
    facade = scalar["ticket"]["shared"]["facade"]
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](
        module,
        [
            "slhdsa.ParallelScalarFors.low_published",
            "slhdsa.ParallelScalarFors.low_from_message",
        ],
    )


if __name__ == "__main__":
    main()
