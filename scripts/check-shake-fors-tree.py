#!/usr/bin/env python3
"""Certify the exact production horizontal FORS tree returned by both buffer phases."""

import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
sys.path.insert(0, str(HERE / "parallel-proof"))
from build import SRC, function

facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
table = facade["LEAN"] / "Shakeopt/ForsTreeTable.lean"


def program(folder, original):
    body = function(original, "fors_subtree_horiz").replace(
        "pub(super) fn fors_subtree_horiz<const N: usize>", "fn fors_subtree_horiz"
    )
    for old, new in (
        ("[u8; N]", "Digest"),
        ("[0u8; N]", "EMPTY"),
        ("node_index: u32", "node_index: Idx"),
        ("[0u32; 16]", "[Idx::ZERO; 16]"),
        ("[u32; WIDTH]", "[Idx; WIDTH]"),
    ):
        body = body.replace(old, new)
    probe = folder / "tree.rs"
    exe = folder / "tree"
    template = (HERE / "shake-fors/horizontal-tree.rs").read_text()
    probe.write_text(template.replace("// PRODUCTION", body))
    subprocess.run(
        ["rustc", "--edition=2021", "-O", "-Coverflow-checks=yes", probe, "-o", exe],
        check=True,
    )
    traces = subprocess.check_output([exe], text=True)
    terms = {}

    def intern(it):
        tag = next(it)
        if tag == "L":
            width, off = int(next(it)), int(next(it))
            expr = f".leaf {width} ({off})"
        elif tag == "B":
            packed, h, i = int(next(it)), int(next(it)), int(next(it))
            l, r = intern(it), intern(it)
            expr = f".branch {str(bool(packed)).lower()} ({h}) ({i}) {l} {r}"
        else:
            raise ValueError(tag)
        return terms.setdefault(expr, f"t{len(terms)}")

    roots = []
    for line in traces.splitlines():
        it = iter(line.split())
        if int(next(it)) != len(roots) + 3:
            raise ValueError("missing tree height")
        roots.append(intern(it))
        if next(it, None) is not None:
            raise ValueError("extra node")
    if len(roots) != 12:
        raise ValueError("incomplete height coverage")
    declarations = "\n".join(
        f"private def {name} : Shape := {value}" for value, name in terms.items()
    )
    return (
        "import Parallel.KeygenShape\nnamespace Shakeopt.ForsTree\nopen ParallelKeygen.Tree\n"
        + declarations
        + "\ndef schedule : List Shape := ["
        + ", ".join(roots)
        + "]\nend Shakeopt.ForsTree\n"
    )


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.elan/bin:{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    )
    source = (SRC / "shake/fors_batch.rs").read_text()
    with tempfile.TemporaryDirectory() as tmp:
        folder = Path(tmp)
        if program(folder, source) != table.read_text():
            raise ValueError("changed horizontal FORS dependencies")
        old = "let parents = pair_active(seed, &addrs, &left, &right, count);"
        if source.count(old) != 1:
            raise ValueError("changed FORS tail merge")
        bad = program(
            folder, source.replace(old, old.replace("&left, &right", "&right, &left"))
        )
        proof = (
            (table.parent / "ForsTree.lean")
            .read_text()
            .replace("import Shakeopt.ForsTreeTable", bad)
        )
        result = subprocess.run(
            ["lake", "env", "lean", "--stdin"],
            cwd=facade["LEAN"],
            input=proof,
            text=True,
            stdout=subprocess.PIPE,
        )
        if result.returncode == 0 or "decide" not in result.stdout:
            raise ValueError("mutated tail merge did not fail the Lean validity check")
    module = "Shakeopt.ForsWideSignature"
    facade["run"](["lake", "build", module], facade["LEAN"])
    facade["audit_theorems"](
        module,
        [
            "Shakeopt.ForsTree.root_fips",
            "Shakeopt.ForsTree.index_fits",
            "Shakeopt.ForsWideSignature.sign_fips",
            "Shakeopt.ForsWideSignature.signature_eq",
        ],
    )


if __name__ == "__main__":
    main()
