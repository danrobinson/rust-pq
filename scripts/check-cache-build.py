#!/usr/bin/env python3
"""Bind cached tree construction to the FIPS node recurrence checked by Lean."""

import os
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent


def body(source, name):
    match = re.search(rf"^( *)((?:pub(?:\(super\))? )?fn {name}(?:<|\())", source, re.M)
    if not match:
        raise ValueError(f"missing builder function {name}")
    end = source.index("\n" + match[1] + "}", match.end())
    return source[match.start() : end + len(match[1]) + 2]


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".elan/bin"),
            str(Path.home() / ".cargo/bin"),
            os.environ["PATH"],
        ]
    )
    src = ROOT / "rust/src"
    cache = (src / "cache.rs").read_text()
    before, shake = cache.split("mod shake_ops {")
    sha2 = before.split("mod sha2_ops {")[1]
    address = (src / "address.rs").read_text()
    methods = "\n".join(
        body(address, name)
        for name in (
            "new",
            "with_layer",
            "with_tree",
            "with_type",
            "with_keypair",
            "with_word2",
            "with_word3",
        )
    )
    methods = methods.replace("layer: u32", "layer: Layer").replace(
        "tree: u64", "tree: TreeIndex"
    )
    methods = methods.replace(
        "layer: 0, tree: 0", "layer: Layer::Zero, tree: TreeIndex::Zero"
    )
    model = (
        (HERE / "cache-proof/builder.rs")
        .read_text()
        .replace("// ADDRESS_METHODS", methods)
    )
    for marker, source, names in [
        ("COMMON_FUNCTIONS", cache, ("level_offset", "tree_node_count")),
        ("SHA2_FUNCTIONS", sha2, ("build_xmss_tree", "build_leaves_parallel")),
        (
            "SHAKE_FUNCTIONS",
            shake,
            ("build_xmss_tree", "build_leaves_parallel", "fill_leaves_chunk"),
        ),
        ("SIMD_FUNCTIONS", shake, ("hash_pairs", "fill_xmss_leaves")),
    ]:
        functions = "\n".join(body(source, n) for n in names)
        functions = functions.replace("[u8; N]", "[Token; N]").replace(
            "[0u8; N]", "[Token::Empty; N]"
        )
        functions = functions.replace("layer: u32", "layer: Layer").replace(
            "tree_index: u64", "tree_index: TreeIndex"
        )
        model = model.replace("// " + marker, functions)
    with tempfile.TemporaryDirectory() as tmp:
        file, exe = Path(tmp) / "builder.rs", Path(tmp) / "builder"
        for width in (3, 8):
            file.write_text(model.replace("PROOF_WIDTH", str(width)))
            for flags in ([], ["--cfg", 'feature="parallel"']):
                subprocess.run(
                    [
                        "rustc",
                        "--edition=2021",
                        "-Awarnings",
                        "-O",
                        "-C",
                        "overflow-checks=yes",
                        *flags,
                        file,
                        "-o",
                        exe,
                    ],
                    check=True,
                )
                subprocess.run([exe], check=True)
    facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
    subprocess.run(
        ["lake", "build", "Cachepath.Construction"], cwd=ROOT / "lean-hw", check=True
    )
    facade["audit_theorems"](
        "Cachepath.Construction",
        ["slhdsa.cache.constructed", "slhdsa.cache.built_xmss"],
    )


if __name__ == "__main__":
    main()
