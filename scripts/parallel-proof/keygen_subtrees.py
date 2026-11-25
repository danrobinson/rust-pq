"""Lift the returned expression of each hosted SHAKE XMSS traversal."""

import subprocess
from pathlib import Path

from build import SRC, function


def program(directory, batch=None):
    if batch is None:
        batch = (SRC / "shake/batch.rs").read_text()
    production = "\n".join(
        function(batch, f) for f in ("xmss_subtree", "xmss_subtree_fallback")
    )
    production = (
        production.replace("pub(super) fn", "fn")
        .replace("[u8; N]", "Digest")
        .replace("[0u8; N]", "EMPTY")
    )
    # The digest type no longer carries N, so supply each erased const argument.
    for name in ("xmss_subtree_fallback", "keygen", "thash_pair", "pair_active"):
        production = production.replace(name + "(", name + "::<N>(")
    template = Path(__file__).with_name("keygen-subtrees.rs").read_text()
    template = template.replace("// PRODUCTION", production).replace(
        "ADDRESS_PATH", str(SRC / "address.rs")
    )
    declarations = []
    by_shape = {}

    def intern(tokens):
        tag = next(tokens)
        if tag == "L":
            k, off = int(next(tokens)), int(next(tokens))
            expr = f".leaf {k} ({off})"
        elif tag == "B":
            packed, hd, off = (int(next(tokens)) for _ in range(3))
            left, right = intern(tokens), intern(tokens)
            expr = f".branch {str(bool(packed)).lower()} ({hd}) ({off}) {left} {right}"
        else:
            raise ValueError(tag)
        if expr not in by_shape:
            name = f"shape{len(by_shape)}"
            declarations.append(f"private def {name} : Shape := {expr}")
            by_shape[expr] = name
        return by_shape[expr]

    tables = {}
    for width in (3, 8):
        src, binary = directory / "tree.rs", directory / "tree"
        src.write_text(template.replace("PROOF_WIDTH", str(width)))
        subprocess.run(
            [
                "rustc",
                "--edition=2021",
                "-Awarnings",
                "-O",
                "-Coverflow-checks=yes",
                src,
                "-o",
                binary,
            ],
            check=True,
        )
        table = {}
        for line in subprocess.check_output([binary], text=True).splitlines():
            it = iter(line.split())
            n, z = int(next(it)), int(next(it))
            witness = intern(it)
            if next(it, None) is not None or table.setdefault(z, witness) != witness:
                raise ValueError(
                    f"width {width}: digest-dependent or incomplete traversal at N={n}, h={z}"
                )
        if set(table) != set(range(1, 10)):
            raise ValueError("missing subtree height")
        tables[width] = "[" + ", ".join(table[z] for z in range(1, 10)) + "]"
    return (
        "import Parallel.KeygenShape\n\nnamespace ParallelKeygen.Tree\n"
        + "\n".join(declarations)
        + f"\ndef schedule (wide : Bool) : List Shape :=\n  if wide then {tables[8]}\n  else {tables[3]}\n"
        + "end ParallelKeygen.Tree\n"
    )
