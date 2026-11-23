#!/usr/bin/env python3
"""Bind the width-polymorphic SHAKE batch helpers to the three production translations."""
import re
import runpy
import tempfile
from pathlib import Path

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
common = facade["common"]
LEAN = facade["LEAN"]
WIDTHS = {"aarch64-apple-darwin": 2, "aarch64-unknown-linux-gnu": 3, "x86_64-unknown-linux-gnu": 8}


def check(package, width):
    literal = f"{width}#usize"
    program = (LEAN / "Shakebatch/Program.lean").read_text().replace("machine.width", literal)
    program = program.replace("machine.permute", "shake256.parallel.permute")
    base_types = set(common["declarations"](common["body"](LEAN / "Slhdsa/Types.lean")))
    fresh_types = set(common["declarations"](common["body"](package / "Types.lean")))
    if fresh_types - base_types:
        raise ValueError(f"new batch input types at width {width}: {fresh_types - base_types}")
    reference = set(common["declarations"](common["body"](LEAN / "Slhdsa/Funs.lean")))
    declarations = list(common["declarations"](common["body"](package / "Funs.lean")))
    width_declaration = f"@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := {literal}"
    if width_declaration not in declarations:
        raise ValueError(f"unknown SIMD width in {package}")
    for decl in declarations:
        if decl == width_declaration or decl in reference:
            continue
        if decl.replace("shake256.parallel.WIDTH", literal) not in program:
            raise ValueError(f"unmatched width-{width} production function: {decl}")
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    external = list(common["declarations"](template))
    expected = f"axiom shake256.parallel.permute : Array (Array Std.U64 {literal}) 25#usize → Result (Array (Array Std.U64 {literal}) 25#usize)"
    if [" ".join(s.split()) for s in external] != [expected]:
        raise ValueError(f"unexpected boundary at width {width}: {external}")
    print(f"checked width {width} batch header, loads, writes and short hash calls", flush=True)


def check_nodes(package, width):
    literal = f"{width}#usize"
    program = (LEAN / "Shakebatch/NodesProgram.lean").read_text().replace("machine.width", literal)
    for name in ("Types.lean", "Funs.lean"):
        shared = set(common["declarations"](common["body"](LEAN / "Slhdsa" / name)))
        for decl in common["declarations"](common["body"](package / name)):
            if decl not in shared and decl not in program:
                raise ValueError(f"unmatched FORS declaration for width {width}: {decl}")
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    source = ["import Shakebatch.ForsNodes", "open Aeneas Aeneas.Std Result slhdsa", "open slhdsa.ShakeBatch",
              "variable [m : ShakeBatch.Machine]"]
    models = {"core.array.Array.map": "@_root_.core.array.Array.map",
              "shake.batch.short": "@ShakeBatch.shake.batch.short m",
              "shake.batch.pair": "@ShakeBatch.shake.batch.pair m"}
    seen = set()
    for decl in common["declarations"](template):
        match = re.fullmatch(r"(?:@\[.*?\]\s*)?axiom ([^\s]+)\s*(.*)", decl, re.DOTALL)
        if not match or match[1] not in models:
            raise ValueError(f"unknown FORS input at width {width}: {decl}")
        name, signature = match.groups()
        seen.add(name)
        signature = signature.replace(literal, "m.width")
        # The expected type and the concrete model must retain the same implicit binders.
        binders, sep, result = signature.rpartition(":")
        if not sep or not result.strip():
            raise ValueError(f"unrecognized FORS binding signature: {signature}")
        args = re.findall(r"[{(]([^ :{}()]+)\s*:", binders)
        source.append(f"example {signature} := {models[name]} {' '.join(args)}")
    if seen != set(models):
        raise ValueError(f"missing FORS input at width {width}: {seen}")
    common["run"](["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(source), text=True)
    print(f"checked width {width} recursive FORS nodes and bindings", flush=True)


if __name__ == "__main__":
    common["run"](["lake", "build", "Shakebatch.ForsNodes"], LEAN)
    facade["audit_theorems"]("Shakebatch.Header", ["slhdsa.ShakeBatch." + name for name in
        ("word_spec", "seed_rows", "put_spec", "address_rows", "high_bit", "header_spec")])
    facade["audit_theorems"]("Shakebatch.Read", ["slhdsa.ShakeBatch.read_spec"])
    facade["audit_theorems"]("Shakebatch.Pair", ["slhdsa.ShakeBatch.short_fips", "slhdsa.ShakeBatch.pair_fips",
        "Spec.Keccak.padded_fips"])
    facade["audit_theorems"]("Shakebatch.ForsNodes", ["slhdsa.ShakeBatch.fors_secrets", "slhdsa.ShakeBatch.fors_nodes"])
    for target, width in WIDTHS.items():
        with tempfile.TemporaryDirectory() as folder:
            package = facade["extract"]("rust", target, "Header", Path(folder),
                ("crate::shake::batch::short", "crate::shake::batch::pair"),
                ("crate::shake256::parallel::permute",))
            check(package, width)
            nodes = facade["extract"]("rust", target, "Nodes", Path(folder),
                ("crate::shake::fors_batch::nodes",), ("crate::shake::batch::short", "crate::shake::batch::pair"))
            check_nodes(nodes, width)
