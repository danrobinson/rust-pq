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


def check_calls(package, width, filename, models, uses_width, stream=False, aliases=None):
    literal = f"{width}#usize"
    program = (LEAN / "Shakebatch" / filename).read_text().replace("machine.width", literal)
    for generic, production in (aliases or {}).items():
        program = program.replace(generic, production)
    if stream:
        for generic, production in {"stream.State": "shake256.Sponge", "stream.start": "shake.hash.start",
                                    "stream.digest": "shake.hash.digest", "stream.absorb": "shake256.Sponge.absorb"}.items():
            program = program.replace(generic, production)
        text = (package / "TypesExternal_Template.lean").read_text()
        external_types = common["declarations"](text[text.index("/-- "):])
        if list(external_types) != ["axiom shake256.Sponge : Type"]:
            raise ValueError(f"unexpected recovery state types at width {width}")
    for name in ("Types.lean", "Funs.lean"):
        shared = set(common["declarations"](common["body"](LEAN / "Slhdsa" / name)))
        for decl in common["declarations"](common["body"](package / name)):
            if uses_width and decl == f"@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := {literal}":
                continue
            normalized = "\n".join(line.rstrip() for line in decl.replace("shake256.parallel.WIDTH", literal).splitlines())
            if decl not in shared and normalized not in "\n".join(line.rstrip() for line in program.splitlines()):
                raise ValueError(f"unmatched FORS declaration for width {width}: {decl}")
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    source = ["import Shakebatch.Sign", "import Shakebatch.ForsDispatch", "import Shakebatch.Available", "open Aeneas Aeneas.Std Result slhdsa", "open slhdsa.ShakeBatch",
              "variable [m : ShakeBatch.Machine] [s : ShakeBatch.Stream]",
              "variable (hardware : Result Bool) (available : Usize → Result Bool)"]
    seen = set()
    for decl in common["declarations"](template):
        match = re.fullmatch(r"(?:@\[.*?\]\s*)?axiom ([^\s]+)\s*(.*)", decl, re.DOTALL)
        if not match or match[1] not in models:
            raise ValueError(f"unknown FORS input at width {width}: {decl}")
        name, signature = match.groups()
        seen.add(name)
        signature = signature.replace(literal, "m.width")
        if stream:
            signature = signature.replace("shake256.Sponge", "s.State")
        # The expected type and the concrete model must retain the same implicit binders.
        binders, sep, result = signature.rpartition(":")
        if not sep or not result.strip():
            raise ValueError(f"unrecognized FORS binding signature: {signature}")
        args = re.findall(r"[{(]([^ :{}()]+)\s*:", binders)
        source.append(f"example {signature} := {models[name]} {' '.join(args)}")
    if seen != set(models):
        raise ValueError(f"missing FORS input at width {width}: {seen}")
    common["run"](["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(source), text=True)
    print(f"checked width {width} {filename} and bindings", flush=True)


if __name__ == "__main__":
    common["run"](["lake", "build", "Shakebatch.ForsDispatch", "Shakebatch.Available"], LEAN)
    facade["audit_theorems"]("Shakebatch.Header", ["slhdsa.ShakeBatch." + name for name in
        ("word_spec", "seed_rows", "put_spec", "address_rows", "high_bit", "header_spec")])
    facade["audit_theorems"]("Shakebatch.Read", ["slhdsa.ShakeBatch.read_spec"])
    facade["audit_theorems"]("Shakebatch.Pair", ["slhdsa.ShakeBatch.short_fips", "slhdsa.ShakeBatch.pair_fips",
        "Spec.Keccak.padded_fips"])
    facade["audit_theorems"]("Shakebatch.ForsNodes", ["slhdsa.ShakeBatch.fors_secrets", "slhdsa.ShakeBatch.fors_nodes"])
    facade["audit_theorems"]("Shakebatch.Sign", ["slhdsa.ShakeBatch.sign_fors_trees"])
    facade["audit_theorems"]("Shakebatch.Recover", ["slhdsa.ShakeBatch.recover_fors_trees"])
    facade["audit_theorems"]("Shakebatch.ForsDispatch", ["slhdsa.ShakeBatch.sign_dispatched", "slhdsa.ShakeBatch.recover_dispatched"])
    facade["audit_theorems"]("Shakebatch.Available", ["slhdsa.ShakeBatch.available_for_fips"])
    for target, width in WIDTHS.items():
        with tempfile.TemporaryDirectory() as folder:
            package = facade["extract"]("rust", target, "Header", Path(folder),
                ("crate::shake::batch::short", "crate::shake::batch::pair"),
                ("crate::shake256::parallel::permute",))
            check(package, width)
            nodes = facade["extract"]("rust", target, "Nodes", Path(folder),
                ("crate::shake::fors_batch::nodes",), ("crate::shake::batch::short", "crate::shake::batch::pair"))
            check_calls(nodes, width, "NodesProgram.lean", {
                "core.array.Array.map": "@_root_.core.array.Array.map",
                "shake.batch.short": "@ShakeBatch.shake.batch.short m",
                "shake.batch.pair": "@ShakeBatch.shake.batch.pair m"}, False)
            sign = facade["extract"]("rust", target, "Sign", Path(folder),
                ("crate::shake::fors_batch::sign",), ("crate::shake::fors_batch::nodes", "crate::shake::fors_batch::secrets"))
            check_calls(sign, width, "SignProgram.lean", {
                "core.array.Array.map": "@_root_.core.array.Array.map",
                "shake.fors_batch.secrets": "@ShakeBatch.shake.fors_batch.secrets m",
                "shake.fors_batch.nodes": "@ShakeBatch.shake.fors_batch.nodes m"}, True)
            recover = facade["extract"]("rust", target, "Recover", Path(folder),
                ("crate::shake::fors_batch::recover",),
                ("crate::shake::batch::short", "crate::shake::batch::pair", "crate::shake::hash", "crate::shake256"),
                ("crate::shake256::parallel::WIDTH",))
            check_calls(recover, width, "RecoverProgram.lean", {
                "core.array.Array.map": "@_root_.core.array.Array.map",
                "shake.batch.short": "@ShakeBatch.shake.batch.short m",
                "shake.batch.pair": "@ShakeBatch.shake.batch.pair m",
                "shake.hash.start": "@ShakeBatch.Stream.start s",
                "shake.hash.digest": "@ShakeBatch.Stream.digest s",
                "shake256.Sponge.absorb": "@ShakeBatch.Stream.absorb s"}, True, stream=True)
            dispatch = facade["extract"]("rust", target, "Dispatch", Path(folder),
                ("crate::shake::fors::fors_sign", "crate::shake::fors::fors_pk_from_sig"),
                ("crate::shake::batch", "crate::shake::fors_batch", "crate::shake::hash", "crate::shake::xmss", "crate::shake256"))
            check_calls(dispatch, width, "ForsDispatchProgram.lean", {
                "shake.xmss.climb": "@slhdsa.shake.xmss.climb",
                "shake.batch.available": "available",
                "shake.hash.thash": "@slhdsa.shake.hash.thash",
                "shake.hash.thash_pair": "@slhdsa.shake.hash.thash_pair",
                "shake.fors_batch.sign": "@ShakeBatch.shake.fors_batch.sign m",
                "shake256.Sponge.absorb": "slhdsa.shake256.Sponge.absorb",
                "shake.hash.digest": "slhdsa.shake.hash.digest",
                "shake.hash.start": "@slhdsa.shake.hash.start",
                "shake.fors_batch.recover": "@ShakeBatch.shake.fors_batch.recover m s"}, False,
                aliases={"← available N": "← shake.batch.available N"})
            available = facade["extract"]("rust", target, "Avail", Path(folder),
                ("crate::shake::batch::available",), ("crate::shake256::parallel::available",))
            check_calls(available, width, "Available.lean", {"shake256.parallel.available": "hardware"}, False,
                        aliases={"then hardware": "then shake256.parallel.available"})
