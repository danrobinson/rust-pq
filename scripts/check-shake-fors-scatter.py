#!/usr/bin/env python3
"""Re-extract the current SHAKE FORS secret address, secret store, and sibling store."""

from pathlib import Path
import os
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))
facade, decls, lean = shared["facade"], shared["decls"], shared["lean"]
dest = lean / "Cachepath/NativeVerify/ForsSignScatterProgram.lean"
cuts = [
    "crate::shake::fors_batch::" + x
    for x in (
        "nodes_fallback",
        "batch_pairs_slice",
        "batch_leaves_slice",
        "fors_subtree_horiz",
    )
] + ["crate::shake::batch", "crate::shake256"]


def program(package, width):
    prefix = "import Shakebatch.WriteRows\nimport Shakebatch.Selection\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace slhdsa.NativeVerify.ForsSign\nvariable [machine : ShakeBatch.Machine]\nvariable (short : {N : Std.Usize} → Array Std.U8 N → Array address.Adrs machine.width → ShakeBatch.Rows N → Std.Usize → Result (ShakeBatch.Rows N))\n"
    defs = []
    for file in ("Types.lean", "Funs.lean"):
        for item in decls(package / file, "slhdsa"):
            if any(
                x in item.partition(":=")[0]
                for x in (
                    "shake.fors_batch.sign.closure ",
                    "shake.fors_batch.sign.closure.",
                    "shake.fors_batch.sign_loop0.body",
                    "shake.fors_batch.sign_loop0\n",
                    "shake.fors_batch.sign_loop0_loop0",
                    "shake.fors_batch.sign_loop1_loop0_loop0",
                )
            ):
                defs.append(
                    item.replace("shake.fors_batch.sign", "sign")
                    .replace(f"{width}#usize", "machine.width")
                    .replace("shake256.parallel.WIDTH", "machine.width")
                    .replace("shake.batch.short_active", "short")
                    .replace(
                        "sign_loop0.body selections", "sign_loop0.body short selections"
                    )
                )
    if len(defs) != 11:
        raise ValueError(f"expected eleven scatter definitions, got {len(defs)}")
    return prefix + "\n\n".join(defs) + "\nend slhdsa.NativeVerify.ForsSign\n"


def fallback_program(package, width):
    header = """import Cachepath.NativeVerify.ForsSignSecrets
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]
abbrev Nodes := {N : Usize} → Array U8 N → Array U8 N → address.Adrs → Array U32 machine.width →
  U32 → Usize → Result (Rows N)
variable (short : Short) (nodes : Nodes)
"""
    forms = []
    for file in ("Types.lean", "Funs.lean"):
        for d in decls(package / file, "slhdsa"):
            head = d.partition(":=")[0]
            if "shake.fors_batch.sign.closure_" in head or any(
                "shake.fors_batch." + name in head
                for name in (
                    "sign_loop1_loop0.body",
                    "sign_loop1_loop0\n",
                    "sign_loop1.body",
                    "sign_loop1\n",
                )
            ):
                forms.append(
                    d.replace("shake.fors_batch.sign", "sign")
                    .replace(f"{width}#usize", "machine.width")
                    .replace("shake256.parallel.WIDTH", "machine.width")
                    .replace("shake.fors_batch.nodes_fallback", "nodes")
                    .replace(
                        "sign_loop1_loop0.body sk", "sign_loop1_loop0.body nodes sk"
                    )
                    .replace("sign_loop1_loop0 {", "sign_loop1_loop0 nodes {")
                    .replace(
                        "sign_loop1.body selections", "sign_loop1.body nodes selections"
                    )
                )
    if len(forms) != 14:
        raise ValueError(f"unexpected number of fallback declarations: {len(forms)}")
    (top,) = (
        d
        for d in decls(package / "Funs.lean", "slhdsa")
        if d.startswith("def shake.fors_batch.sign\n")
    )
    guard = "  else\n    if p.a > 0#u32"
    if top.count(guard) != 1:
        raise ValueError("unexpected eight-lane FORS entry")
    narrow = top.split(guard)[0] + "  else fail .panic"
    forms.append(
        narrow.replace(
            "shake.fors_batch.sign_loop0 selections", "sign_loop0 short selections"
        )
        .replace("shake.fors_batch.sign_loop1 iter", "sign_loop1 nodes iter")
        .replace("def shake.fors_batch.sign", "def narrow")
        .replace("shake256.parallel.WIDTH", "machine.width")
    )
    return header + "\n\n".join(forms) + "\nend slhdsa.NativeVerify.ForsSign\n"


def node_program(package, width):
    prefix = """import Cachepath.NativeVerify.ForsSignNarrow
open Aeneas Aeneas.Std Result ControlFlow Error
namespace slhdsa.NativeVerify.ForsSign
open ShakeBatch
variable [machine : Machine]
abbrev Leaf := {N : Usize} → Array U8 N → Array U8 N → address.Adrs → Array U32 machine.width → Usize → Result (Rows N)
abbrev Pair := {N : Usize} → Array U8 N → Array address.Adrs machine.width → Rows N → Rows N → Usize → Result (Rows N)
variable (leaf : Leaf) (pair : Pair)
"""
    forms = []
    for file in ("Types.lean", "Funs.lean"):
        for d in decls(package / file, "slhdsa"):
            if "shake.fors_batch.nodes_fallback" in d.partition(":=")[0]:
                forms.append(
                    d.replace("shake.fors_batch.nodes_fallback", "descend")
                    .replace(f"{width}#usize", "machine.width")
                    .replace("shake.fors_batch.fors_leaves_fused", "leaf")
                    .replace("shake.batch.pair_active", "pair")
                )
    if len(forms) != 16 or not forms[-1].endswith("partial_fixpoint"):
        raise ValueError("incomplete native FORS recursion")
    return prefix + "\n\n".join(forms) + "\nend slhdsa.NativeVerify.ForsSign\n"


def main():
    os.environ["PATH"] = (
        f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    )
    with tempfile.TemporaryDirectory() as temp:
        for target in facade["TARGETS"]:
            pkg = facade["extract"](
                "rust",
                target,
                "Scatter",
                Path(temp),
                ["crate::shake::fors_batch::sign"],
                cuts,
                ["crate::shake256::parallel::WIDTH"],
            )
            if (
                program(pkg, 3 if "aarch64-unknown" in target else 8)
                != dest.read_text()
            ):
                raise ValueError(f"FORS signer address or store differs on {target}")
            if (
                fallback_program(pkg, 3 if "aarch64-unknown" in target else 8)
                != (dest.parent / "ForsSignAuthProgram.lean").read_text()
            ):
                raise ValueError(f"FORS authentication loop differs on {target}")
            pkg = facade["extract"](
                "rust",
                target,
                "Nodes",
                Path(temp),
                ["crate::shake::fors_batch::nodes_fallback"],
                [
                    "crate::shake::fors_batch::fors_leaves_fused",
                    "crate::shake::batch",
                    "crate::shake256",
                ],
                ["crate::shake256::parallel::WIDTH"],
            )
            if (
                node_program(pkg, 3 if "aarch64-unknown" in target else 8)
                != (dest.parent / "ForsSignNodeProgram.lean").read_text()
            ):
                raise ValueError(f"recursive FORS node differs on {target}")
            caller = facade["extract"](
                "rust",
                target,
                "Dispatch",
                Path(temp),
                ["crate::shake::fors::fors_sign"],
                [
                    "crate::shake::batch",
                    "crate::shake::fors_batch",
                    "crate::shake::hash",
                    "crate::shake::xmss",
                    "crate::shake256",
                    "crate::util",
                ],
            )
            (top,) = (
                d
                for d in decls(caller / "Funs.lean", "slhdsa")
                if d.startswith("def shake.fors.fors_sign\n")
            )
            model = (dest.parent / "ForsSignLinux.lean").read_text()
            body = (
                top.split("  := do", 1)[1]
                .replace("shake.batch.available", "available")
                .replace("shake.fors_batch.sign p", "narrow short nodes p")
            )
            if (
                body.split()
                != model.split("  := do", 1)[1].split("end\n", 1)[0].split()
            ):
                raise ValueError(f"FORS public dispatcher differs on {target}")
            print(
                f"{target}: matched extracted FORS dispatcher, signing phases and node recursion",
                flush=True,
            )
    module = "Cachepath.NativeVerify.ForsSignNode"
    facade["run"](["lake", "build", module], lean)
    facade["audit_theorems"](
        module,
        [
            "slhdsa.NativeVerify.ForsSign." + x
            for x in (
                "addresses",
                "store_secrets",
                "store_siblings",
                "secret_phase",
                "auth_phase",
                "auth_batches",
                "narrow_spec",
                "linux",
                "descend_correct",
            )
        ],
    )


if __name__ == "__main__":
    main()
