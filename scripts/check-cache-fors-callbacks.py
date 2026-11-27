#!/usr/bin/env python3
"""Bind the cache SIMD FORS sign, recovery and recursive node bodies to their Lean proofs."""
from pathlib import Path
import re
import runpy
import tempfile

batch = runpy.run_path(str(Path(__file__).with_name("check-shake-batch.py")))
facade, common = batch["facade"], batch["common"]
lean = facade["ROOT"] / "lean-hw"
widths = {"aarch64-apple-darwin": 8, "aarch64-unknown-linux-gnu": 3, "x86_64-unknown-linux-gnu": 8}
simd = "crate::cache::shake_ops::simd::"
models = {
    "fors_secrets": "shake.fors_batch.secrets",
    "fors_nodes": "shake.fors_batch.nodes",
    "fors_sign": "shake.fors_batch.sign",
    "fors_pk_from_sig": "shake.fors_batch.recover",
    **{name: "shake.batch." + name for name in ("word", "header", "put", "read")},
    "short": "shake.batch.short",
    "pair": "shake.batch.pair",
}


def normalize(text):
    for source, model in models.items():
        text = text.replace("cache.shake_ops.simd." + source, model)
    return " ".join(text.split())


def check(target, width, scratch, crate="rust"):
    roots = [simd + name for name in ("fors_nodes", "fors_sign", "fors_pk_from_sig")]
    roots += ["crate::cache::shake_ops::start", "crate::cache::shake_ops::digest"]
    cuts = ["crate::shake256"]
    package = facade["extract"](crate, target, "ForsCallbacks", scratch, roots, cuts,
                                ("crate::shake256::parallel::WIDTH",))
    shared = lean.parent / "lean/Slhdsa"
    model = " ".join(normalize((lean / "Shakebatch" / (kind + "Program.lean")).read_text())
                     for kind in ("Nodes", "Sign", "Recover"))
    literal = f"{width}#usize"
    model += " " + normalize((lean / "Shakebatch/Program.lean").read_text())
    model = model.replace("machine.permute", "shake256.parallel.permute")
    model = model.replace("machine.width", literal).replace("stream.State", "shake256.Sponge")
    for name, replacement in (("start", "cache.shake_ops.start"), ("digest", "cache.shake_ops.digest"),
                              ("absorb", "shake256.Sponge.absorb")):
        model = model.replace("stream." + name, replacement)
    abstract = (package / "TypesExternal_Template.lean").read_text().split("open slhdsa", 1)[-1]
    if list(common["declarations"](abstract[abstract.index("/--"):])) != ["axiom shake256.Sponge : Type"]:
        raise ValueError(f"changed abstract FORS sponge type on {target}")
    witnessed = set()
    for file in ("Types", "Funs"):
        std = set(common["declarations"](common["body"](shared / (file + ".lean"))))
        normalized_std = {normalize(d) for d in std}
        functions = list(common["declarations"](common["body"](package / (file + ".lean"))))
        for decl in functions:
            definition = re.search(r"\bdef\s+([\w.]+)", decl)
            if definition:
                witnessed.add(definition[1])
            if decl in std or normalize(decl) == f"@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := {literal}":
                continue
            norm = normalize(decl).replace("shake256.parallel.WIDTH", literal)
            shared_hash = norm.replace("cache.shake_ops.start", "shake.hash.start").replace("cache.shake_ops.digest", "shake.hash.digest")
            if shared_hash not in normalized_std and norm not in model:
                raise ValueError(f"unmatched FORS declaration on {target}: {norm}")
    required = {"cache.shake_ops.simd." + name for name in models}
    required |= {"cache.shake_ops.start", "cache.shake_ops.digest", "shake256.parallel.WIDTH"}
    if required - witnessed:
        raise ValueError(f"missing FORS declarations on {target}: {required - witnessed}")
    template = (package / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    expected = {
        "core.array.Array.map": "@_root_.core.array.Array.map",
        "shake256.parallel.permute": "m.permute",
        "shake256.Sponge.absorb": "shake256.Sponge.absorb", "shake256.Sponge.finish": "shake256.Sponge.finish",
        "shake256.Sponge.new": "shake256.Sponge.new",
    }
    proof = ["import Cachepath.ForsCallbacks", "open Aeneas Aeneas.Std Result slhdsa",
             "variable [m : ShakeBatch.Machine] [s : ShakeBatch.Stream]"]
    for decl in common["declarations"](template):
        name, signature = re.fullmatch(r"(?:@\[.*?\]\s*)?axiom (\S+)\s*(.*)", decl, re.S).groups()
        rhs = expected.pop(name)
        signature = signature.replace(literal,"m.width")
        args = re.findall(r"[{(]([^ :{}()]+)\s*:", signature.rpartition(":")[0])
        proof.append(f"example {signature} := {rhs} {' '.join(args)}")
    if expected:
        raise ValueError(f"missing FORS externals: {expected}")
    facade["run"](["lake", "env", "lean", "--stdin"], lean, input="\n".join(proof), text=True)


def reject_wrong_sibling(scratch):
    endtoend = runpy.run_path(str(Path(__file__).with_name("check-cache-endtoend.py")))
    crate = endtoend["copy_rust_crate"](scratch)
    path = crate / "src/cache.rs"
    text = path.read_text()
    old = "let siblings = fors_nodes(sk, seed, addr, indices.map(|i| (i >> j) ^ 1), j);"
    if text.count(old) != 1:
        raise ValueError("expected one SIMD FORS signing sibling calculation")
    path.write_text(text.replace(old, old.replace("^ 1", "^ 0")))
    try:
        check("aarch64-apple-darwin",8,scratch,crate)
    except ValueError as exc:
        if "unmatched FORS declaration" not in str(exc) or "shake.fors_batch.sign" not in str(exc):
            raise
    else:
        raise ValueError("wrong authentication sibling survived the source replay")
    print("Rejected a regenerated SIMD FORS signer that copies the selected node as its sibling.", flush=True)


def main():
    facade["run"](["lake", "build", "Cachepath.ForsCallbacks", "Cachepath.ShakeClosed"], lean)
    with tempfile.TemporaryDirectory() as temp:
        for target,width in widths.items():
            scratch = Path(temp) / target
            scratch.mkdir()
            check(target,width,scratch)
            print(f"{target}: matched SIMD FORS signing and recovery at width {width}", flush=True)
        reject_wrong_sibling(Path(temp))
    facade["audit_theorems"]("Cachepath.ForsCallbacks", ["CacheopsRust.ForsCallbacks.sign_eq", "CacheopsRust.ForsCallbacks.recover_eq"])


if __name__ == "__main__":
    main()
