#!/usr/bin/env python3
"""Check the production batched WOTS source against its width-polymorphic Lean program."""
from pathlib import Path
import re
import runpy
import tempfile

base = runpy.run_path(str(Path(__file__).with_name("check-shake-batch.py")))
LEAN, common, extract, WIDTHS = base["LEAN"], base["common"], base["facade"]["extract"], base["WIDTHS"]


def body_names(text):
    for declaration in common["declarations"](text):
        match = re.search(r"\b(?:def|abbrev|axiom|structure)\s+(\S+)", declaration)
        if match:
            yield match[1], declaration


def check_program(package, width, module, roots):
    literal = f"{width}#usize"
    source = (LEAN / f"Shakebatch/{module}.lean").read_text()
    specialized = source.replace("machine.width", literal).replace("machine.permute", "shake256.parallel.permute")
    specialized = (specialized.replace("stream.absorb", "shake256.Sponge.absorb").replace("stream.State", "shake256.Sponge")
                   .replace("stream.start", "shake.hash.start").replace("stream.digest", "shake.hash.digest"))
    names = "|".join(roots)
    seen = set()
    for filename in ("Types.lean", "Funs.lean"):
        for name, decl in body_names(common["body"](package / filename)):
            if re.match(rf"shake\.batch\.(?:{names})(?:\.|_|$)", name):
                exact = decl.replace("shake256.parallel.WIDTH", literal)
                # Reducibility on the type synonym is immaterial to kernel definitional equality.
                if exact.removeprefix("@[reducible]\n") not in specialized:
                    raise ValueError(f"unbound width-{width} WOTS body {name}")
                seen.add(name)
    expected = set(re.findall(rf"\bdef\s+(shake\.batch\.(?:{names})[^\s]*)", source))
    if expected != seen:
        raise ValueError(f"width-{width} declaration mismatch {expected.symmetric_difference(seen)}")
    print(f"verified {len(seen)} {module} definitions at width {width}", flush=True)


def check_dispatch(package):
    names = ("wots_pk_gen", "wots_sign", "wots_pk_from_sig")
    source = (LEAN / "Shakebatch/WotsDispatchProgram.lean").read_text()
    source = source.replace("(available : Std.Usize → Result Bool) ", "").replace("← available N", "← shake.batch.available N")
    baseline = dict(body_names(common["body"](LEAN.parent / "lean/Slhdsa/Funs.lean")))
    seen = set()
    for name, decl in body_names(common["body"](package / "Funs.lean")):
        if name in ("shake.wots." + item for item in names):
            if "\n".join(line.rstrip() for line in decl.split("\n")) not in source:
                raise ValueError(f"unbound WOTS feature dispatch {name}")
            seen.add(name)
        elif name.startswith("shake.wots.") and any(name.startswith("shake.wots."+item+"_loop") for item in names):
            if baseline.get(name) != decl:
                raise ValueError(f"unbound scalar WOTS loop {name}")
            seen.add(name)
    expected = {"shake.wots."+base+suffix for base in names for suffix in ("","_loop","_loop.body")}
    if seen != expected:
        raise ValueError(f"incomplete scalar and dispatch coverage {seen ^ expected}")
    print(f"verified all {len(seen)} WOTS dispatch and scalar loop definitions", flush=True)


def main():
    with tempfile.TemporaryDirectory(prefix="shake-wots-") as d:
        for target, width in WIDTHS.items():
            scratch = Path(d) / target
            scratch.mkdir()
            roots = ("crate::shake::batch::secrets", "crate::shake::batch::chains")
            cuts = tuple("crate::shake::batch::" + op for op in ("short", "header", "put"))
            package = extract("rust", target, "Chains", scratch, roots, (*cuts, "crate::shake256::parallel::permute"))
            check_program(package, width, "WotsChainProgram", ("secrets", "chains"))
            roots = ("crate::shake::batch::keygen",)
            cuts = ("crate::shake::batch::secrets", "crate::shake::batch::chains",
                    "crate::shake::hash::start", "crate::shake::hash::digest", "crate::shake256::Sponge::absorb")
            keys = extract("rust", target, "Wotskeys", scratch, roots, cuts)
            check_program(keys, width, "WotsKeyProgram", ("keygen",))
            order = extract("rust", target, "Wotsorder", scratch, ("crate::shake::batch::chain_order",), ())
            check_program(order, width, "WotsOrderProgram", ("chain_order",))
            callers = extract("rust", target, "Wotssign", scratch, ("crate::shake::batch::sign", "crate::shake::batch::recover"),
                              (*cuts, "crate::shake::batch::chain_order", "crate::util::block"))
            check_program(callers, width, "WotsSignProgram", ("sign", "recover"))
            entrypoints = ("wots_pk_gen", "wots_sign", "wots_pk_from_sig")
            entrycuts = ("crate::shake::batch::available", "crate::shake::batch::keygen", "crate::shake::batch::sign",
                         "crate::shake::batch::recover", "crate::wots::wots_digits", "crate::shake::wots::secret",
                         "crate::shake::wots::chain", "crate::shake::hash::start", "crate::shake::hash::digest",
                         "crate::util::block", "crate::shake256::Sponge::absorb")
            dispatch = extract("rust", target, "Wotsdispatch", scratch, tuple("crate::shake::wots::"+f for f in entrypoints), entrycuts)
            check_dispatch(dispatch)
        common["run"](["lake", "build", "Shakebatch.WotsKeys", "Shakebatch.WotsScatter", "Shakebatch.WotsDispatch"], LEAN)
        check = Path(d) / "Check.lean"
        theorems = ("wots_secrets", "wots_chains", "keygen_spec", "WotsOrder.order_spec", "sign_batches", "recover_batches",
                    "sign_spec", "recover_spec", "wots_pk_gen_spec", "wots_sign_spec", "wots_pk_from_sig_spec")
        check.write_text("import Shakebatch.WotsKeys\nimport Shakebatch.WotsScatter\nimport Shakebatch.WotsDispatch\n" +
                         "".join(f"#print axioms slhdsa.ShakeBatch.{t}\n" for t in theorems))
        output = common["run"](["lake", "env", "lean", check], LEAN, text=True, capture_output=True).stdout
        for theorem in theorems:
            if f"'slhdsa.ShakeBatch.{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in output:
                raise ValueError(output)


if __name__ == "__main__":
    main()
