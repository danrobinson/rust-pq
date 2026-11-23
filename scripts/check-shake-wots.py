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
        common["run"](["lake", "build", "Shakebatch.WotsKeys", "Shakebatch.WotsScatter"], LEAN)
        check = Path(d) / "Check.lean"
        theorems = ("wots_secrets", "wots_chains", "keygen_spec", "WotsOrder.order_spec")
        check.write_text("import Shakebatch.WotsKeys\nimport Shakebatch.WotsScatter\n" +
                         "".join(f"#print axioms slhdsa.ShakeBatch.{t}\n" for t in theorems))
        output = common["run"](["lake", "env", "lean", check], LEAN, text=True, capture_output=True).stdout
        for theorem in theorems:
            if f"'slhdsa.ShakeBatch.{theorem}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in output:
                raise ValueError(output)


if __name__ == "__main__":
    main()
