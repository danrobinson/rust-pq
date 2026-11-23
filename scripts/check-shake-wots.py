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


def check_chains(package, width):
    literal = f"{width}#usize"
    source = (LEAN / "Shakebatch/WotsChainProgram.lean").read_text()
    specialized = source.replace("machine.width", literal).replace("machine.permute", "shake256.parallel.permute")
    seen = set()
    for filename in ("Types.lean", "Funs.lean"):
        for name, decl in body_names(common["body"](package / filename)):
            if re.match(r"shake\.batch\.(secrets|chains)(?:\.|_|$)", name):
                exact = decl.replace("shake256.parallel.WIDTH", literal)
                # Reducibility on the type synonym is immaterial to kernel definitional equality.
                if exact.removeprefix("@[reducible]\n") not in specialized:
                    raise ValueError(f"unbound width-{width} WOTS body {name}")
                seen.add(name)
    expected = set(re.findall(r"\bdef\s+(shake\.batch\.(?:secrets|chains)[^\s]*)", source))
    if expected != seen:
        raise ValueError(f"width-{width} declaration mismatch {expected.symmetric_difference(seen)}")
    print(f"verified {len(seen)} WOTS chain definitions at width {width}", flush=True)


def main():
    with tempfile.TemporaryDirectory(prefix="shake-wots-") as d:
        for target, width in WIDTHS.items():
            scratch = Path(d) / target
            scratch.mkdir()
            roots = ("crate::shake::batch::secrets", "crate::shake::batch::chains")
            cuts = tuple("crate::shake::batch::" + op for op in ("short", "header", "put"))
            package = extract("rust", target, "Chains", scratch, roots, (*cuts, "crate::shake256::parallel::permute"))
            check_chains(package, width)


if __name__ == "__main__":
    main()
