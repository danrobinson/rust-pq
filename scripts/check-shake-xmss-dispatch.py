#!/usr/bin/env python3
"""Replay both width-eight XMSS/WOTS dispatchers, their scalar loops and feature decisions."""
from pathlib import Path
import re
import runpy
import tempfile

here = Path(__file__).resolve().parent
reference = runpy.run_path(str(here / "check-shake-width-three-xmss.py"))
facade = reference["facade"]
arm = facade["common"]
lean = arm["LEAN"]
roots = ["crate::" + n for n in reference["ROOTS"]]
cuts = ["crate::" + n for n in reference["CUTS"] +
        ("shake::batch::xmss_subtree", "shake::batch::xmss_sign_batch")]


def check(package):
    outer = (lean / "Fused/OuterProgram.lean").read_text()
    scalar = set(arm["declarations"](arm["body"](lean / "Slhdsa/Funs.lean")))
    expected = set(re.findall(r"^def (shake\.[^\s]+)", outer, re.M))
    found = set()
    for decl in arm["declarations"](arm["body"](package / "Funs.lean")):
        name = re.search(r"\bdef\s+(\S+)", decl)
        if not name:
            continue
        if name[1] in expected:
            if decl not in outer:
                raise ValueError(f"unmatched extracted XMSS dispatch declaration {name[1]}")
            found.add(name[1])
        elif name[1].startswith(("shake.wots.wots_pk_gen_loop", "shake.wots.wots_sign_loop")):
            if decl not in scalar:
                raise ValueError(f"unmatched scalar WOTS dependency {name[1]}")
    if expected != found or len(found) != 8:
        raise ValueError(f"missing XMSS dispatcher or loop: {expected - found}")


def main():
    root = lean.parent
    with tempfile.TemporaryDirectory() as temp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            folder = Path(temp) / target
            folder.mkdir()
            pkg = facade["extract"](root / "rust", target, "Dispatch", folder, roots, cuts)
            check(pkg)
            path = pkg / "Funs.lean"
            src = path.read_text()
            for before, after in [
                ("then shake.batch.xmss_sign_batch p m sk_seed idx seed adrs",
                 "then shake.batch.xmss_sign_batch p sk_seed m idx seed adrs"),
                ("let sig ← shake.wots.wots_sign m sk_seed seed a1",
                 "let sig ← shake.wots.wots_sign m seed sk_seed a1"),
                ("let a1 ← address.Adrs.with_word2 a z", "let a1 ← address.Adrs.with_word2 a i"),
            ]:
                if before not in src:
                    raise ValueError(f"mutation no longer targets the extracted body on {target}")
                path.write_text(src.replace(before, after))
                try:
                    check(pkg)
                except ValueError:
                    continue
                raise ValueError(f"accepted altered signing path on {target}")
    print("Matched eight complete XMSS/WOTS dispatcher declarations on each host and rejected all six mutations.")


if __name__ == "__main__":
    main()
