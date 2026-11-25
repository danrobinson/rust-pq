#!/usr/bin/env python3
"""Link Linux Arm's width-three XMSS node and signer to the two live WOTS contracts."""
from pathlib import Path
import re
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
cache = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
facade = cache["facade"]
arm = facade["common"]
TARGET = "aarch64-unknown-linux-gnu"
ROOTS = ("shake::xmss::xmss_node", "shake::xmss::xmss_sign", "shake::wots::wots_sign",
         "shake::wots::wots_pk_gen")
CUTS = ("wots::wots_digits", "shake::batch::available", "shake::batch::sign", "shake::batch::keygen",
        "shake::hash::thash_pair", "shake::hash::start", "shake::hash::digest",
        "shake::wots::secret", "shake::wots::chain", "shake256::Sponge::absorb")


def select_live_width(source, name):
    # Aeneas cannot translate a nested mutable loan in the width-eight branch.
    # Rust type-checks the width assertion and the projected value-returning
    # branch. Reaching its end without returning is a Rust compilation error.
    start = source.index("fn " + name + "<")
    body = source.index("{", start)
    end = source.index("\n}", body)
    prefix, guard, rest = source[body + 1:end].partition("    if WIDTH != 8 {")
    expected_prefix = "" if name == "xmss_subtree" else "let digits = wots_digits(m);"
    if not guard or prefix.strip() != expected_prefix:
        raise ValueError(f"changed precondition or shadowed compile-time width in {name}")
    selected, close, dead = rest.partition("\n    }")
    if not close or not dead.strip() or not re.search(r"\breturn\s+[^;]+;\s*$", selected):
        raise ValueError(f"invalid early return in {name}")
    return source[:body + 1] + prefix + selected + source[end:]


def main():
    lean = arm["LEAN"]
    facade["run"](["lake", "build", "Shakebatch.WidthThreeLinux"], lean)
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        crate = cache["copy_rust_crate"](scratch)
        path = crate / "src/shake/batch.rs"
        text = path.read_text()
        for name in ("xmss_subtree", "xmss_sign_batch"):
            text = select_live_width(text, name)
        path.write_text(text + "\nconst _: [(); 3] = [(); WIDTH];\n")
        pkg = facade["extract"](crate, TARGET, "WidthThree", scratch,
            ["crate::" + x for x in ROOTS], ["crate::" + x for x in CUTS])
        fresh = list(arm["declarations"](arm["body"](pkg / "Funs.lean")))
        shared = set(arm["declarations"](arm["body"](lean / "Slhdsa/Funs.lean")))
        model = (lean / "Shakebatch/WidthThreeProgram.lean").read_text()
        expected = set(re.findall(r"^def (shake\.[^\s]+)", model, re.M))
        found = set()
        for declaration in fresh:
            match = re.search(r"\bdef\s+(\S+)", declaration)
            if match and declaration in model:
                found.add(match[1])
            elif (match and match[1].startswith(("shake.xmss.", "shake.batch.xmss_", "shake.wots.wots_pk_gen_loop",
                                                  "shake.wots.wots_sign_loop")) and declaration not in shared):
                raise ValueError(f"unmatched dependency: {declaration[:220]}")
        if found != expected:
            raise ValueError(f"missing XMSS declaration: {expected - found}")
        facade["audit_theorems"]("Shakebatch.WidthThree", [
            "slhdsa.WidthThree.subtree_spec", "slhdsa.WidthThree.node_spec",
            "slhdsa.WidthThree.xmss_sign_spec"])
        facade["audit_theorems"]("Shakebatch.WidthThreeLinux", [
            "WidthThreeTree.slhdsa.Shake.ht_sign_spec", "slhdsa.WidthThree.fallback_spec",
            "WidthThreeLinux.slhdsa.WidthThree.parallel_sign_spec", "WidthThreeLinux.slhdsa.WidthThree.parallel_context_spec"])
        print(f"{TARGET}: {len(found)} XMSS/WOTS dispatcher definitions match the width-three program")


if __name__ == "__main__":
    main()
