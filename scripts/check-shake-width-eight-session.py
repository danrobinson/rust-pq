#!/usr/bin/env python3
"""Check the production SHAKE width-eight dispatch and both hosted Lean sessions."""
from pathlib import Path
import re
import runpy
import sys
import tempfile

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
root = Path(__file__).resolve().parent.parent
profiles = ("128s", "128f", "192s", "192f", "256s", "256f")
rules = (
    ("shake/batch.rs", "fn available<const N: usize>() -> bool { matches!(N, 16 | 24 | 32) && parallel::available() }",
     "16 | 24 | 32", "16 | 24"),
    ("xmss.rs", "if p.hp >= 3 && super::batch::available::<N>() { return super::batch::xmss_sign_batch(p, m, sk_seed, idx, seed, adrs); }",
     "p.hp >= 3", "p.hp >= 4"),
    ("shake/fors.rs", "if super::batch::available::<N>() { return super::fors_batch::sign(p, &indices, sk_seed, seed, adrs); }",
     "sk_seed, seed, adrs", "seed, sk_seed, adrs"),
)


def check_call(source, rule):
    compact = lambda s: re.sub(r"\s+", "", s)
    if compact(source).count(compact(rule)) != 1:
        raise ValueError("missing or ambiguous production width-eight dispatch")


def check_fors_caller():
    helpers = runpy.run_path(str(Path(__file__).with_name("check-shake-fors-scatter.py")))
    module = (root / "lean-hw/ForsDriver/DispatchProgram.lean").read_text()
    expected = module.split("def dispatched", 1)[1].split("  := do", 1)[1].split("theorem off_eq", 1)[0]
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin", "x86_64-unknown-linux-gnu"):
            out = Path(tmp) / target
            out.mkdir()
            pkg = facade["extract"]("rust", target, "Dispatch", out, ["crate::shake::fors::fors_sign"],
                ["crate::shake::batch", "crate::shake::fors_batch", "crate::shake::hash",
                 "crate::shake::xmss", "crate::shake256", "crate::util"])
            (caller,) = [decl for decl in helpers["decls"](pkg / "Funs.lean", "slhdsa")
                         if decl.startswith("def shake.fors.fors_sign\n")]
            source = caller.split("  := do", 1)[1].replace("shake.fors_batch.sign p", "sign p").replace(
                "shake.batch.available", "available")
            if source.split() != expected.split():
                raise ValueError(f"{target} FORS digest decoder, feature decision, or signing branch changed")


def main():
    for path, rule, before, after in rules:
        source = (root / "rust/src" / path).read_text()
        check_call(source, rule)
        try:
            check_call(source.replace(before, after), rule)
        except ValueError:
            continue
        raise ValueError(f"{path}: changed production call passed the dispatch check")

    facade["run"]([sys.executable, Path(__file__).with_name("check-shake-fused-program.py")], root)

    check_fors_caller()
    for checker in ("check-shake-xmss-dispatch.py", "check-shake-buffered-program.py", "check-shake-buffered-leaves.py",
                    "check-shake-fors-driver.py", "check-fors-horizontal.py"):
        facade["run"]([sys.executable, Path(__file__).with_name(checker)], root)

    audit_public()


def audit_public():
    module = "Shakebatch.WidthEightCoverage"
    facade["run"](["lake", "build", module], root / "lean-hw")
    operations = ("sign_spec", "sign_deterministic_spec", "verify_spec", "slh_sign_spec",
                  "slh_verify_spec", "slh_sign_internal_spec", "slh_verify_internal_spec", "seeded_roundtrip",
                  "keygen_spec", "slh_keygen_internal_spec")
    theorems = [f"WidthEight{host}API.shake_{s}.{op}" for s in profiles
                for host in ("Apple", "X86") for op in operations]
    fors = ["slhdsa.ForsDriver." + name for name in
            ("sign_spec", "sign_small_spec", "upper", "on_spec", "off_eq")]
    fors += [host + ".slhdsa.ForsHorizontal.subtree_spec" for host in ("ForsTreeApple", "ForsTreeX86")]
    dispatch = ["slhdsa.WidthEight.apple_fast", "slhdsa.WidthEight.x86_select",
                "WidthEightOuterApple.slhdsa.WidthEight.outer_eq", "WidthEightOuterX86.slhdsa.WidthEight.outer_eq",
                "slhdsa.Fused.Outer.off_sign", "slhdsa.Fused.Outer.on_sign"]
    facade["audit_theorems"](module, theorems + fors + dispatch)
    print(f"Verified {len(theorems)} width-eight hosted theorem roots, both native XMSS selections, and both complete native FORS drivers.")


if __name__ == "__main__":
    main()
