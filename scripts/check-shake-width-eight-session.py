#!/usr/bin/env python3
"""Check the production SHAKE width-eight dispatch and both hosted Lean sessions."""
from pathlib import Path
import re
import runpy
import sys

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

    module = "Shakebatch.WidthEightCoverage"
    facade["run"](["lake", "build", module], root / "lean-hw")
    operations = ("sign_spec", "sign_deterministic_spec", "verify_spec", "slh_sign_spec",
                  "slh_verify_spec", "slh_sign_internal_spec", "slh_verify_internal_spec", "seeded_roundtrip")
    theorems = [f"WidthEight{host}API.shake_{s}.{op}" for s in profiles
                for host in ("Apple", "X86") for op in operations]
    lanes = ["slhdsa.WidthEight.Fors." + name for name in
             ("secret_fips", "leaf_fips", "parent_fips", "secret_lane", "fused_lane", "packed_lane", "signature_eq")]
    facade["audit_theorems"](module, theorems + lanes + ["slhdsa.WidthEight.apple_fast", "slhdsa.WidthEight.x86_select"])
    print(f"Verified {len(theorems)} width-eight hosted theorem roots, both native XMSS selections, seven native FORS theorems, and three dispatch mutations.")


if __name__ == "__main__":
    main()
