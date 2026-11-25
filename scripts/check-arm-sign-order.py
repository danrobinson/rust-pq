#!/usr/bin/env python3
"""Extract the live all-digit WOTS signing bucket sort on both Arm platforms."""
import argparse
import os
from pathlib import Path
import runpy
import tempfile

HERE = Path(__file__).resolve().parent
cache = runpy.run_path(str(HERE / "check-cache-endtoend.py"))
facade = cache["facade"]
LEAN = cache["LEAN"]


def extract(tmp, target):
    crate = cache["copy_rust_crate"](tmp)
    path = crate / "src/sha256/arm_wide.rs"
    source = path.read_text()
    before_hashes = source.split("fn wots_sign_fused_active", 1)[1].split("    let (sk_x, sk_xb)", 1)[0]
    body = before_hashes.split("{", 1)[1]
    first, separator, body = body.partition("    let len = digits.len();")
    if first.strip() or not separator:
        raise ValueError("the signing sort no longer begins at the input digits")
    # Cut immediately after the third sort loop; all three Rust loop bodies
    # and their integer types are preserved in the Aeneas translation.
    path.write_text(source + "\nfn sign_order(digits: &[u32]) -> [u8; LEN_MAX] {" + body + "order\n}\n")
    package = facade["extract"](crate, target, "ArmSignOrder", tmp,
                                ["crate::sha256::arm_wide::sign_order"], [])
    if (package / "FunsExternal_Template.lean").exists():
        raise ValueError("unexpected external in the Arm signing sort")
    common = facade["common"]
    decls = common["declarations"](common["body"](package / "Funs.lean"))
    header = "import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnamespace slhdsa.Armwide.SignOrder"
    return "\n\n".join([header, *decls, "end slhdsa.Armwide.SignOrder\n"])


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--refresh", action="store_true")
    args = parser.parse_args()
    check(args.refresh)


def check(refresh=False):
    os.environ["PATH"] = os.pathsep.join([
        str(Path.home() / ".elan/bin"), str(Path.home() / ".cargo/bin"), os.environ["PATH"],
    ])
    for target in facade["TARGETS"][:2]:
        with tempfile.TemporaryDirectory() as tmp:
            program = extract(Path(tmp), target)
        path = LEAN / "Armwide/SignOrderProgram.lean"
        if refresh and target == facade["TARGETS"][0]:
            path.write_text(program)
        elif path.read_text() != program:
            raise ValueError(f"{target}: stale Arm signing sort extraction")
    facade["run"](["lake", "build", "Armwide.SignOrder"], LEAN)
    facade["audit_theorems"]("Armwide.SignOrder", [
        "slhdsa.Armwide.SignOrder.sort_spec", "slhdsa.Armwide.SignOrder.sign_bytes",
    ])
    print("Apple and Linux AArch64 signing sort and FIPS WOTS bytes checked", flush=True)


if __name__ == "__main__":
    main()
