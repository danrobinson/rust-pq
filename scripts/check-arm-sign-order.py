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


def check_wrapper(tmp, target):
    package = facade["extract"]("rust", target, "WSign", tmp, ["crate::wots::arm::sign"],
                                ["crate::wots::arm::wots_digits_stack", "crate::sha256::arm_wide::wots_sign_fused"])
    common = facade["common"]
    fresh = list(common["declarations"](common["body"](package / "Funs.lean")))
    nominal = list(common["declarations"](common["body"](package / "Types.lean")))
    if len(fresh) != 2 or len(nominal) != 2:
        raise ValueError(f"{target}: unexpected Arm WOTS sign wrapper declaration set")
    for declaration, path in [(fresh[1], "Armwide/NativeWotsProgram.lean"), (fresh[0], "Slhdsa/Funs.lean"),
                               *[(t, "Slhdsa/Types.lean") for t in nominal]]:
        if declaration not in (LEAN / path).read_text():
            raise ValueError(f"{target}: stale Arm WOTS sign wrapper or nominal type in {path}")

    dispatcher = facade["extract"]("rust", target, "WDispatch", tmp, ["crate::wots::wots_sign"],
                                    ["crate::sha256::arm_wide::available", "crate::wots::arm::sign",
                                     "crate::wots::wots_digits","crate::wots::sk_blocks","crate::hash::chain_blocks"])
    decls = list(common["declarations"](common["body"](dispatcher / "Funs.lean")))
    decls = [d for d in decls if "def wots.wots_sign" in d]
    if len(decls) != 5 or any(d not in (LEAN / "Armwide/DispatchProgram.lean").read_text() for d in decls):
        raise ValueError(f"{target}: public Arm WOTS dispatch or either fallback loop differs")


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
            check_wrapper(Path(tmp), target)
        path = LEAN / "Armwide/SignOrderProgram.lean"
        if refresh and target == facade["TARGETS"][0]:
            path.write_text(program)
        elif path.read_text() != program:
            raise ValueError(f"{target}: stale Arm signing sort extraction")
    facade["run"](["lake", "build", "Armwide.SignOrder", "Armwide.Dispatch"], LEAN)
    facade["audit_theorems"]("Armwide.SignOrder", [
        "slhdsa.Armwide.SignOrder.sort_spec", "slhdsa.Armwide.SignOrder.sign_bytes",
    ])
    facade["audit_theorems"]("Armwide.NativeWots", ["slhdsa.Armwide.Public.sign_spec", "slhdsa.Armwide.Public.sign_eq_scalar"])
    facade["audit_theorems"]("Armwide.Dispatch", ["slhdsa.Armwide.Public.Dispatcher.cached_hit_wots"])
    print("Apple and Linux AArch64 signing sort and FIPS WOTS bytes checked", flush=True)


if __name__ == "__main__":
    main()
