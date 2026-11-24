#!/usr/bin/env python3
"""Symbolically verify optimized RustCrypto FORS signing and public-key reconstruction.

The pinned crate's signing, recovery and recursive node methods run on each
actual RustCrypto receiver. Distinct observation points inside Shake, Sha2L1
and Sha2L35 record the selected PRF/F/H/T method, its receiver and arguments.
Inductive child calls return independent arbitrary bytes. The checker verifies
the digest indices, encoded addresses, each recursive level and every output
byte. The corresponding Lean provider composition is in PeerEquality.ForsProvider.
"""

from pathlib import Path
import argparse
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BASE = runpy.run_path(str(ROOT / "scripts/check-peer-fors.py"))
FOREST = runpy.run_path(str(ROOT / "scripts/peer-fors/forest_ir.py"))["Forest"]
TARGETS = (
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-gnu",
)


def setup(work, concrete=False):
    sets = [(family, set_) for family in ("sha2", "shake") for set_ in BASE["SETS"]]
    peer = BASE["setup"](work, sets, [])
    source = (ROOT / "scripts/peer-fors/calls.rs").read_text()
    source = source.replace(
        'include!("shape.rs");', (ROOT / "scripts/peer-fors/shape.rs").read_text()
    )
    if concrete:
        source = runpy.run_path(str(ROOT / "scripts/peer-fors/concrete.py"))[
            "instrument"
        ](peer, source)
    probes = []
    with (peer / "src/fors.rs").open("a") as module:
        for family, set_ in sets:
            suite = ("Sha2_" if family == "sha2" else "Shake") + set_
            n, a, k = BASE["SETS"][set_]
            rust = source.replace("SUITE_", suite + "_").replace("PEER_TYPE", suite)
            rust = (
                rust.replace("PARAM_N", str(n))
                .replace("PARAM_A", str(a))
                .replace("PARAM_K", str(k))
            )
            file = f"proof_calls_{family}_{set_}"
            (peer / "src" / (file + ".rs")).write_text(rust)
            module.write(f'\n#[path="{file}.rs"] mod {file};\n')
            probes.append((suite, n, a, k))
    return peer, probes


def check_target(ir, probes, concrete=False):
    machine = (
        runpy.run_path(str(ROOT / "scripts/peer-fors/concrete_ir.py"))["ConcreteForest"]
        if concrete
        else FOREST
    )
    for name, n, a, k in probes:
        arguments = (ir, n, a, k, name) if concrete else (ir, n, a, k)
        sign = machine(*arguments).sign(name + "_sign")
        recover = machine(*arguments).recover(name + "_recover")
        if concrete:
            for z in range(a + 1):
                machine(*arguments).node(name + "_node", z)
            print(
                f"{name}: checked all {a+1} recursive levels with the actual concrete provider",
                flush=True,
            )
        print(
            f"{name}: FORS signing and recovery checked ({sign+recover} instructions)",
            flush=True,
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--target", action="append", choices=TARGETS)
    parser.add_argument(
        "--representative",
        action="store_true",
        help="reproduce the previous shared-body check using a representative receiver",
    )
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="slh-peer-fors-alg-") as t:
        work = Path(t)
        peer, probes = setup(work, not args.representative)
        for target in args.target or TARGETS:
            subprocess.run(
                [
                    "cargo",
                    "rustc",
                    "--locked",
                    "--release",
                    "--lib",
                    "--target",
                    target,
                    "--target-dir",
                    str(work / "artifacts"),
                    "--",
                    "--emit=llvm-ir",
                ],
                cwd=peer,
                check=True,
            )
            (output,) = (work / "artifacts" / target / "release").rglob("slh_dsa*.ll")
            check_target(output.read_text(), probes, not args.representative)
            print(
                f"{target}: all twelve independent peer FORS callers checked",
                flush=True,
            )


if __name__ == "__main__":
    main()
