#!/usr/bin/env python3
"""Check each optimized RustCrypto signature codec against independent FIPS byte offsets.

The private accessors in the scratch archive only read typed fields. The first
probe parses a symbolic wire input and enumerates these fields in FIPS order.
This establishes every typed byte for every possible wire input. Each writer
must independently return that same string; every typed field assignment has
a corresponding wire input. Invalid-length checks use one symbolic length
constrained only to differ from the parameter set's fixed signature size.
"""

import argparse
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
DRIVER = runpy.run_path(str(ROOT / "scripts/check-peer-fors.py"))
ORIGINS = runpy.run_path(str(ROOT / "scripts/peer-fors/origins.py"))
TARGETS = (
    "aarch64-apple-darwin",
    "aarch64-unknown-linux-gnu",
    "x86_64-unknown-linux-gnu",
)
LAYERS = {
    "128s": (7, 9),
    "128f": (22, 3),
    "192s": (7, 9),
    "192f": (22, 3),
    "256s": (8, 8),
    "256f": (17, 4),
}


def instruments(crate):
    for module, accessor in {
        "hypertree.rs": "impl<P:HypertreeParams> HypertreeSig<P> { pub(crate) fn proof_row(&self,i:usize)->&XmssSig<P>{ &self.0[i] } }",
        "wots.rs": "impl<P:WotsParams> WotsSig<P> { pub(crate) fn proof_byte(&self,i:usize,b:usize)->u8 { self.0[i][b] } }",
    }.items():
        with (crate / "src" / module).open("a") as out:
            out.write("\n" + accessor + "\n")
    template = (ROOT / "scripts/peer-fors/codec_probe.rs").read_text()
    probes = []
    with (crate / "src/fors.rs").open("a") as out:
        for family in ("Sha2_", "Shake"):
            for param, (n, a, k) in DRIVER["SETS"].items():
                name, (d, h) = family + param, LAYERS[param]
                fors = n * k * (1 + a)
                sig = n + fors + n * d * (2 * n + 3 + h)
                expanded = template.replace("PEER_", name + "_")
                replacements = {
                    "PEER": "crate::" + name,
                    "SIZE": sig,
                    "FORS_SIZE": fors,
                    "D_VALUE": d,
                    "W_VALUE": 2 * n + 3,
                    "N_VALUE": n,
                }
                expanded = re.sub(
                    r"\b(?:PEER|SIZE|FORS_SIZE|D_VALUE|W_VALUE|N_VALUE)\b",
                    lambda m: str(replacements[m[0]]),
                    expanded,
                )
                out.write("\n" + expanded)
                probes.append((name, sig, fors))
    return probes


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--target", choices=TARGETS, action="append")
    args = p.parse_args()
    with tempfile.TemporaryDirectory(prefix="slh-peer-wire-") as temp:
        work = Path(temp)
        crate = DRIVER["setup"](work, [], [])
        probes = instruments(crate)
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
                cwd=crate,
                check=True,
            )
            (ir_path,) = (work / "artifacts" / target / "release").rglob("slh_dsa*.ll")
            ir = ir_path.read_text()
            for name, sig, fors in probes:
                for suffix in ("parse", "array", "vec", "forest", "forest_write"):
                    ORIGINS["check"](
                        ir,
                        name + "_" + suffix,
                        fors if suffix.startswith("forest") else sig,
                    )
                ORIGINS["check_invalid"](ir, name + "_invalid", sig)
                print(
                    f"{target}: verified {name} parser, both writers and FORS rows",
                    flush=True,
                )


if __name__ == "__main__":
    main()
