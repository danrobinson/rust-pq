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
import json
import shutil
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


def cross_library(work, probes):
    """Build a single LTO module so both actual crate implementations are available."""
    crate = work / "cross"
    (crate / "src").mkdir(parents=True)
    source = (ROOT / "scripts/peer-fors/codec_cross.rs").read_text()
    (crate / "src/lib.rs").write_text(
        "\n".join(
            source.replace("PEER", name).replace("SIZE", str(size))
            for name, size, _ in probes
        )
    )
    (crate / "Cargo.toml").write_text(f"""[package]
name = "slh-wire-cross"
version = "0.1.0"
edition = "2024"
[workspace]
[lib]
crate-type = ["staticlib"]
[dependencies]
peer = {{package = "slh-dsa", path = "../peer"}}
ours = {{package = "slhdsa-compat", path = {json.dumps(str(ROOT / "compat"))}, features = ["platform-sha2"]}}
[profile.release]
codegen-units = 1
panic = "abort"
lto = true
""")
    shutil.copyfile(ROOT / "bench/Cargo.lock", crate / "Cargo.lock")
    metadata = lambda path, locked: json.loads(
        subprocess.check_output(
            [
                "cargo",
                "metadata",
                *(["--locked"] if locked else []),
                "--format-version",
                "1",
                "--manifest-path",
                str(path),
            ]
        )
    )
    baseline = metadata(work / "peer/Cargo.toml", True)
    actual = metadata(crate / "Cargo.toml", False)

    def peer_graph(graph):
        packages = {x["id"]: x for x in graph["packages"]}
        nodes = {n["id"]: n for n in graph["resolve"]["nodes"]}
        pending = [next(k for k, p in packages.items() if p["name"] == "slh-dsa")]
        visited = set()
        while pending:
            k = pending.pop()
            if k in visited:
                continue
            visited.add(k)
            pending += [
                dep["pkg"]
                for dep in nodes[k]["deps"]
                if any(edge["kind"] != "dev" for edge in dep["dep_kinds"])
            ]
        return {
            (packages[k]["name"], packages[k]["version"], packages[k]["source"])
            for k in visited
        }

    if peer_graph(actual) != peer_graph(baseline):
        raise ValueError("cross-build peer dependency graph differs from benchmark")
    return crate


def cross_check(crate, artifacts, target, probes):
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
            str(artifacts),
            "--",
            "--emit=llvm-ir",
        ],
        cwd=crate,
        check=True,
    )
    (ir_path,) = (artifacts / target / "release").rglob("slh_wire_cross*.ll")
    ir = ir_path.read_text()
    for name, size, _ in probes:
        for suffix in ("peer_to_ours", "ours_to_peer"):
            ORIGINS["check"](ir, name + "_" + suffix, size)
        ORIGINS["check_invalid"](ir, name + "_both_invalid", size)
    print(
        f"{target}: both compiled libraries interoperate byte-for-byte in both directions on all twelve sets",
        flush=True,
    )


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--target", choices=TARGETS, action="append")
    args = p.parse_args()
    with tempfile.TemporaryDirectory(prefix="slh-peer-wire-") as temp:
        work = Path(temp)
        crate = DRIVER["setup"](work, [], [])
        probes = instruments(crate)
        cross = cross_library(work, probes)
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

            cross_check(cross, work / "cross-artifacts", target, probes)


if __name__ == "__main__":
    main()
