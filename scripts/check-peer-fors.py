#!/usr/bin/env python3
"""Check the independent pinned RustCrypto FORS implementations against their algorithm-level contracts."""

import argparse
import json
import re
import runpy
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts/peer-fors"
SETS = {
    "128s": (16, 12, 14),
    "128f": (16, 6, 33),
    "192s": (24, 14, 17),
    "192f": (24, 8, 33),
    "256s": (32, 14, 22),
    "256f": (32, 9, 35),
}


def setup(tmp, shapes, operations):
    packages = json.loads(
        subprocess.check_output(
            [
                "cargo",
                "metadata",
                "--locked",
                "--format-version",
                "1",
                "--manifest-path",
                ROOT / "bench/Cargo.toml",
            ]
        )
    )["packages"]
    (peer,) = [p for p in packages if p["name"] == "slh-dsa"]
    if peer["version"] != "0.2.0-rc.5" or not peer["source"].startswith("registry+"):
        raise ValueError("unexpected peer package")
    crate = tmp / "peer"
    digest_gate = runpy.run_path(str(ROOT / "scripts/check-peer-digest.py"))
    checksums = digest_gate["registry_checksums"](ROOT / "bench/Cargo.lock")
    digest_gate["unpack_peer"](peer, crate, checksums[peer["name"], peer["version"], peer["source"]])
    # Use the comparator's dependency versions, even when the published peer ships
    # a different lockfile for its own test suite.
    manifest = crate / "Cargo.toml"
    text = re.sub(
        r"^\[dev-dependencies(?:\.[^\]]+)?\]\n.*?(?=^\[|\Z)",
        "",
        manifest.read_text(),
        flags=re.MULTILINE | re.DOTALL,
    )
    manifest.write_text(text)
    shutil.copy2(ROOT / "bench/Cargo.lock", crate / "Cargo.lock")
    selected = json.loads(
        subprocess.check_output(
            [
                "cargo",
                "metadata",
                "--format-version",
                "1",
                "--manifest-path",
                crate / "Cargo.toml",
            ]
        )
    )
    pool = {p["id"]: p for p in selected["packages"]}
    nodes = {d["id"]: d for d in selected["resolve"]["nodes"]}
    pinned = {(p["name"], p["version"], p["source"]) for p in packages}
    pending = [selected["resolve"]["root"]]
    checked = set()
    while pending:
        item = pending.pop()
        if item in checked:
            continue
        checked.add(item)
        p = pool[item]
        if p["source"] and (p["name"], p["version"], p["source"]) not in pinned:
            raise ValueError(f"dependency differs from the benchmark: {item}")
        pending.extend(
            dep["pkg"]
            for dep in nodes[item]["deps"]
            if any(k["kind"] != "dev" for k in dep["dep_kinds"])
        )
    declarations = []
    if "node" in operations:
        path = crate / "src/fors.rs"
        original = path.read_text()
        method = original[
            original.index("    fn fors_node(") : original.index("    fn fors_sign(")
        ]
        if method.count("fn fors_node(") != 1 or method.count("self.fors_node(") != 2:
            raise ValueError("unexpected peer recursive node definition")
        clone = method.replace("fn fors_node(", "fn proof_one_node(", 1)
        insert = original.index("    fn fors_sign(")
        path.write_text(
            original[:insert] + "    #[cfg(kani)]\n" + clone + original[insert:]
        )
    implementations = "".join(
        (crate / "src/hashes" / file).read_text() for file in ("sha2.rs", "shake.rs")
    )
    for family, shape in shapes:
        n, a, k = SETS[shape]
        typ = ("Sha2_" if family == "sha2" else "Shake") + shape
        # A proof receiver changes only the dependent hash calls and uses the peer's
        # genuine default methods. Reject any concrete suite that overrides them.
        implementation = re.search(
            r"^impl ForsParams for " + typ + r"\s*\{(.*?)^\}",
            implementations,
            re.MULTILINE | re.DOTALL,
        )
        if not implementation or not re.fullmatch(
            r"\s*type K = U<"
            + str(k)
            + r">;\s*type A = U<"
            + str(a)
            + r">;\s*type MD = U<[^;]+>;\s*",
            implementation[1],
        ):
            raise ValueError(f"peer {typ} overrides its FORS algorithms")
        for op in operations:
            name = f"proof_{family}_{shape}_{op}"
            code = (
                (SCRIPTS / f"{op}.rs")
                .read_text()
                .replace('include!("shape.rs");', (SCRIPTS / "shape.rs").read_text())
                .replace("PEER_TYPE", typ)
                .replace("PARAM_N", str(n))
                .replace("PARAM_A", str(a))
                .replace("PARAM_K", str(k))
            )
            (crate / "src" / (name + ".rs")).write_text(code)
            declarations.append(f'#[cfg(kani)] #[path="{name}.rs"] mod {name};')
    with (crate / "src/fors.rs").open("a") as f:
        f.write("\n" + "\n".join(declarations) + "\n")
    return crate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--set",
        action="append",
        choices=[f"{f}_{s}" for f in ("sha2", "shake") for s in SETS],
    )
    parser.add_argument(
        "--operation", action="append", choices=["node", "row", "forest"]
    )
    args = parser.parse_args()
    shapes = (
        [tuple(s.split("_")) for s in args.set]
        if args.set
        else [(f, s) for f in ("sha2", "shake") for s in SETS]
    )
    with tempfile.TemporaryDirectory(prefix="slh-peer-fors-") as folder:
        crate = setup(
            Path(folder), shapes, args.operation or ["node", "row"]
        )
        cmd = ["cargo", "kani", "-Z", "stubbing", "--output-format", "terse"]
        subprocess.run(cmd, cwd=crate, check=True)


if __name__ == "__main__":
    main()
