#!/usr/bin/env python3
"""Verify the pinned RustCrypto hypertree and XMSS callers against arbitrary child results."""
import argparse
import os
import json
from pathlib import Path
import runpy
import re
import shutil
import subprocess
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-peer-digest.py")))
ROOT = common["ROOT"]
SHAPES = {"128s": (16,7,9), "128f": (16,22,3), "192s": (24,7,9),
          "192f": (24,22,3), "256s": (32,8,8), "256f": (32,17,4)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--set", choices=[f"{f}_{s}" for f in ("sha2","shake") for s in SHAPES])
    parser.add_argument("--operation", choices=["hypertree","xmss"], default="hypertree")
    parser.add_argument("--harness", choices=["sign","recover","verify_layers"])
    args = parser.parse_args()
    if args.harness and (args.harness == "verify_layers") != (args.operation == "hypertree"):
        parser.error("harness does not belong to the selected operation")
    graph = common["metadata"](ROOT/"bench/Cargo.toml")
    peer, = [x for x in graph["packages"] if x["name"] == "slh-dsa" and x["version"] == "0.2.0-rc.5"]
    pins = common["registry_checksums"](ROOT/"bench/Cargo.lock")
    with tempfile.TemporaryDirectory(prefix="slh-peer-ht-") as directory:
        p = Path(directory)
        common["unpack_peer"](peer, p, pins[peer["name"], peer["version"], peer["source"]])
        template_name = "peer-hypertree/verify.rs" if args.operation == "hypertree" else "peer-xmss/recover.rs"
        template = (ROOT/"scripts"/template_name).read_text()
        for shape, (n,d,hp) in SHAPES.items():
            for family, ty in (("sha2","Sha2_"), ("shake","Shake")):
                name = family+"_"+shape
                if args.set and args.set != name:
                    continue
                if args.operation == "xmss":
                    # Production aliases inherit the exact default method used by
                    # the observation type. Reject any per-suite override.
                    source = (p/"src/hashes"/(family+".rs")).read_text()
                    body = rf"impl\s+XmssParams\s+for\s+{ty+shape}\s*\{{\s*type HPrime = U<{hp}>;\s*\}}"
                    if len(re.findall(body, source)) != 1:
                        raise ValueError(f"XMSS implementation or height changed for {name}")
                path = "proof_"+args.operation+"_"+name
                (p/"src"/(path+".rs")).write_text(template.replace("PEER_TYPE",ty+shape)

                        .replace("PARAM_N",str(n)).replace("PARAM_HP",str(hp)).replace("PARAM_D",str(d)))
                common["append"](p/"src"/(args.operation+".rs"),f'#[cfg(kani)] #[path="{path}.rs"] mod {path};')
        # As the root package Cargo otherwise resolves upstream benchmark-only
        # dependencies, which are absent from the benchmark's production graph.
        manifest = p/"Cargo.toml"
        manifest.write_text(re.sub(r"(?ms)^\[dev-dependencies\.[^\]]+\]\n.*?(?=^\[|\Z)", "", manifest.read_text()))
        shutil.copy2(ROOT/"bench/Cargo.lock",p/"Cargo.lock")
        subprocess.run(["cargo","metadata","--offline","--format-version","1"],cwd=p,
                       stdout=subprocess.DEVNULL,check=True)
        # RustCrypto's dev dependencies can differ as the primary package. Check
        # every registry dependency reachable for a normal library build.
        metadata = json.loads(subprocess.check_output(["cargo","metadata","--locked","--format-version","1"],cwd=p))
        nodes = {node["id"]: node for node in metadata["resolve"]["nodes"]}
        pkgs = {pkg["id"]: pkg for pkg in metadata["packages"]}
        current = common["registry_checksums"](p/"Cargo.lock")
        seen = set()
        pending = [metadata["resolve"]["root"]]
        while pending:
            dep = pending.pop()
            if dep in seen:
                continue
            seen.add(dep)
            pkg = pkgs[dep]
            if pkg["source"]:
                key = (pkg["name"],pkg["version"],pkg["source"])
                if pins.get(key) != current[key]:
                    raise ValueError(f"unlocked peer dependency {key}")
            pending.extend(next_dep["pkg"] for next_dep in nodes[dep]["deps"]
                           if any(edge["kind"] != "dev" for edge in next_dep["dep_kinds"]))
        # The harness builds a legitimate seeded context before checking the tree.
        # The adjacent XMSS method is abstract. Hardware SHA used only to build
        # the context would otherwise call intrinsics unsupported by CBMC.
        env = os.environ.copy()
        env["RUSTFLAGS"] = (env.get("RUSTFLAGS","") + ' --cfg sha2_backend="soft"').strip()
        cmd = ["cargo","kani","-Z","stubbing","--output-format","terse"]
        if args.harness:
            cmd += ["--harness", "::"+args.harness]
        subprocess.run(cmd,cwd=p,env=env,check=True)


if __name__ == "__main__":
    main()
