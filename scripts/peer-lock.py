"""Prepare a proof copy of an archive and validate its normal dependency closure."""
import json
from pathlib import Path
import re
import runpy
import shutil
import subprocess

common = runpy.run_path(str(Path(__file__).with_name("check-peer-digest.py")))
ROOT = common["ROOT"]


def unpack(path, name, version, *, add_dependency=None):
    graph = common["metadata"](ROOT / "bench/Cargo.toml")
    package, = [p for p in graph["packages"] if p["name"] == name and p["version"] == version]
    lock = ROOT / "bench/Cargo.lock"
    pins = common["registry_checksums"](lock)
    common["unpack_peer"](package, path, pins[name, version, package["source"]])
    manifest = path / "Cargo.toml"
    # The crate's benchmark and test-only packages are outside the release graph.
    manifest.write_text(re.sub(r"(?ms)^\[dev-dependencies\.[^\]]+\]\n.*?(?=^\[|\Z)", "", manifest.read_text()))
    if add_dependency:
        dep, dest = add_dependency
        common["append"](manifest, f"[dependencies.{dep}]\npath = " + json.dumps(str(dest)))
    shutil.copy2(lock, path / "Cargo.lock")
    subprocess.run(["cargo", "metadata", "--offline", "--format-version", "1"], cwd=path,
                   stdout=subprocess.DEVNULL, check=True)
    resolved = common["metadata"](manifest)
    nodes = {n["id"]: n for n in resolved["resolve"]["nodes"]}
    packages = {p["id"]: p for p in resolved["packages"]}
    current = common["registry_checksums"](path / "Cargo.lock")
    pending = [resolved["resolve"]["root"]]
    seen = set()
    while pending:
        id_ = pending.pop()
        if id_ in seen:
            continue
        seen.add(id_)
        p = packages[id_]
        if p["source"]:
            k = p["name"], p["version"], p["source"]
            if current[k] != pins.get(k):
                raise ValueError(f"dependency outside benchmark lock: {k}")
        pending.extend(d["pkg"] for d in nodes[id_]["deps"] if any(e["kind"] != "dev" for e in d["dep_kinds"]))
    return manifest
