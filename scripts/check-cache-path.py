#!/usr/bin/env python3
"""Check cache-path theorems against a fresh translation for each accelerated CPU target."""

import os
import runpy
import tempfile
from pathlib import Path

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".elan/bin"),
            str(Path.home() / ".cargo/bin"),
            os.environ["PATH"],
        ]
    )
    roots = tuple(
        "crate::cache::" + n
        for n in ("append_auth_path", "tree_root", "tree_node_count")
    )
    packages = {"Cachepath": roots, "Cachesearch": ("crate::cache::lookup_cached_index",)}
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            for package, items in packages.items():
                fresh = facade["extract"]("rust", target, package, Path(tmp), items, ())
                if {p.name for p in fresh.iterdir()} != {"Types.lean", "Funs.lean"}:
                    raise ValueError(f"unexpected {package} dependency on {target}")
                for path in fresh.iterdir():
                    if (
                        path.read_bytes()
                        != (facade["LEAN"] / package / path.name).read_bytes()
                    ):
                        raise ValueError(
                            f"{package} translation changed on {target}: {path.name}"
                        )
    facade["run"](["lake", "build", "Cachesearch.Proof"], facade["LEAN"])
    facade["audit_theorems"]("Cachesearch.Proof", ["slhdsa.cache.search", "slhdsa.cache.lookup"])
    facade["run"](["lake", "build", "Cachepath.Proof"], facade["LEAN"])
    facade["audit_theorems"](
        "Cachepath.Proof",
        [
            "slhdsa.cache.cached_xmss",
            "slhdsa.cache.path",
            "slhdsa.cache.root",
            "slhdsa.cache.offset",
        ],
    )


if __name__ == "__main__":
    main()
