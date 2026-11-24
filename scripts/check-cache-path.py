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
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            fresh = facade["extract"]("rust", target, "Cachepath", Path(tmp), roots, ())
            if {p.name for p in fresh.iterdir()} != {"Types.lean", "Funs.lean"}:
                raise ValueError(f"unexpected cache dependency on {target}")
            for path in fresh.iterdir():
                if (
                    path.read_bytes()
                    != (facade["LEAN"] / "Cachepath" / path.name).read_bytes()
                ):
                    raise ValueError(
                        f"cache translation changed on {target}: {path.name}"
                    )
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
