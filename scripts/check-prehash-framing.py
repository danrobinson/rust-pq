#!/usr/bin/env python3
"""Re-extract the formatter for each accelerated CPU target and audit its Lean proof."""
from pathlib import Path
import os
import runpy
import tempfile

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))


def main():
    os.environ["PATH"] = os.pathsep.join([str(Path.home()/".elan/bin"), str(Path.home()/".cargo/bin"), os.environ["PATH"]])
    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"]:
            scratch = Path(tmp)/target
            scratch.mkdir()
            fresh = facade["extract"]("rust", target, "Prehash", scratch,
                                      ("crate::prehash::format_prehash_message",), ())
            for file in ("Types.lean", "Funs.lean"):
                if (fresh/file).read_bytes() != (facade["LEAN"]/"Prehash"/file).read_bytes():
                    raise ValueError(f"prehash translation changed for {target}: {file}")
            if set(p.name for p in fresh.iterdir()) != {"Types.lean", "Funs.lean"}:
                raise ValueError(f"unexpected prehash translation dependencies on {target}")
    facade["run"](["lake", "build", "Prehash.Proof"], facade["LEAN"])
    facade["audit_theorems"]("Prehash.Proof", ["slhdsa.prehash.framing"])


if __name__ == "__main__":
    main()
