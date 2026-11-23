#!/usr/bin/env python3
"""Check the extracted streaming loop and its SHA-256 and SHA-512 refinements."""
from pathlib import Path
import runpy
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]


def check(target, scratch):
    package = scratch / "Segmented"
    llbc = scratch / "segmented.llbc"
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         "--start-from", "crate::slh::message::continued", "--dest-file", llbc,
         "--", "--locked", "--features", "platform-sha2", "--target", target], ROOT / "rust")
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar",
         "-namespace", "SegmentedRust", "-split-files", "-dest", package, llbc], ROOT)
    for filename in ("Funs.lean", "Types.lean"):
        if (package / filename).read_bytes() != (LEAN / "Segmented" / filename).read_bytes():
            raise ValueError(f"segmented hashing translation {filename} differs for {target}")
    if list(package.glob("*External*")):
        raise ValueError(f"unexpected external leaf in segmented hashing for {target}")


if __name__ == "__main__":
    for target in ("x86_64-unknown-linux-gnu", "aarch64-apple-darwin", "aarch64-unknown-linux-gnu"):
        with tempfile.TemporaryDirectory() as temp:
            check(target, Path(temp))
    run(["lake", "build", "Segmented.Instances"], LEAN)
