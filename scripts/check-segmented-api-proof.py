#!/usr/bin/env python3
"""Re-extract the message digest and randomizer, sharing nominally identical Lean types."""
from pathlib import Path
import re
import runpy
import tempfile

common = runpy.run_path(str(Path(__file__).with_name("check-arm-api-proof.py")))
ROOT, LEAN, run = common["ROOT"], common["LEAN"], common["run"]
BINDINGS = ("slh::message::continued", "sha256::compress", "sha512::compress",
            "sha256::sha256_from", "sha512::sha512_from", "hash::mgf1_sha256", "hash::mgf1_sha512")


def shared_types(source):
    source = source.replace("public import Aeneas", "public import Slhdsa.Types\npublic import Segmented.Types")
    for name, module, owner in [("params.Params", "Slhdsa", "slhdsa"),
                                ("slh.message.MessageHash", "Segmented", "SegmentedRust")]:
        match = re.search(r"^structure " + re.escape(name) + r"\b[\s\S]*?(?=\n\n)", source, re.MULTILINE)
        original = (LEAN / module / "Types.lean").read_text()
        if match is None or match.group() + "\n\n" not in original:
            raise ValueError(f"the source declaration of {name} differs from {owner}.{name}")
        source = source[:match.start()] + f"abbrev {name} := {owner}.{name}" + source[match.end():]
    return source


def check(scratch, target):
    package, llbc = scratch / "Segmentedapi", scratch / "segmentedapi.llbc"
    run([ROOT / ".tools/aeneas/charon/bin/charon", "cargo", "--preset=aeneas",
         "--start-from", "crate::slh::message::randomizer", "--start-from", "crate::slh::message::digest",
         *(arg for external in BINDINGS for arg in ("--opaque", "crate::" + external)),
         "--dest-file", llbc, "--", "--locked", "--features", "platform-sha2", "--target", target], ROOT / "rust")
    run([ROOT / ".tools/aeneas/bin/aeneas", "-backend", "lean", "-abort-on-error", "-no-progress-bar",
         "-namespace", "SegmentedApiRust", "-split-files", "-dest", package, llbc], ROOT)
    if (package / "Funs.lean").read_bytes() != (LEAN / "Segmentedapi/Funs.lean").read_bytes():
        raise ValueError(f"message functions differ on {target}")
    if shared_types((package / "Types.lean").read_text()) != (LEAN / "Segmentedapi/Types.lean").read_text():
        raise ValueError(f"message types differ on {target}")
    names = set(re.findall(r"^axiom ([^ :\n]+)", (package / "FunsExternal_Template.lean").read_text(), re.MULTILINE))
    if names != {x.replace("::", ".") for x in BINDINGS}:
        raise ValueError(f"unexpected external bindings on {target}: {names}")


if __name__ == "__main__":
    for target in ("x86_64-unknown-linux-gnu", "aarch64-apple-darwin", "aarch64-unknown-linux-gnu"):
        with tempfile.TemporaryDirectory() as temp:
            check(Path(temp), target)
    run(["lake", "build", "Segmentedapi.Funs"], LEAN)
