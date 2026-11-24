#!/usr/bin/env python3
"""Check all 60 named SHA-2 core operations of the portable platform-sha2 fallback."""
from pathlib import Path
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-x86-core-proof.py")))
TARGETS = ("i686-unknown-linux-gnu", "powerpc64-unknown-linux-gnu", "riscv64gc-unknown-none-elf")
BINDINGS = {
    "sha256.compress_portable": "slhdsa.sha256.compress_portable",
    "sha512.compress_portable": "slhdsa.sha512.compress_portable",
    "slh.message.randomizer": "PortableMessage.SegmentedApiRust.slh.message.randomizer",
    "slh.message.digest": "PortableMessage.SegmentedApiRust.slh.message.digest",
}
OPS = ("slh_keygen_internal", "slh_sign_internal", "slh_verify_internal", "slh_sign", "slh_verify",
       "keygen", "public_key", "sign", "sign_deterministic", "verify")
ENTRIES = [(f"sets.{s}.{op}", f"PortableAPI.slhdsa.{s}.{op}_spec",
            ("" if op == "public_key" else "PortableAPI.") + f"slhdsa.sets.{s}.{op}")
           for s in shared["common"]["SETS"] for op in OPS]


if __name__ == "__main__":
    shared["run"](["lake", "build", "Portableplatform.Public"], shared["LEAN"])
    for target in TARGETS:
        with tempfile.TemporaryDirectory() as temp:
            shared["check"](Path(temp), ENTRIES, BINDINGS, "Portableplatform.Public", "PortableTarget", target)
