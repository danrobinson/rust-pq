#!/usr/bin/env python3
"""Re-extract HashSLH-DSA digest & Alg 23/25 code on all 3 CPU targets and audit Lean proofs."""
from pathlib import Path
import os
import re
import runpy
import tempfile

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
ROOT = facade["ROOT"]
LEAN = facade["LEAN"]
CHARON = ROOT / ".tools/aeneas/charon/bin/charon"
AENEAS = ROOT / ".tools/aeneas/bin/aeneas"

STARTS = (
    "crate::prehash::PreHash::oid_der",
    "crate::prehash::PreHash::digest_len",
    "crate::prehash::PreHash::hash",
    "crate::prehash::shake128",
    "crate::prehash::format_prehash_message",
    "crate::prehash::hash_slh_sign_prehashed",
    "crate::prehash::hash_slh_verify_prehashed",
    "crate::prehash::hash_slh_sign",
    "crate::prehash::hash_slh_verify",
)

OPAQUES = (
    "crate::slh::slh_sign_internal",
    "crate::slh::slh_verify_internal",
    "crate::shake::slh::slh_sign_internal",
    "crate::shake::slh::slh_verify_internal",
    "crate::sha256::sha256",
    "crate::sha512::sha512",
    "crate::shake256::shake256",
)

EXPECTED_EXTERNALS = {
    "shake256.shake256",
    "sha512.sha512",
    "sha256.sha256",
    "slh.slh_sign_internal",
    "shake.slh.slh_sign_internal",
    "slh.slh_verify_internal",
    "shake.slh.slh_verify_internal",
}

FORBIDDEN = ("sorry", "admit", "axiom", "native_decide", "bv_decide")


def extract_target(target, scratch):
    dest = scratch / "Prehashdigest"
    dest.mkdir(parents=True)
    llbc = scratch / "prehashdigest.llbc"
    facade["run"](
        [
            CHARON,
            "cargo",
            "--preset=aeneas",
            *(arg for item in STARTS for arg in ("--start-from", item)),
            *(arg for item in OPAQUES for arg in ("--opaque", item)),
            "--dest-file",
            llbc,
            "--",
            "--locked",
            "--features",
            "platform-sha2",
            "--target",
            target,
        ],
        ROOT / "rust",
    )
    facade["run"](
        [
            AENEAS,
            "-backend",
            "lean",
            "-abort-on-error",
            "-no-progress-bar",
            "-split-files",
            "-namespace",
            "PrehashDigestRust",
            "-dest",
            dest,
            llbc,
        ],
        ROOT,
    )
    return dest


def audit_source_clean(paths):
    for path in paths:
        text = path.read_text()
        for tok in FORBIDDEN:
            if re.search(rf"\b{tok}\b", text):
                raise ValueError(f"forbidden token '{tok}' in {path}")


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".elan/bin"),
            str(Path.home() / ".cargo/bin"),
            os.environ["PATH"],
        ]
    )
    with tempfile.TemporaryDirectory() as tmp:
        for target in facade["TARGETS"]:
            scratch = Path(tmp) / target
            scratch.mkdir()
            fresh = extract_target(target, scratch)
            names = {p.name for p in fresh.iterdir()}
            if names != {"Types.lean", "Funs.lean", "FunsExternal_Template.lean"}:
                raise ValueError(f"unexpected Prehashdigest files on {target}: {names}")
            for file in ("Types.lean", "Funs.lean"):
                if (fresh / file).read_bytes() != (LEAN / "Prehashdigest" / file).read_bytes():
                    raise ValueError(f"Prehashdigest translation changed for {target}: {file}")
            found = set(
                re.findall(
                    r"(?m)^axiom\s+([^\s:]+)\b",
                    (fresh / "FunsExternal_Template.lean").read_text(),
                )
            )
            if found != EXPECTED_EXTERNALS:
                raise ValueError(
                    f"unexpected Prehashdigest externals on {target}: {found} != {EXPECTED_EXTERNALS}"
                )
            print(f"{target}: Prehashdigest translation matched byte-for-byte", flush=True)

    audit_source_clean(
        [
            ROOT / "lean/Spec/PreHash.lean",
            LEAN / "Prehashdigest/Types.lean",
            LEAN / "Prehashdigest/FunsExternal.lean",
            LEAN / "Prehashdigest/Funs.lean",
            LEAN / "Prehash/Digest.lean",
        ]
    )

    facade["run"](["lake", "build", "Spec.PreHash", "Prehash.Digest"], LEAN)
    facade["audit_theorems"](
        "Spec.PreHash",
        [
            "Spec.PreHash.shake128_length",
            "Spec.PreHash.feedWord128",
            "Spec.PreHash.prehashDigest_length",
            "Spec.PreHash.shake_128s_valid",
            "Spec.PreHash.shake_128f_valid",
            "Spec.PreHash.shake_192s_valid",
            "Spec.PreHash.shake_192f_valid",
            "Spec.PreHash.shake_256s_valid",
            "Spec.PreHash.shake_256f_valid",
            "Spec.PreHash.hashSlh_complete_prehashed",
            "Spec.PreHash.hashSlh_complete",
            "Spec.PreHash.hashSlhSign_ctx_gt_255",
            "Spec.PreHash.hashSlhVerify_ctx_gt_255",
            "Spec.PreHash.hashSlhSignPrehashed_bad_len",
            "Spec.PreHash.hashSlhVerifyPrehashed_bad_len",
        ],
    )
    facade["audit_theorems"](
        "Prehash.Digest",
        [
            "slhdsa.prehash.digest.oid_spec",
            "slhdsa.prehash.digest.digest_len_spec",
            "slhdsa.prehash.digest.keccak_f1600_spec",
            "slhdsa.prehash.digest.shake128_spec",
            "slhdsa.prehash.digest.hash_stack_spec",
            "slhdsa.prehash.digest.digest_spec",
            "slhdsa.prehash.digest.format_prehash_message_spec",
            "slhdsa.prehash.digest.hash_slh_sign_prehashed_spec",
            "slhdsa.prehash.digest.hash_slh_verify_prehashed_spec",
            "slhdsa.prehash.digest.hash_slh_sign_spec",
            "slhdsa.prehash.digest.hash_slh_verify_spec",
            "slhdsa.prehash.digest.hash_slh_complete_rust",
        ],
    )
    print("ALL Prehash.Digest & Spec.PreHash checks and axiom audits PASSED!", flush=True)


if __name__ == "__main__":
    main()
