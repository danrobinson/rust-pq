#!/usr/bin/env python3
"""Re-extract zero-copy segmented SHAKE message hashing across all 3 targets and audit Lean proofs."""
from pathlib import Path
import os
import re
import runpy
import tempfile

facade = runpy.run_path(str(Path(__file__).with_name("check-platform-facade.py")))
ROOT, LEAN, run = facade["ROOT"], facade["LEAN"], facade["run"]

SEG_ROOTS = (
    "crate::shake::hash::prf_msg_ctx",
    "crate::shake::hash::h_msg_ctx",
    "crate::shake::slh::shake_sign_ctx",
    "crate::shake::slh::shake_verify_ctx",
    "crate::shake::slh::slh_sign",
    "crate::shake::slh::slh_verify",
)

SEG_CUTS = (
    "crate::shake256",
    "crate::shake::slh::slh_sign_internal",
    "crate::shake::slh::slh_verify_internal",
    "crate::shake::slh::with_context",
    "crate::shake::slh::digest_tree",
    "crate::shake::slh::digest_leaf",
    "crate::shake::fors::fors_sign",
    "crate::shake::fors::fors_pk_from_sig",
    "crate::shake::ht::ht_sign",
    "crate::shake::ht::ht_verify",
    "crate::util::block",
    "crate::address::Adrs::new",
    "crate::address::Adrs::with_tree",
    "crate::address::Adrs::with_type",
    "crate::address::Adrs::with_keypair",
)

EXPECTED_EXTERNAL_FUNS = {
    "shake256.Sponge.new",
    "shake256.Sponge.absorb",
    "shake256.Sponge.finish",
    "shake.ht.ht_sign",
    "shake.ht.ht_verify",
    "shake.slh.digest_tree",
    "shake.slh.digest_leaf",
    "shake.slh.slh_sign_internal",
    "shake.slh.slh_verify_internal",
    "shake.slh.with_context",
    "shake.fors.fors_sign",
    "shake.fors.fors_pk_from_sig",
    "util.block",
}

THEOREMS = [
    "Shakeopt.Segmented.keccak_feed_append",
    "Shakeopt.Segmented.sponge_absorb_append",
    "Shakeopt.Segmented.prf_msg_ctx_spec",
    "Shakeopt.Segmented.prf_msg_ctx_params",
    "Shakeopt.Segmented.prf_msg_ctx_eq_contiguous",
    "Shakeopt.Segmented.h_msg_ctx_spec",
    "Shakeopt.Segmented.h_msg_ctx_params",
    "Shakeopt.Segmented.h_msg_ctx_eq_contiguous",
    "Shakeopt.Segmented.shake_sign_ctx_spec",
    "Shakeopt.Segmented.shake_verify_ctx_spec",
    "Shakeopt.Segmented.slh_sign_spec",
    "Shakeopt.Segmented.slh_verify_spec",
]


def shared_types(source: str) -> str:
    source = source.replace("public import Aeneas", "public import Slhdsa.Types")
    source = source.replace("public import Seg.TypesExternal", "public import Shakeopt.Seg.TypesExternal")
    original = (LEAN / "Slhdsa/Types.lean").read_text()
    for name in ("address.Adrs", "params.Params"):
        match = re.search(
            r"^structure " + re.escape(name) + r"\b[\s\S]*?(?=\n\n)",
            source,
            re.MULTILINE,
        )
        if match is None or match.group() + "\n\n" not in original:
            raise ValueError(f"source declaration of {name} differs from slhdsa.{name}")
        source = source[: match.start()] + f"abbrev {name} := slhdsa.{name}" + source[match.end() :]
    return source


def check_target(scratch: Path, target: str) -> None:
    package = scratch / "Seg"
    llbc = scratch / "seg.llbc"
    run(
        [
            ROOT / ".tools/aeneas/charon/bin/charon",
            "cargo",
            "--preset=aeneas",
            *(arg for item in SEG_ROOTS for arg in ("--start-from", item)),
            *(arg for item in SEG_CUTS for arg in ("--opaque", item)),
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
    run(
        [
            ROOT / ".tools/aeneas/bin/aeneas",
            "-backend",
            "lean",
            "-abort-on-error",
            "-no-progress-bar",
            "-namespace",
            "ShakeoptSeg",
            "-split-files",
            "-dest",
            package,
            llbc,
        ],
        ROOT,
    )
    funs = (package / "Funs.lean").read_text()
    funs = funs.replace("public import Seg.Types", "public import Shakeopt.Seg.Types")
    funs = funs.replace("public import Seg.FunsExternal", "public import Shakeopt.Seg.FunsExternal")
    if funs != (LEAN / "Shakeopt/Seg/Funs.lean").read_text():
        raise ValueError(f"segmented SHAKE functions differ on {target}")
    if shared_types((package / "Types.lean").read_text()) != (LEAN / "Shakeopt/Seg/Types.lean").read_text():
        raise ValueError(f"segmented SHAKE types differ on {target}")
    ext_types = set(
        re.findall(r"^axiom ([^ :\n]+)", (package / "TypesExternal_Template.lean").read_text(), re.MULTILINE)
    )
    if ext_types != {"shake256.Sponge"}:
        raise ValueError(f"unexpected external types on {target}: {ext_types}")
    ext_funs = set(
        re.findall(r"^axiom ([^ :\n]+)", (package / "FunsExternal_Template.lean").read_text(), re.MULTILINE)
    )
    if ext_funs != EXPECTED_EXTERNAL_FUNS:
        raise ValueError(f"unexpected external functions on {target}: {ext_funs}")
    print(f"{target}: matched Shakeopt.Seg extraction ({len(SEG_ROOTS)} roots, {len(ext_funs)} verified bindings)", flush=True)


def main() -> None:
    os.environ["PATH"] = os.pathsep.join(
        [str(Path.home() / ".elan/bin"), str(Path.home() / ".cargo/bin"), os.environ["PATH"]]
    )
    for target in facade["TARGETS"]:
        with tempfile.TemporaryDirectory() as tmp:
            check_target(Path(tmp), target)
    run(["lake", "build", "Shakeopt.Segmented"], LEAN)
    facade["audit_theorems"]("Shakeopt.Segmented", THEOREMS)
    print(f"Shakeopt.Segmented: audited {len(THEOREMS)} theorems strictly within [propext, Classical.choice, Quot.sound]", flush=True)


if __name__ == "__main__":
    main()
