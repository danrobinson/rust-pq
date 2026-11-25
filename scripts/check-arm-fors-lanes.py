#!/usr/bin/env python3
"""Bounded proof of native SHA-256 FORS leaf and path callers for every SHA-2 set."""

import os
from pathlib import Path
import re
import shutil
import sys
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
GEOMETRY = [
    (16, 14, 12),
    (16, 33, 6),
    (24, 17, 14),
    (24, 33, 8),
    (32, 22, 14),
    (32, 35, 9),
]


def function(source, name):
    (match,) = re.finditer(r"^(?:pub\(crate\) )?fn " + name + r"\b", source, re.M)
    return source[match.start() : source.index("\n}", match.end()) + 2]


def generate():
    source = (ROOT / "rust/src/sha256/arm_wide.rs").read_text()
    for name, call in (
        (
            "fors_verify_leaves",
            "fors_verify_leaves_active::<N>(state, adrs, sig, indices, vals, height)",
        ),
        (
            "fors_path_level_16",
            "fors_path_level_16_active(state, adrs, sig, indices, vals, height, level_offset)",
        ),
    ):
        wrapper = function(source, name)
        body_only = wrapper[wrapper.index("{") + 1 : -1]
        actual = re.sub(r"//[^\n]*", "", body_only)
        if (
            actual.split()
            != ("debug_assert!(available()); unsafe { " + call + " };").split()
        ):
            raise ValueError(f"unverified native wrapper: {name}")
    body = "\n".join(
        function(source, name)
        for name in (
            "step4_shared_head",
            "fors_verify_leaves_active",
            "fors_path_level_16_active",
        )
    )
    body = body.replace("fn fors_", "pub(super) fn fors_")
    if body.count("arm::load_be(&sig[") != 4:
        raise ValueError("expected four signature sibling loads")
    body = body.replace("arm::load_be(&sig[", "load_sibling(&sig[")
    stores = r"vst1q_u8\(([^,]+), vrev32q_u8\(vreinterpretq_u8_u32\((x\[[^\]]+\])\)\)\)"
    body, n = re.subn(stores, r"store_be(\1, \2)", body)
    if n != 4:
        raise ValueError("expected four exact big-endian NEON digest store sequences")
    program = (HERE / "arm-fors/lanes.rs").read_text().replace("// PRODUCTION", body)
    for n, k, a in GEOMETRY:
        for parent in [False, True] if n == 16 else [False]:
            name = f"{'parent' if parent else 'leaf'}_{n}_{k}"
            program += f"\n#[kani::proof]\n#[kani::unwind(40)]\nfn {name}() {{ check::<{n},{k},{a},{k * (a + 1) * n},{str(parent).lower()}>(); }}\n"
    return program


def paired():
    source = (ROOT / "rust/src/sha512/paired.rs").read_text()
    body = "\n".join(
        function(source, name)
        for name in ("path_parents_batch", "path_parents_batch_active")
    )
    program = (HERE / "arm-fors/paired.rs").read_text().replace("// PRODUCTION", body)
    for n, k, a in GEOMETRY:
        if n != 16:
            program += f"\n#[kani::proof]\n#[kani::unwind(40)]\nfn pair_{n}_{k}() {{ check::<{n},{k},{a},{k * (a + 1) * n}>(); }}\n"
    return program


def main():
    drv = (
        os.environ.get("KANI")
        or shutil.which("kani")
        or str(Path.home() / ".kani/kani-0.68.0/bin/kani-driver")
    )
    env = dict(
        os.environ,
        PATH=os.pathsep.join(
            [str(Path(drv).parent), str(Path.home() / ".cargo/bin"), os.environ["PATH"]]
        ),
    )
    with tempfile.TemporaryDirectory() as tmp:
        args = sys.argv[1:]
        family = args.pop(0) if args and args[0] in ("lanes", "paired") else None
        for name, make in (("lanes", generate), ("paired", paired)):
            if family and family != name:
                continue
            file = Path(tmp) / (name + ".rs")
            file.write_text(make())
            subprocess.run([drv, str(file), *args], env=env, check=True)


if __name__ == "__main__":
    main()
