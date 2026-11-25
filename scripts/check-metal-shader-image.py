#!/usr/bin/env python3
"""Check the shader source pointer and length passed by a linked Apple arm64 host."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts/apple-binary"))
from image import Image, require, sign_extend


def consumer():
    run = subprocess.run(
        [
            "cargo",
            "test",
            "--locked",
            "--release",
            "--test",
            "metal_verify",
            "--no-run",
            "--message-format=json",
        ],
        cwd=ROOT / "metal",
        capture_output=True,
        text=True,
    )
    if run.returncode:
        raise RuntimeError(run.stderr)
    (exe,) = [
        Path(r["executable"])
        for line in run.stdout.splitlines()
        if (r := json.loads(line)).get("executable")
    ]
    return exe


def call_target(pc, w):
    require(w >> 26 == 37, "expected direct call")
    return pc + 4 * sign_extend(w % 2**26, 26)


def source_at_call(image, source):
    entry, words = image.function(b"11MetalSigner3new", b"12slhdsa_metal")
    ctx, ctx_words = image.function(b"12MetalContext3new", b"12slhdsa_metal")
    ffi, _ = image.function(b"_slh_metal_ctx_create", b"_slh_metal_ctx_create")
    # These instructions save the nonvolatile registers, allocate the frame and
    # save X8. No branch or call precedes the embedded slice construction.
    require(
        words[:8]
        == [
            0xA9BB67FA,
            0xA9015FF8,
            0xA90257F6,
            0xA9034FF4,
            0xA9047BFD,
            0x910103FD,
            0xD106C3FF,
            0xAA0803F5,
        ],
        "unrecognized MetalSigner::new prefix",
    )
    adrp, add, result, movz, movk, branch = words[8:14]
    require(
        adrp & 0x9F00001F == 0x90000000 and add & 0xFFC003FF == 0x91000000,
        "shader pointer is not ADRP X0; ADD X0,X0,#offset",
    )
    pages = sign_extend(((adrp >> 5 & 0x7FFFF) << 2) | (adrp >> 29 & 3), 21)
    address = ((entry + 32) & ~4095) + 4096 * pages + (add >> 10 & 4095)
    require(
        result == 0xD10203A8
        and movz & 0xFFE0001F == 0x52800001
        and movk & 0xFFE0001F == 0x72A00001,
        "shader length is not built in W1",
    )
    size = (movz >> 5 & 65535) | ((movk >> 5 & 65535) << 16)
    require(
        call_target(entry + 52, branch) == ctx, "shader slice sent to unexpected callee"
    )
    sections = [
        name
        for name, (base, sz, _) in image.sections.items()
        if base <= address and address + size <= base + sz
    ]
    require(
        len(sections) == 1 and sections[0] in (b"__const", b"__cstring"),
        "shader slice outside a constant data section",
    )
    require(
        image.read(sections[0], address, size) == source
        and image.data.count(source) == 1,
        "embedded source bytes or length differ from the checked MSL translation unit",
    )
    # X20 and X21 hold the original byte count and address over the bzero call
    # which clears the separate 1024-byte stack diagnostic output.
    require(
        ctx_words[:12]
        == [
            0xA9BC5FF8,
            0xA90157F6,
            0xA9024FF4,
            0xA9037BFD,
            0x9100C3FD,
            0xD11083FF,
            0xF94003FF,
            0xAA0103F4,
            0xAA0003F5,
            0xAA0803F3,
            0x910023E0,
            0x52808001,
        ]
        and ctx_words[13:17] == [0x910023E2, 0xAA1503E0, 0xAA1403E1, 0x52808003],
        "MetalContext::new no longer preserves and forwards the input slice",
    )
    require(
        call_target(ctx + 68, ctx_words[17]) == ffi,
        "unexpected runtime shader creation target",
    )
    return address, call_target(ctx + 48, ctx_words[12])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", nargs="?", type=Path)
    args = parser.parse_args()
    os.environ["PATH"] = (
        str(Path.home() / ".cargo/bin") + os.pathsep + os.environ["PATH"]
    )
    path = args.binary or consumer()
    data = path.read_bytes()
    source = (
        (ROOT / "metal/shaders/slhdsa.metal").read_bytes()
        + b"\n"
        + (ROOT / "metal/shaders/slhdsa_shake.metal").read_bytes()
    )
    image = Image(data)
    ptr, clear = source_at_call(image, source)
    with tempfile.TemporaryDirectory() as tmp:
        snapshot = Path(tmp) / "image"
        snapshot.write_bytes(data)
        table = subprocess.check_output(
            ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", snapshot],
            text=True,
        )
    stubs = [
        (base, sz)
        for name, (base, sz, _) in image.sections.items()
        if name in (b"__stubs", b"__auth_stubs")
    ]
    require(
        any(base <= clear < base + sz for base, sz in stubs)
        and any(
            int(addr, 16) == clear
            for addr in re.findall(r"^(0x[0-9a-f]+)\s+\d+\s+_bzero$", table, re.M)
        ),
        "unrecognized imported diagnostic-buffer initializer",
    )
    # Mutate the loaded payload without changing the linked instruction words.
    changed = bytearray(data)
    changed[ptr - image.base] ^= 1
    try:
        source_at_call(Image(changed), source)
    except ValueError as e:
        require("embedded source" in str(e), "mutation failed at an unrelated check")
    else:
        raise ValueError("modified shader byte accepted")
    print(
        f"Mach-O {hashlib.sha256(data).hexdigest()} passes {len(source)} exact MSL bytes "
        f"({hashlib.sha256(source).hexdigest()}) to slh_metal_ctx_create."
    )


if __name__ == "__main__":
    main()
