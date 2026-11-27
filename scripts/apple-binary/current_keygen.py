#!/usr/bin/env python3
"""Bind both successful public keygen ABIs to the current Apple arm64 consumer."""

import hashlib
from pathlib import Path
import struct
import sys

sys.dont_write_bytecode = True
from public_witness import check_witness
from image import require, sign_extend
from keygen_witness import path

ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "lean/Spec/ApplePublicKeygenWitness.lean"


def page(pc, w):
    require(w & 0x9F000000 == 0x90000000, "expected PC-relative constant")
    return (pc & ~4095) + 4096 * sign_extend(
        ((w >> 5 & 0x7FFFF) << 2) | (w >> 29 & 3), 21
    )


def sha256_seed(image, suffix):
    entry, ops = image.function(b"3slh19slh_keygen_internal" + suffix, b"6slhdsa")
    first = ops.index(0x6E200800)
    end = ops.index(0x6F00E402, first)
    words = ops[first:end]
    pc = entry + 4 * first

    def target(i, scale):
        head, op = words[i : i + 2]
        register = head & 31
        require((op >> 5 & 31) == register, "mismatched literal base")
        require(
            (op & 0xFFC00000) == (0x3DC00000 if scale == 16 else 0x91000000),
            "unexpected literal reference",
        )
        return page(pc + 4 * i, head) + scale * (op >> 10 & 4095)

    iv = target(4, 16)
    require(target(6, 16) == iv + 16, "SHA-256 IV halves not adjacent")
    h = list(struct.unpack("<8I", image.read(b"__const", iv, 32)))
    k = list(struct.unpack("<64I", image.read(b"__const", target(9, 1), 256)))
    return (pc, words), f"def seed128 : Seed := .inlined 0x{pc:x} {words} {h} {k}"


def certificate(image):
    lines = [
        "import Spec.ArmPublicKeygen",
        "namespace CurrentAppleKeygen",
        "open Spec.ArmKeygen Spec.ArmPublicKeygen",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    names = []
    for family in ("shake", "sha2"):
        shake = family == "shake"
        for n in (16, 24, 32):
            suffix = f"Kj{n:x}_EB{6 if shake else 4}_".encode()
            crate = b"6slhdsa5shake" if shake else b"6slhdsa"
            root, _ = image.function(
                (b"5batch12xmss_subtree" if shake else b"4xmss9xmss_node") + suffix,
                crate,
            )
            ext = inline = None
            seed = ".shake"
            if not shake and n == 16:
                inline, decl = sha256_seed(image, suffix)
                lines.append(decl)
                seed = "seed128"
            elif not shake:
                ext, _ = image.function(b"4hash8seed_ctx" + suffix, crate)
                seed = f".external 0x{ext:x}"
            for shape in "sf":
                suite = f"{family}_{8 * n}{shape}"
                for op in ("keygen", "slh_keygen_internal"):
                    entry, _ = image.function(
                        f"{len(suite)}{suite}{len(op)}{op}".encode(), b"6slhdsa4sets"
                    )
                    steps = path(image, entry, root, ext, inline)
                    (param,) = [
                        page(pc, w) + (v >> 10 & 4095)
                        for (pc, w), (_, v) in zip(steps, steps[1:])
                        if w & 0x9F00001F == 0x90000000 and v & 0xFFC003FF == 0x91000000
                    ]
                    name = f"{suite}_{op}"
                    p = f"Spec.{suite}"
                    rows = ", ".join(f"(0x{pc:x},0x{w:08x})" for pc, w in steps)
                    config = f"{name}_config"
                    trace = f"{name}_path"
                    checked = f"{name}_checked"
                    lines += [
                        f"def {config} : Config := ⟨{n},{p}.d,{p}.hp,0x{entry:x},0x{root:x},0x{param:x},{list(image.read(b'__const', param, 36))},{str(op != 'keygen').lower()},{seed}⟩",
                        f"theorem {name}_params : {config}.params=parameterBytes {p} := by decide",
                        f"def {trace} := [{rows}]",
                        f"theorem {checked} : runWith rootCall {config} {trace} = some (secret {n},publicKey {n}) := by decide",
                        f"theorem {name}_fips (sk prf pk : Spec.Bytes) (hs : sk.length={n}) (hr : prf.length={n}) (hp : pk.length={n}) :",
                        f"    execute {p} {config} {trace} sk prf pk=some (Spec.slhKeygenInternal {p} sk prf pk) :=",
                        f"  execute_fips {p} (by constructor <;> decide) {config} {trace} {checked} (by decide) (by decide) sk prf pk hs hr hp",
                    ]
                    names.extend((name + "_params", checked, name + "_fips"))
                    if suite in ("shake_128s", "sha2_192s") and op == "keygen":
                        bad = list(image.read(b"__const", param, 36))
                        bad[24] ^= 1
                        lines.append(
                            f"theorem {name}_wrongHeight : runWith rootCall {{ {config} with params := {bad} }} {trace} ≠ some (secret {n},publicKey {n}) := by decide"
                        )
                        lines.append(
                            f"theorem {name}_wrongRoot : runWith rootCall {{ {config} with root := 0x{root + 4:x} }} {trace} ≠ some (secret {n},publicKey {n}) := by decide"
                        )
    return "\n".join(lines + ["end CurrentAppleKeygen", ""]), [
        "CurrentAppleKeygen." + n for n in names
    ]


def main():
    check_witness(__doc__, certificate, DEST, ["Spec.ArmPublicKeygen"])
    print(
        "Checked all 24 current Apple keygen drivers, parameters, complete key buffers, and callee arguments."
    )


if __name__ == "__main__":
    main()
