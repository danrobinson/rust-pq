"""Extract linked keygen PCs, ARM words and parameter bytes for independent Lean replay."""

import argparse
import hashlib
import struct
from itertools import product
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image, require, sign_extend


def path(image, entry, root, seed_entry, inline):
    pc = entry
    links = []
    words = []
    for _ in range(256):
        if pc == root or pc == seed_entry:
            pc = links.pop()
        if inline and pc == inline[0]:
            pc += 4 * len(inline[1])
        word = int.from_bytes(image.read(b"__text", pc, 4), "little")
        words.append((pc, word))
        if word == 0xD65F03C0:
            if not links:
                return words
            pc = links.pop()
        elif word >> 26 in (5, 37):
            if word >> 26 == 37:
                links.append(pc + 4)
            pc += 4 * sign_extend(word % (1 << 26), 26)
        else:
            pc += 4
    raise ValueError("unbounded keygen candidate")


def certificate(image):
    lines = [
        "import Spec.ArmKeygen",
        "namespace LinkedAppleKeygen",
        "open Spec.ArmKeygen",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    for family, n in product(("shake", "sha2"), (16, 24, 32)):
        seed_entry = inline = None
        seed = ".shake"
        shake = family == "shake"
        mono = f"Kj{n:x}_EB{6 if shake else 4}_"
        crate = b"6slhdsa5shake" if shake else b"6slhdsa"
        if not shake and n > 16:
            seed_entry, _ = image.function(("4hash8seed_ctx" + mono).encode(), crate)
            seed = f".external 0x{seed_entry:x}"
        if not shake and n == 16:
            pc, ops = image.function(
                ("3slh19slh_keygen_internal" + mono).encode(), crate
            )
            start = ops.index(0x6E200800)
            end = ops.index(0x6F00E402)
            inline = (pc + 4 * start, ops[start:end])
            # The capped instruction block and its linked start are checked separately
            # by Lean. Its exact ADRP/LDR instructions refer to these two constants.
            iv = list(struct.unpack("<8I", image.read(b"__const", 0x1000D5F30, 32)))
            rounds = list(
                struct.unpack("<64I", image.read(b"__const", 0x1000DC470, 256))
            )
            lines.append(
                f"def seedKernel : Seed := .inlined 0x{inline[0]:x} "
                f"{list(inline[1])} {iv} {rounds}"
            )
            seed = "seedKernel"
        for variant in "sf":
            p = f"{family}_{n * 8}{variant}"
            label = f"{len(p)}{p}"
            root, _ = image.function(("4xmss9xmss_node" + mono).encode(), crate)
            for name in ("keygen", "slh_keygen_internal"):
                entry, _ = image.function(
                    f"{label}{len(name)}{name}".encode(), b"6slhdsa4sets"
                )
                candidate = path(image, entry, root, seed_entry, inline)
                addresses = [
                    (
                        pc // 4096
                        + sign_extend(((w >> 5 & 0x7FFFF) << 2) | (w >> 29 & 3), 21)
                    )
                    * 4096
                    + ((v >> 10) & 4095)
                    for (pc, w), (_, v) in zip(candidate, candidate[1:])
                    if w & 0x9F00001F == 0x90000000 and v & 0xFFC003FF == 0x91000000
                ]
                (param,) = addresses
                record = list(image.read(b"__const", param, 36))
                prefix = f"{p}_{name}"
                lines += [
                    f"def {prefix}_config : Config := ⟨Spec.{p}.n, Spec.{p}.d, Spec.{p}.hp, "
                    f"0x{entry:x}, 0x{root:x}, 0x{param:x}, {record}, {str(name != 'keygen').lower()}, {seed}⟩",
                    f"theorem {prefix}_parameters : {prefix}_config.params = parameterBytes Spec.{p} := by decide",
                    f"def {prefix}_path : List (Nat × Nat) := ["
                    + ",\n ".join(f"(0x{pc:x},0x{w:08x})" for pc, w in candidate)
                    + "]",
                    f"theorem {prefix}_checked : run {prefix}_config {prefix}_path = "
                    f"some (secret Spec.{p}.n, publicKey Spec.{p}.n) := by decide",
                ]
                lines.append(
                    f"def {prefix}_keyTrace {{out}} "
                    f"(h : run {prefix}_config {prefix}_path = some out) "
                    f"(sources : Nat → Spec.Bytes) (sizes : ∀ i < 4, (sources i).length = Spec.{p}.n) := "
                    f"@concreteKeyGeneration Spec.{p} out {prefix}_config {prefix}_path h "
                    f"{prefix}_checked sources sizes (by decide) (by decide)"
                )
                if p == "sha2_192s" and name == "keygen":
                    require(
                        sum(w == 0xAA0303E0 for _, w in candidate) == 1,
                        "missing seed input",
                    )
                    lines.append(
                        f"theorem wrongSeedInput : run {prefix}_config ({prefix}_path.map "
                        "(fun (pc,w) => (pc,if w == 0xaa0303e0 then 0xaa0103e0 else w))) "
                        "≠ some (secret 24, publicKey 24) := by decide"
                    )
                if p == "sha2_128s" and name == "keygen":
                    for control, field in (
                        ("wrongCompressionWord", "words"),
                        ("wrongRoundConstant", "k"),
                    ):
                        replacement = ".inlined entry " + (
                            "(0 :: words.drop 1) iv k"
                            if field == "words"
                            else "words iv (0 :: k.drop 1)"
                        )
                        lines.append(
                            f"private def {control}Seed : Seed := match seedKernel with\n"
                            f"  | .inlined entry words iv k => {replacement}\n"
                            "  | _ => .shake"
                        )
                        lines.append(
                            f"theorem {control} : run {{ {prefix}_config with seed := {control}Seed }} "
                            f"{prefix}_path ≠ some (secret 16, publicKey 16) := by decide"
                        )
                if p == "shake_128s" and name == "keygen":
                    controls = [
                        ("wrongTopLayer", 0x51000508, 0x51000108),
                        ("wrongPublicOutput", 0x3D8006A0, 0x3D8002A0),
                        ("wrongSavedPair", 0xA9487BFD, 0xA9477BFD),
                    ]
                    for control, old, new in controls:
                        require(
                            sum(w == old for _, w in candidate) == 1,
                            "missing " + control,
                        )
                        lines.append(
                            f"theorem {control} : run {prefix}_config ({prefix}_path.map "
                            f"(fun (pc,w) => (pc,if w == 0x{old:x} then 0x{new:x} else w))) "
                            f"≠ some (secret 16, publicKey 16) := by decide"
                        )
                    bad_record = record.copy()
                    bad_record[24] ^= 1
                    lines.append(
                        f"theorem wrongHeightRecord : run "
                        f"{{ {prefix}_config with params := {bad_record} }} {prefix}_path "
                        "≠ some (secret 16, publicKey 16) := by decide"
                    )
    lines += [
        "#print axioms sha2_128s_keygen_checked",
        "#print axioms sha2_256f_slh_keygen_internal_keyTrace",
        "#print axioms shake_128s_keygen_checked",
        "#print axioms shake_256f_slh_keygen_internal_keyTrace",
        "end LinkedAppleKeygen",
    ]
    return "\n".join(lines) + "\n"


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    opts = parser.parse_args()
    sys.stdout.write(certificate(Image(opts.binary.read_bytes())))
