"""Extract linked keygen PCs, ARM words and parameter bytes for independent Lean replay."""

import argparse
import hashlib
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image, require, sign_extend


def path(image, entry, root):
    pc = entry
    links = []
    words = []
    for _ in range(256):
        if pc == root:
            pc = links.pop()
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
    for n in (16, 24, 32):
        for variant in "sf":
            p = f"shake_{n * 8}{variant}"
            label = f"{len(p)}{p}"
            root, _ = image.function(
                f"4xmss9xmss_nodeKj{n:x}_EB6_".encode(), b"6slhdsa5shake"
            )
            for name in ("keygen", "slh_keygen_internal"):
                entry, _ = image.function(
                    f"{label}{len(name)}{name}".encode(), b"6slhdsa4sets"
                )
                candidate = path(image, entry, root)
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
                    f"0x{entry:x}, 0x{root:x}, 0x{param:x}, {record}, {str(name != 'keygen').lower()}⟩",
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
