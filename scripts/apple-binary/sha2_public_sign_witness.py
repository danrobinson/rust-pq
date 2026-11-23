"""Extract the SHA-2 public signing entries and shared context/message dispatchers."""

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image


def array(words):
    return (
        "#["
        + ",\n".join(
            ",".join(hex(w) for w in words[i : i + 8]) for i in range(0, len(words), 8)
        )
        + "]"
    )


def certificate(image):
    free = image.function(b"___rust_dealloc", b"___rustc")[0]
    lines = [
        "import Spec.ArmSha2PublicSign",
        "import Spec.AppleSha2InternalSignerWitness",
        "import Spec.AppleSegmentedFrameWitness",
        "namespace LinkedAppleSha2PublicSign",
        "open Spec.ArmSha2PublicSign",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
    ]
    for n in (16, 24, 32):
        dispatch, code = image.function(
            f"3slh8slh_signKj{n:x}_EB4_".encode(), b"6slhdsa"
        )
        lines.append(f"def dispatch{n} : Array Nat := " + array(code))
        for v in "sf":
            label = f"sha2_{8 * n}{v}"
            short = f"LinkedSha2InternalSigner.{label}"
            segmented = f"LinkedSegmentedFrame.{label}"
            for suffix, det in [
                (b"4sign", False),
                (b"8slh_sign", False),
                (b"18sign_deterministic", True),
            ]:
                addr, words = image.function(suffix, f"6slhdsa4sets9{label}".encode())
                name = label + "_" + suffix.decode().lstrip("0123456789")
                lines += [
                    f"def {name} : Image := ⟨Spec.{label}.n,{str(det).lower()},0x{addr:x},"
                    + array(words)
                    + f",0x{dispatch:x},dispatch{n},{short}.cfg.param,LinkedApplePureFrame.image.entry,{short}.body,{segmented}.entry,0x{free:x}⟩",
                    f"theorem {name}_checked (valid short : Bool) : run {name} valid short = some (expected valid short) := by",
                    "  cases valid <;> cases short <;> decide +kernel",
                ]
    for tag, base, field, i, delta, valid, short in [
        ("wrongContextCutoff", "sign", "dispatchWords", 6, 1 << 10, False, True),
        ("wrongMessageCutoff", "sign", "dispatchWords", 11, 1 << 10, True, False),
        ("wrongSegmentTarget", "sign", "dispatchWords", 18, 1, True, False),
        ("wrongResult", "sign", "dispatchWords", 40, 1 << 10, True, True),
        ("wrongSeed", "sign_deterministic", "words", 8, 1 << 10, True, False),
    ]:
        name = "sha2_128s_" + base
        lines += [
            f"theorem {tag} : run {{{name} with {field} := {name}.{field}.modify {i} (· ^^^ {delta})}} {str(valid).lower()} {str(short).lower()} ≠",
            f"    some (expected {str(valid).lower()} {str(short).lower()}) := by decide +kernel",
        ]
    return "\n".join(lines + ["end LinkedAppleSha2PublicSign", ""])


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("binary", type=Path)
    print(certificate(Image(p.parse_args().binary.read_bytes())), end="")
