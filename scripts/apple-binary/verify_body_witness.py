"""Extract the SHAKE verifier bodies and their linked contract destinations for Lean replay."""

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image


def certificate(image):
    fam = b"6slhdsa5shake"

    def profile(n):
        suffix = f"Kj{n:x}_EB6_".encode()

        def address(stem):
            return image.function(fam + stem + suffix, fam)[0]

        body, words = image.function(fam + b"3slh19slh_verify_internal" + suffix, fam)
        ht, htwords = (
            image.function(fam + b"2ht9ht_verify" + suffix, fam) if n != 16 else (0, [])
        )
        calls = [
            address(b"4hash5h_msg"),
            image.function(b"6slhdsa4util7base_2b", b"6slhdsa")[0],
            address(b"10fors_batch7recover"),
            address(b"4xmss16xmss_pk_from_sig"),
            image.function(b"___rust_dealloc", b"___rustc")[0],
            ht,
        ]
        return body, words, calls, htwords

    lines = [
        "import Spec.ArmVerifyBody",
        "import Spec.AppleVerifyLengthWitness",
        "namespace LinkedAppleVerifyBody",
        "open Spec.ArmVerifyBody LinkedAppleVerifyLength",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
    ]

    def array(name, ws):
        return (
            f"def {name} : Array Nat := #["
            + ",\n".join(
                ",".join(hex(w) for w in ws[i : i + 8]) for i in range(0, len(ws), 8)
            )
            + "]"
        )

    for n in (16, 24, 32):
        body, words, calls, htwords = profile(n)
        lines.extend([array(f"words{n}", words), array(f"htWords{n}", htwords)])
        for v in "sf":
            label = f"shake_{8 * n}{v}"
            lines += [
                f"def {label}_image : Image := ⟨Spec.{label},{label}_path,{label}_toHash,0x{body:x},words{n},"
                + ",".join(hex(a) for a in calls)
                + f",htWords{n}⟩",
                f"theorem {label}_checked : run {label}_image = some (expected Spec.{label}) := by decide +kernel",
                f"def {label}_trace {{msg sig pk events}} (h : run {label}_image = some events)",
                f"    (v : Callees Spec.{label} msg sig pk) := trace h {label}_checked (by decide) v",
                f"theorem {label}_eq {{msg sig pk events}} (h : run {label}_image = some events)",
                f"    (v : Callees Spec.{label} msg sig pk) : returned v events = Spec.slhVerifyInternal Spec.{label} msg sig pk :=",
                f"  ({label}_trace h v).eq_spec",
            ]
    for name, i, new in [
        ("badDigestShift", 61, 0xAA0B20CB),
        ("wrongFORSInput", 109, 0x91008323),
        ("wrongLayerSlice", 145, 0x8B1B02C2),
        ("wrongVerdict", 164, 0xEB09013F),
    ]:
        lines += [
            f"theorem {name} : run {{shake_128s_image with words := words16.set! {i} 0x{new:08x}}} ≠",
            "    some (expected Spec.shake_128s) := by decide +kernel",
        ]
    for label, width, i, wrong in [
        ("wrongWideSibling", 24, 40, 0x8B1802E2),
        ("wrongWideComparison", 32, 58, 0xEB08011F),
    ]:
        profileName = f"shake_{8 * width}s"
        lines.extend(
            [
                f"theorem {label} : run {{{profileName}_image with htWords := htWords{width}.set! {i} 0x{wrong:08x}}} ≠",
                f"    some (expected Spec.{profileName}) := by decide +kernel",
            ]
        )
    return "\n".join(lines + ["end LinkedAppleVerifyBody", ""])


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("binary", type=Path)
    sys.stdout.write(certificate(Image(p.parse_args().binary.read_bytes())))
