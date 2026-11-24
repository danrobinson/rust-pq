"""Extract the twelve linked SHA-2 public verification wrappers and segmented callees."""

import argparse
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from image import Image


def array(name, words):
    return (
        f"def {name} : Array Nat := #["
        + ",\n".join(
            ",".join(hex(w) for w in words[i : i + 8]) for i in range(0, len(words), 8)
        )
        + "]"
    )


def certificate(image):
    lines = [
        "import Spec.ArmSha2PublicVerify",
        "import Spec.AppleSha2VerifyWitness",
        "namespace LinkedAppleSha2PublicVerify",
        "open Spec.ArmSha2PublicVerify",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
    ]
    entries = []
    for n in (16, 24, 32):
        mid, mwords = image.function(
            f"6slhdsa3slh10slh_verifyKj{n:x}_EB4_".encode(), b"6slhdsa"
        )
        seg, swords = image.function(
            f"6slhdsa3slh7message6verifyKj{n:x}_EB6_".encode(), b"6slhdsa"
        )
        digest, _ = image.function(
            f"6slhdsa3slh7message6digestKj{n:x}_EB6_".encode(), b"6slhdsa"
        )
        lines.extend([array(f"dispatcher{n}", mwords), array(f"segmented{n}", swords)])
        for v in "sf":
            label = f"sha2_{8 * n}{v}"
            for suffix in ("verify", "slh_verify"):
                entry, words = image.function(
                    f"{len(label)}{label}{len(suffix)}{suffix}".encode(),
                    b"6slhdsa4sets",
                )
                name = f"{label}_{suffix}"
                lines.append(array(name + "Words", words))
                lines.append(
                    f"def {name} : Image := ⟨LinkedAppleSha2VerifyBody.{label}_image,0x{entry:x},{name}Words,0x{mid:x},dispatcher{n},0x{seg:x},segmented{n},0x{digest:x}⟩"
                )
                entries.append((name, label))
    for name, label in entries:
        lines.extend(
            [
                f"theorem {name}_paths (c m s : Bool) : run {name} c m s = some (route c m s) := by",
                "  cases c <;> cases m <;> cases s <;> decide +kernel",
            ]
        )
        lines.extend(
            [
                f"theorem {name}_eq {{msg ctx sig pk : Spec.Bytes}} {{choices : Fin 8}}",
                f"    (v : Spec.ArmSha2Verify.Callees Spec.{label} (input msg ctx choices) sig pk) :",
                f"    verified (a := {name}) (choices := choices) (msg := msg) (ctx := ctx) v = some (Spec.slhVerify Spec.{label} msg sig ctx pk) :=",
                f"  valid_eq {name}_paths LinkedAppleSha2VerifyBody.{label}_checked (by decide) v",
                f"theorem {name}_malformed (msg ctx sig pk : Spec.Bytes) (h : sig.length ≠ Spec.{label}.sigBytes) (core : Bool) :",
                f"    (evaluate {name} msg ctx sig).map (fun r => verdictOf r core) = some (Spec.slhVerify Spec.{label} msg sig ctx pk) :=",
                f"  malformed_eq {name}_paths msg ctx sig pk h core",
                f"theorem {name}_contextRejected (msg ctx sig : Spec.Bytes) (h : ctx.length > 255) : evaluate {name} msg ctx sig = some .contextRejected :=",
                f"  oversized_ctx {name}_paths msg ctx sig h",
            ]
        )
    for tag, field, words, i, mask, small, result in [
        ("contextBound", "dispatchWords", "dispatcher16", 6, 1024, "true", "framed"),
        ("messageBound", "dispatchWords", "dispatcher16", 13, 1024, "true", "framed"),
        (
            "framedSignature",
            "dispatchWords",
            "dispatcher16",
            37,
            1 << 16,
            "true",
            "framed",
        ),
        (
            "segmentedCtx",
            "segmentedWords",
            "segmented16",
            28,
            1 << 16,
            "false",
            "segmented",
        ),
        (
            "segmentedSeed",
            "segmentedWords",
            "segmented16",
            118,
            4096,
            "false",
            "segmented",
        ),
        (
            "rootCompare",
            "segmentedWords",
            "segmented16",
            208,
            1 << 16,
            "false",
            "segmented",
        ),
    ]:
        lines.append(
            f"theorem {tag}_mutation : run {{ sha2_128s_verify with {field} := {words}.set! {i} ({words}[{i}]! ^^^ {mask}) }} true {small} true ≠ some .{result} := by decide +kernel"
        )
    lines.extend(f"#print axioms sha2_{w}s_verify_eq" for w in (128, 192, 256))
    return "\n".join(lines + ["end LinkedAppleSha2PublicVerify", ""])


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("executable", type=Path)
    print(certificate(Image(p.parse_args().executable.read_bytes())), end="")
