"""Extract the linked SHAKE verifier rejection paths and first H_msg calls for Lean replay."""

import argparse
import hashlib
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image, require, sign_extend


def literal(items):
    return "[" + ", ".join(f"(0x{pc:x},0x{w:08x})" for pc, w in items) + "]"


def negative(name, label, good, title, field):
    return [
        f"theorem {title} : inspect {{ {name} with {field} }} ≠",
        f"    some ⟨Spec.{label}.sigBytes,0x{good:x},false⟩ := by decide",
    ]


def certificate(image):
    lines = [
        "import Spec.ArmVerifyLength",
        "namespace LinkedAppleVerifyLength",
        "open Spec.ArmVerifyLength",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    for n in (16, 24, 32):
        inner, ops = image.function(
            f"6slhdsa5shake3slh19slh_verify_internalKj{n:x}_EB6_".encode(), b"6slhdsa"
        )
        end = next(j for j, w in enumerate(ops) if w & 0xFF00001F == 0x54000001)
        compare = inner + 4 * (end - 1)
        branch = compare + 4
        good = branch + 4
        target = end + sign_extend((ops[end] >> 5) & 0x7FFFF, 19)
        require(0 <= target < len(ops), "branch outside verifier")
        ret = next(j for j in range(target, len(ops)) if ops[j] == 0xD65F03C0)
        prefix = [(inner + 4 * i, ops[i]) for i in range(end - 1)]
        reject = [(inner + 4 * j, ops[j]) for j in range(target, ret + 1)]
        hash_entry, _ = image.function(
            f"6slhdsa5shake4hash5h_msgKj{n:x}_EB6_".encode(), b"6slhdsa5shake"
        )
        bl = next(i for i in range(end + 1, len(ops)) if ops[i] >> 26 == 37)
        good_path = [(inner + 4 * j, ops[j]) for j in range(end + 1, bl + 1)]
        for v in "sf":
            label = f"shake_{8 * n}{v}"
            entry, wrapper = image.function(
                f"{len(label)}{label}19slh_verify_internal".encode(), b"6slhdsa4sets"
            )
            pages = [
                (i, sign_extend(((w >> 5 & 0x7FFFF) << 2) | (w >> 29 & 3), 21))
                for i, w in enumerate(wrapper)
                if w & 0x9F00001F == 0x90000000
            ]
            ((i, displacement),) = pages
            w = wrapper[i + 1]
            require(w & 0xFFC003FF == 0x91000000, "missing parameter address")
            param = ((entry + 4 * i) & ~4095) + 4096 * displacement + (w >> 10 & 4095)
            data = list(image.read(b"__const", param, 36))
            before = [(entry + 4 * j, w) for j, w in enumerate(wrapper)] + prefix
            name = label + "_path"
            lines += [
                f"def {name} : Path := ⟨0x{entry:x}, 0x{param:x}, {data},",
                f"  {literal(before)},",
                f"  (0x{compare:x},0x{ops[end - 1]:08x}), (0x{branch:x},0x{ops[end]:08x}),",
                f"  {literal(reject)}⟩",
                f"theorem {label}_params : {name}.params = Spec.ArmKeygen.parameterBytes Spec.{label} := by decide",
                f"theorem {label}_checked : inspect {name} = some ⟨Spec.{label}.sigBytes,0x{good:x},false⟩ := by decide",
                f"theorem {label}_validEdge : execute {name} Spec.{label}.sigBytes = some (.continued 0x{good:x}) :=",
                f"  acceptedEdge {label}_checked (by decide)",
                f"def {label}_trace (msg sig pk : Spec.Bytes) (value : Bool)",
                f"    (actual : execute {name} sig.length = some (.returned value)) :",
                f"    LinkedArm.Signer.VerifyTrace Spec.{label} msg sig pk value :=",
                f"  toVerifyTrace {label}_checked msg sig pk value actual",
                f"def {label}_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64)",
                f"    (bad : sig.length ≠ Spec.{label}.sigBytes) :",
                f"    LinkedArm.Signer.VerifyTrace Spec.{label} msg sig pk false :=",
                f"  {label}_trace msg sig pk false (rejects {label}_checked sig fits bad)",
                "",
            ]
            lines.extend(
                [
                    f"def {label}_toHash : List (Nat × Nat) := {literal(good_path)}",
                    f"theorem {label}_hashCall : hashCall {name} Spec.{label}.n Spec.{label}.sigBytes",
                    f"    0x{hash_entry:x} {label}_toHash = some (expectedCall Spec.{label}.n) := by decide",
                    f"theorem {label}_digestPremise {{call}}",
                    f"    (actual : hashCall {name} Spec.{label}.n Spec.{label}.sigBytes 0x{hash_entry:x} {label}_toHash = some call)",
                    f"    (msg sig pk digest : Spec.Bytes) (sigSize : Spec.{label}.n ≤ sig.length)",
                    f"    (pkSize : 2 * Spec.{label}.n ≤ pk.length)",
                    f"    (target : let v := Spec.ArmKeygen.interpret (hashSources Spec.{label} sig pk)",
                    "      digest = Spec.Hmsg Spec."
                    + label
                    + " (Spec.ArmKeygen.bytes v call.randomizer)",
                    "        (Spec.ArmKeygen.bytes v call.publicSeed) (Spec.ArmKeygen.bytes v call.publicRoot) msg) :",
                    f"    digest = Spec.Hmsg Spec.{label} (sig.take Spec.{label}.n)",
                    f"      (Spec.block Spec.{label} pk 0) (Spec.block Spec.{label} pk 1) msg :=",
                    f"  digestPremise {label}_hashCall actual msg sig pk digest sigSize pkSize (by decide) (by decide) target",
                    "",
                ]
            )
            if label == "shake_128s":
                # Mutate the actual ADD X1,SP,#offset that supplies the randomizer.
                # Different register allocations can move its stack slot.
                (hash_argument,) = [w for _, w in good_path if w & 0xFFC003FF == 0x910003E1]
                require((hash_argument >> 10 & 4095) >= 32, "unexpected H_msg stack argument")
                fields = [
                    (
                        "wrongLengthSource",
                        f"before := {name}.before.map (fun (pc,w) => (pc,if pc = 0x{entry + 4:x} then 0xaa0203e4 else w))",
                    ),
                    (
                        "wrongSizeArithmetic",
                        f"before := {name}.before.map (fun (pc,w) => (pc,if w = 0x91000d17 then 0x91001117 else w))",
                    ),
                    ("reversedGuard", f"branch := (0x{branch:x},0x{ops[end] ^ 1:08x})"),
                    (
                        "acceptsMalformed",
                        f"reject := {name}.reject.map (fun (pc,w) => (pc,if w = 0x52800000 then 0x52800020 else w))",
                    ),
                ]
                for title, field in fields:
                    lines.extend(negative(name, label, good, title, field))
                lines.extend(
                    [
                        f"theorem wrongHashArgument : hashCall {name} 16 Spec.{label}.sigBytes 0x{hash_entry:x}",
                        f"    ({label}_toHash.map (fun (pc,w) => (pc,if w == 0x{hash_argument:08x} then 0x{hash_argument - (32 << 10):08x} else w)))",
                        "    ≠ some (expectedCall 16) := by decide",
                        f"theorem wrongHashTarget : hashCall {name} 16 Spec.{label}.sigBytes 0x{hash_entry:x}",
                        f"    ({label}_toHash.map (fun (pc,w) => (pc,if pc = 0x{inner + 4 * bl:x} then 0x{ops[bl] ^ 1:08x} else w)))",
                        "    ≠ some (expectedCall 16) := by decide",
                    ]
                )
    return "\n".join(lines + ["end LinkedAppleVerifyLength", ""])


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("binary", type=Path)
    args = p.parse_args()
    sys.stdout.write(certificate(Image(args.binary.read_bytes())))
