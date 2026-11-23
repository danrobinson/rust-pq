"""Regenerate the linked Apple SHA-2 internal verifier's Lean replay witnesses."""

import argparse
import hashlib
from pathlib import Path
import struct
import sys

sys.dont_write_bytecode = True
from image import Image, require, sign_extend
from verify_length_witness import literal


def gate(image):
    lines = [
        "import Spec.ArmVerifyLength",
        "namespace LinkedAppleSha2VerifyLength",
        "open Spec.ArmVerifyLength",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    for n in (16, 24, 32):
        suffix = f"Kj{n:x}_EB4_".encode()
        inner, words = image.function(
            b"6slhdsa3slh19slh_verify_internal" + suffix, b"6slhdsa"
        )
        hmsg, _ = image.function(b"6slhdsa4hash5h_msg" + suffix, b"6slhdsa")
        j = next(i for i, w in enumerate(words) if w & 0xFF00001F == 0x54000001)
        bl = next(i for i in range(j + 1, len(words)) if words[i] >> 26 == 37)
        common = [(inner + 4 * i, words[i]) for i in range(j - 1)]
        good = [(inner + 4 * i, words[i]) for i in range(j + 1, bl + 1)]
        i = j + sign_extend((words[j] >> 5) & 0x7FFFF, 19)
        reject = []
        for _ in range(30):
            require(0 <= i < len(words), "rejection word outside routine")
            w = words[i]
            reject.append((inner + 4 * i, w))
            if w == 0xD65F03C0:
                break
            i += sign_extend(w & 0x3FFFFFF, 26) if w >> 26 == 5 else 1
        else:
            raise ValueError("unterminated rejection")
        for v in "sf":
            label = f"sha2_{8 * n}{v}"
            entry, wrapper = image.function(
                f"{len(label)}{label}19slh_verify_internal".encode(), b"6slhdsa4sets"
            )
            (i,) = [t for t, w in enumerate(wrapper) if w & 0x9F00001F == 0x90000000]
            w = wrapper[i]
            page = ((entry + i * 4) & ~4095) + 4096 * sign_extend(
                ((w >> 5 & 0x7FFFF) << 2) | (w >> 29 & 3), 21
            )
            w = wrapper[i + 1]
            require(w & 0xFFC003FF == 0x91000000, "parameter load")
            param = page + (w >> 10 & 4095)
            name = label + "_path"
            pre = [(entry + 4 * i, w) for i, w in enumerate(wrapper)] + common
            lines += [
                f"def {name} : Path := ⟨{entry},{param},{list(image.read(b'__const', param, 36))},",
                f"  {literal(pre)},(0x{inner + 4 * (j - 1):x},0x{words[j - 1]:08x}),",
                f"  (0x{inner + 4 * j:x},0x{words[j]:08x}),{literal(reject)}⟩",
                f"def {label}_toHash := {literal(good)}".replace(
                    " :=", " : List (Nat × Nat) :=", 1
                ),
                f"theorem {label}_parameters : {name}.params = Spec.ArmKeygen.parameterBytes Spec.{label} := by decide",
                f"theorem {label}_guard : inspect {name} = some ⟨Spec.{label}.sigBytes,{good[0][0]},false⟩ := by decide",
                f"def {label}_malformed (msg sig pk : Spec.Bytes) (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.{label}.sigBytes) :",
                f"    LinkedArm.Signer.VerifyTrace Spec.{label} msg sig pk false :=",
                f"  toVerifyTrace {label}_guard _ _ _ _ (rejects {label}_guard sig fits bad)",
                f"theorem {label}_hashCall : hashCall {name} {n} Spec.{label}.sigBytes 0x{hmsg:x} {label}_toHash = some (expectedCall {n}) := by decide",
            ]
    return "\n".join(lines + ["end LinkedAppleSha2VerifyLength", ""])


def body(image):
    lines = [
        "import Spec.ArmSha2Verify",
        "import Spec.AppleSha2VerifyLengthWitness",
        "namespace LinkedAppleSha2VerifyBody",
        "open Spec.ArmSha2Verify LinkedAppleSha2VerifyLength",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    pc, words = image.function(b"6slhdsa3slh19slh_verify_internalKj10_EB4_", b"6slhdsa")

    def fn(stem):
        return image.function(b"6slhdsa" + stem + b"Kj10_EB4_", b"6slhdsa")[0]

    free = image.function(b"___rust_dealloc", b"___rustc")[0]
    calls = [
        fn(b"4hash5h_msg"),
        0,
        fn(b"4fors16fors_pk_from_sig"),
        fn(b"4xmss16xmss_pk_from_sig"),
        free,
    ]

    def literals(address, count):
        for section, (va, sz, o) in image.sections.items():
            if va <= address <= va + sz - 4 * count:
                return list(
                    struct.unpack(
                        "<" + "I" * count, image.read(section, address, 4 * count)
                    )
                )
        raise ValueError("missing constants")

    lines += [
        "def words : Array Nat := #["
        + ",\n".join(
            ",".join(hex(x) for x in words[j : j + 8]) for j in range(0, len(words), 8)
        )
        + "]"
    ]
    for v in "sf":
        label = f"sha2_128{v}"
        lines += [
            f"def {label}_image : Image := ⟨⟨Spec.{label},{label}_path,{label}_toHash,0x{pc:x},words,"
            + ",".join(hex(a) for a in calls)
            + f",0,#[]⟩,0x{pc + 4 * 92:x},{literals(0x1000D5F30, 8)},{literals(0x1000DC470, 64)}⟩",
            f"theorem {label}_checked : run {label}_image = some (expected Spec.{label}) := by decide +kernel",
            f"def {label}_trace {{msg sig pk events}} (actual : run {label}_image = some events)",
            f"    (v : Callees Spec.{label} msg sig pk) := trace actual {label}_checked (by decide) v",
            f"theorem {label}_eq {{msg sig pk events}} (actual : run {label}_image = some events)",
            f"    (v : Callees Spec.{label} msg sig pk) : returned v events = Spec.slhVerifyInternal Spec.{label} msg sig pk :=",
            f"  ({label}_trace actual v).eq_spec",
        ]
    for name, j, mask in [
        ("wrongSeedRound", 107, 0x1000),
        ("wrongForestInput", 150, 0x400),
        ("wrongLayerSlice", 175, 0x10000),
        ("wrongRoot", 195, 0x10000),
    ]:
        lines += [
            f"theorem {name} : run {{sha2_128s_image with core := {{sha2_128s_image.core with words := words.set! {j} 0x{words[j] ^ mask:08x}}}}} ≠",
            "    some (expected Spec.sha2_128s) := by decide +kernel",
        ]
    return "\n".join(lines + ["end LinkedAppleSha2VerifyBody", ""])


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("executable", type=Path)
    p.add_argument("--body", action="store_true")
    a = p.parse_args()
    print((body if a.body else gate)(Image(a.executable.read_bytes())), end="")
