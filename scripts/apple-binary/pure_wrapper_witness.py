"""Extract the public SHAKE pure wrappers for kernel replay against the internal images."""

import argparse
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image


def certificate(image):
    free = image.function(b"___rust_dealloc", b"___rustc")[0]
    lines = [
        "import Spec.ArmPureWrapper",
        "import Spec.AppleVerifyBodyWitness",
        "import Spec.AppleInternalSignerWitness",
        "namespace LinkedApplePure",
        "open Spec.ArmPureWrapper",
        "set_option maxHeartbeats 0",
        "set_option maxRecDepth 65536",
    ]
    for width in (128, 192, 256):
        for variant in "sf":
            profile = f"shake_{width}{variant}"
            for suffix, mode in [
                (b"6verify", "verify"),
                (b"10slh_verify", "verify"),
                (b"4sign", "sign"),
                (b"8slh_sign", "sign"),
                (b"18sign_deterministic", "deterministic"),
            ]:
                start, words = image.function(
                    suffix, b"6slhdsa4sets10" + profile.encode()
                )
                name = profile + "_" + suffix.decode().lstrip("0123456789")
                internal = (
                    f"LinkedAppleVerifyBody.{profile}_image"
                    if mode == "verify"
                    else f"LinkedInternalSigner.{profile}"
                )
                par = internal + (".gate" if mode == "verify" else ".cfg") + ".param"
                lines += [
                    f"def {name} : Image := ⟨.{mode},Spec.{profile}.n,{par},0x{start:x},#[",
                    ",\n".join(
                        ",".join(hex(w) for w in words[i : i + 8])
                        for i in range(0, len(words), 8)
                    ),
                    f"],LinkedApplePureFrame.image.entry,{internal}.body,0x{free:x}⟩",
                    f"theorem {name}_valid : run {name} true = some .forwarded := by decide +kernel",
                    f"theorem {name}_long : run {name} false = some .rejected := by decide +kernel",
                ]
                if mode == "verify":
                    lines += [
                        f"theorem {name}_eq {{msg ctx sig pk out r}} (f : Frame msg ctx)",
                        f"    (pub : execute {name} ctx = some r)",
                        f"    (core : Spec.ArmVerifyBody.run {internal} = some out)",
                        f"    (v : Spec.ArmVerifyBody.Callees Spec.{profile} f.payload sig pk) :",
                        f"    verifyReturn r (Spec.ArmVerifyBody.returned v out) = Spec.slhVerify Spec.{profile} msg sig ctx pk :=",
                        f"  verify_eq {name}_valid {name}_long pub (fun _ =>",
                        f"    (LinkedAppleVerifyBody.{profile}_eq core v).trans",
                        f"      (congrArg (fun m => Spec.slhVerifyInternal Spec.{profile} m sig pk) f.payload_eq))",
                        f"theorem {name}_malformed {{msg ctx sig pk r}} (pub : execute {name} ctx = some r)",
                        f"    (fits : sig.length < 2^64) (bad : sig.length ≠ Spec.{profile}.sigBytes) :",
                        f"    verifyReturn r false = Spec.slhVerify Spec.{profile} msg sig ctx pk :=",
                        f"  verify_eq {name}_valid {name}_long pub (fun _ =>",
                        f"    (LinkedAppleVerifyLength.{profile}_malformed _ _ _ fits bad).eq_spec)",
                    ]
                else:
                    random = (
                        "(Spec.block Spec." + profile + " key 2)"
                        if mode == "deterministic"
                        else "rand"
                    )
                    args = (
                        "msg ctx key out r"
                        if mode == "deterministic"
                        else "msg ctx key rand out r"
                    )
                    lines += [
                        f"theorem {name}_eq {{{args}}} (f : Frame msg ctx) (profile : Fin 4)",
                        f"    (pub : execute {name} ctx = some r)",
                        f"    (core : Spec.ArmInternalSigner.run {internal} profile = some out)",
                        f"    (v : Spec.ArmInternalSigner.Callees Spec.{profile} f.payload key {random}) :",
                        f"    signReturn r (Spec.ArmInternalSigner.materialize v out) = Spec.slhSign Spec.{profile} msg ctx key {random} :=",
                        f"  sign_eq {name}_valid {name}_long pub (fun _ =>",
                        f"    (LinkedInternalSigner.{profile}_eq profile core v).trans",
                        f"      (congrArg (fun m => Spec.slhSignInternal Spec.{profile} m key {random}) f.payload_eq))",
                    ]
    for tag, op, i, x in [
        ("wrongContext", "verify", 14, 0xAA0403E3),
        ("wrongVerdict", "verify", 31, 0xAA1303E0),
        ("wrongSeed", "sign_deterministic", 6, 0x3DC00480),
        ("wrongResult", "sign", 26, 0xF94013E8),
        ("wrongCutoff", "slh_verify", 5, 0xF103F8BF),
    ]:
        a = "shake_128s_" + op
        lines += [
            f"theorem {tag} : run {{{a} with words := {a}.words.set! {i} {hex(x)}}} true ≠",
            "    some .forwarded := by decide +kernel",
        ]
    return "\n".join(
        lines
        + [
            "#print axioms shake_128s_verify_eq",
            "#print axioms shake_256f_sign_deterministic_eq",
            "end LinkedApplePure",
            "",
        ]
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    print(certificate(Image(parser.parse_args().binary.read_bytes())), end="")
