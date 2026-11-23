"""Extract candidate public rejection paths. Lean independently checks every instruction and PC."""

from image import require, sign_extend


def word(image, pc):
    return int.from_bytes(image.read(b"__text", pc, 4), "little")


def branch(pc, w):
    return pc + 4 * sign_extend(w & 0x3FFFFFF, 26)


def candidate(image, entry):
    pc, links, path = entry, [], []
    for _ in range(64):
        w = word(image, pc)
        path.append((pc, w))
        if w == 0xD65F03C0:
            if not links:
                return path
            pc = links.pop()
        elif w >> 26 in (5, 37):
            if w >> 26 == 37:
                links.append(pc + 4)
            pc = branch(pc, w)
        else:
            pc += 4
    raise ValueError("unterminated public rejection path")


def unwrap_abi(image):
    """Match a real Option<Vec<u8>>::unwrap use of the indirect return slot.

    ADD X8,SP,#slot; ...; BL public_sign; LDR Xi,[SP,#slot]; CMN Xi,#1;
    B.EQ handler; the failure handler calls core::option::unwrap_failed.
    Accept only register-immediate MOVZ or nonflag-setting ADD before BL.
    """
    suffix = b"10shake_128f8slh_sign"
    entry, _ = image.function(suffix, b"6slhdsa4sets")
    caller = next(
        n
        for n, _ in image.symbols
        if b"acvp_shake_128f20roundtrip_and_tamper" in n and b"call_once" in n
    )
    start, words = image.function(caller, b"4acvp")
    fail, _ = image.function(b"6option13unwrap_failed", b"4core")
    for i in range(4, len(words) - 3):
        pc, w = start + 4 * i, words[i]
        if w >> 26 != 37 or branch(pc, w) != entry:
            continue
        setup = words[i - 4]
        if setup & 0xFFC003FF != 0x910003E8:
            continue
        if not all(
            v & 31 != 8 and v & 0xFFC00000 in (0x91000000, 0x52800000) and v & 31 != 31
            for v in words[i - 3 : i]
        ):
            continue
        load, cmn, beq = words[i + 1 : i + 4]
        if load & 0xFFC003E0 != 0xF94003E0 or (load >> 10 & 4095) * 8 != (
            setup >> 10 & 4095
        ):
            continue
        if cmn != 0xB100041F | ((load & 31) << 5) or beq & 0xFF00001F != 0x54000000:
            continue
        dst = pc + 12 + 4 * sign_extend((beq >> 5) & 0x7FFFF, 19)
        a, b, c = (word(image, dst + 4 * j) for j in range(3))
        if (
            a & 0x9F00001F == 0x90000000
            and b & 0xFFC003FF == 0x91000000
            and c >> 26 == 37
            and branch(dst + 8, c) == fail
        ):
            return
    raise ValueError("missing linked None discriminator to core::option::unwrap_failed")


def certificate(image):
    unwrap_abi(image)
    lines = [
        "import Spec.ArmSignReject",
        "namespace LinkedReject",
        "open Spec.ArmSignReject",
        "set_option maxRecDepth 32768",
        "set_option maxHeartbeats 0",
    ]
    claims = []

    def emit(name, entry, n, det, path, value):
        literal = "[" + ",\n ".join(f"(0x{pc:x},0x{w:08x})" for pc, w in path) + "]"
        lines.append(f"private def {name} : List (Nat × Nat) := {literal}")
        args = f"0x{entry:x} {n} {str(det).lower()} {name}"
        if value:
            claims.append(
                f"theorem {name}_returns_none : ReturnsNone {args} := returnsNone_of_checks (by decide)"
            )
        else:
            claims.append(
                f"theorem {name}_rejected : checks {args} = false := by decide"
            )

    for family in ("sha2", "shake"):
        for n in (16, 24, 32):
            for variant in ("s", "f"):
                label = f"{family}_{8 * n}{variant}"
                for op in ("sign", "slh_sign", "sign_deterministic"):
                    suffix = f"{len(label)}{label}{len(op)}{op}".encode()
                    entry, _ = image.function(suffix, b"6slhdsa4sets")
                    path = candidate(image, entry)
                    emit(
                        f"{label}_{op}",
                        entry,
                        n,
                        op == "sign_deterministic",
                        path,
                        True,
                    )
                    if label == "shake_128f" and op == "sign_deterministic":
                        controls = [
                            ("threshold", 0xF103FC7F, 1 << 10),  # 255 -> 254
                            ("wrongResultSlot", 0xF9000288, 1 << 10),
                            ("wrongSavedPair", 0xA9467BFD, 1 << 10),
                            ("wrongKeyRead", 0x3DC00880, 1 << 10),
                        ]
                        for name, original, bit in controls:
                            require(
                                sum(w == original for _, w in path) == 1,
                                "missing rejection control",
                            )
                            emit(
                                name,
                                entry,
                                n,
                                True,
                                [
                                    (pc, w ^ bit if w == original else w)
                                    for pc, w in path
                                ],
                                False,
                            )
    lines.extend(claims)
    lines.append("end LinkedReject")
    return "\n".join(lines) + "\n"
