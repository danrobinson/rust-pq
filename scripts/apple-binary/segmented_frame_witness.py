"""Certify the linked Apple long-message SHA-2 signing driver and its frame windows."""

import argparse
import hashlib
import struct
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image, require, sign_extend
from pure_sign import memcpy_address, symbol


def certificate(image, snapshot):
    lines = [
        "import Spec.ArmSegmentedSigner",
        "namespace LinkedSegmentedFrame",
        "open Spec.ArmSegmentedFrame",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    memcpy = memcpy_address(image, snapshot)
    for n in (16, 24, 32):
        pc, words = image.function(
            f"3slh7message4signKj{n:x}_EB6_".encode(), b"6slhdsa"
        )
        digest, _ = image.function(
            f"3slh7message6digestKj{n:x}_EB6_".encode(), b"6slhdsa"
        )
        size = 256 if n == 16 else 512
        cont, _ = image.function(
            f"3slh7message9continuedKj{size // 4:x}_NtB2_6Sha{size}EB6_".encode(),
            b"6slhdsa",
        )
        indices = []
        for target in (memcpy, cont, digest):
            hits = [
                i
                for i, w in enumerate(words)
                if w >> 26 == 0x25
                and pc + 4 * i + 4 * sign_extend(w % 2**26, 26) == target
            ]
            require(
                hits and (len(hits) == 1 or target == memcpy), "missing segment call"
            )
            indices.append(hits[0])
        copy, inner, hm = indices
        # All three windows use the same inner and digest ABI instruction counts.
        require(copy < inner - 7 < inner < hm - 9 < hm, "unexpected segmentation")
        lines.append(
            f"def words{n} : Array Nat := #["
            + ",\n ".join(
                ", ".join(f"0x{w:08x}" for w in words[i : i + 8])
                for i in range(0, len(words), 8)
            )
            + "]"
        )
        suffix = f"Kj{n:x}_EB4_".encode()
        hooks = {
            "copy": memcpy,
            "free": symbol(image, b"___rust_dealloc", b"___rust_dealloc"),
            "reserve": symbol(
                image, b"11RawVecInnerpE7reserve21do_reserve_and_handle", b"6slhdsa"
            ),
        }
        for op, tag in (
            ("fors", b"4fors9fors_sign"),
            ("recover", b"4fors16fors_pk_from_sig"),
            ("ht", b"2ht7ht_sign"),
        ):
            hooks[op] = image.function(tag + suffix, b"6slhdsa")[0]
        if n == 16:
            j = words.index(0x6E200800, hm)
            end = words.index(0x6F00E402, j)
            iv = list(struct.unpack("<8I", image.read(b"__const", 0x1000D5F30, 32)))
            ks = list(struct.unpack("<64I", image.read(b"__const", 0x1000DC470, 256)))
            seed = f".inlined 0x{pc + 4 * j:x} {list(words[j:end])} {iv} {ks}"
        else:
            hooks["seed"] = image.function(b"4hash8seed_ctx" + suffix, b"6slhdsa")[0]
            seed = f".external 0x{hooks['seed']:x}"
        (cr,) = [pc + 4 * i for i, w in enumerate(words) if w == 0x1B092969]
        require(len(hooks) == len(set(hooks.values())), "ambiguous tail hook")
        hook_list = (
            "[" + ",".join(f"(0x{addr:x},.{op})" for op, addr in hooks.items()) + "]"
        )
        fmt = "I" if n == 16 else "Q"
        width = struct.calcsize(fmt)

        def const(addr, count):
            return list(
                struct.unpack(
                    "<" + str(count) + fmt, image.read(b"__const", addr, count * width)
                )
            )

        iv0 = const(0x1000D5F30 if n == 16 else 0x1000D5220, 8)
        k0 = const(0x1000DCAF0 if n == 16 else 0x1000DCBF0, 64 if n == 16 else 80)
        pad = const(0x1000D5F60 if n == 16 else 0x1000D5F80, 8 if n == 16 else 4)
        lines.append(
            f"def literals{n} : Spec.ArmSegmentedSigner.Literals := ⟨{iv0},{k0},{pad}⟩"
        )
        for variant in "sf":
            name = f"sha2_{8 * n}{variant}"
            stub, code = image.function(
                f"{len(name)}{name}17slh_sign_internal".encode(), b"6slhdsa4sets"
            )
            (j,) = [j for j, w in enumerate(code) if w & 0x9F00001F == 0x90000000]
            w = code[j]
            require(
                code[j + 1] & 0xFFC003FF == 0x91000000, "unexpected parameter pointer"
            )
            record = (
                ((stub + 4 * j) & ~4095)
                + 4096 * sign_extend((w >> 5 & 0x7FFFF) * 4 + (w >> 29 & 3), 21)
                + (code[j + 1] >> 10 & 4095)
            )
            raw = list(image.read(b"__const", record, 36))
            lines += [
                f"def {name} : Image := ⟨Spec.{name},0x{record:x},{raw},0x{pc:x},0x{memcpy:x},"
                f"0x{cont:x},0x{digest:x},words{n},{copy},{inner - 7},{inner},{hm - 9},{hm}⟩",
                f"theorem {name}_checked : checked {name} = some expected := by decide +kernel",
            ]
            lines += [
                f"def full_{name} : Spec.ArmSegmentedSigner.Image := ⟨{name},{hook_list},0x{cr:x},{seed},literals{n}⟩",
                f"theorem full_{name}_checked (i : Fin 4) : Spec.ArmSegmentedSigner.run full_{name} i = "
                "some Spec.ArmSegmentedSigner.expected := by fin_cases i <;> decide +kernel",
            ]
            if variant == "s":
                controls = {
                    16: [(0x390343FF, 0x390343F4), (0x91004A84, 0x91004684)],
                    24: [(0x3904E7F5, 0x3904E7FF), (0xF94037E5, 0xF9403BE5)],
                    32: [(0x91018304, 0x91010304), (0xF90003F9, 0xF90003F7)],
                }[n]
                full_controls = {
                    16: [(61, 0x4F01E6C1), (286, 0x5E282822 ^ 32)],
                    24: [(331, 0xA9102BF8), (379, 0xF94067EA), (430, 0x9101C3FF)],
                    32: [(269, 0xAA1803E5), (390, 0xF9000528)],
                }[n]
                for index, wrong in full_controls:
                    require(words[index] != wrong, "unchanged segmented mutation")
                    lines.append(
                        f"theorem reject_tail_{n}_{index} : Spec.ArmSegmentedSigner.run "
                        f"{{ full_{name} with frame := {{ {name} with words := words{n}.set! {index} 0x{wrong:08x} }} }} 0 "
                        " = none := by decide +kernel"
                    )
                for old, new in controls:
                    (j,) = [j for j, w in enumerate(words) if w == old]
                    lines.append(
                        f"theorem reject_{n}_{j} : checked {{ {name} with words := words{n}.set! "
                        f"{j} 0x{new:08x} }} = none := by decide +kernel"
                    )
    lines.extend(
        [
            "theorem reject_wide_padding : Spec.ArmSegmentedSigner.pinned sha2_256s "
            "{ literals32 with padding := [2^63,0,0,768] } = false := by decide +kernel",
            "theorem reject_narrow_round_table : Spec.ArmSegmentedSigner.pinned sha2_128s "
            "{ literals16 with k := literals16.k.reverse } = false := by decide +kernel",
        ]
    )
    return "\n".join(lines + ["end LinkedSegmentedFrame", ""])


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    data = args.binary.read_bytes()
    with tempfile.TemporaryDirectory() as folder:
        snapshot = Path(folder) / "linked"
        snapshot.write_bytes(data)
        sys.stdout.write(certificate(Image(data), snapshot))
