"""Extract three long-signing frame windows per word width from the Apple image."""

import argparse
import hashlib
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from image import Image, require, sign_extend
from pure_sign import memcpy_address


def certificate(image, snapshot):
    lines = [
        "import Spec.ArmSegmentedFrame",
        "namespace LinkedSegmentedFrame",
        "open Spec.ArmSegmentedFrame",
        "set_option maxRecDepth 65536",
        "set_option maxHeartbeats 0",
        "-- Mach-O SHA-256 " + hashlib.sha256(image.data).hexdigest(),
    ]
    memcpy = memcpy_address(image, snapshot)
    for n in (16, 24, 32):
        pc, words = image.function(f"3slh7message4signKj{n:x}_EB6_".encode(), b"6slhdsa")
        digest, _ = image.function(f"3slh7message6digestKj{n:x}_EB6_".encode(), b"6slhdsa")
        size = 256 if n == 16 else 512
        cont, _ = image.function(
            f"3slh7message9continuedKj{size//4:x}_NtB2_6Sha{size}EB6_".encode(), b"6slhdsa"
        )
        indices = []
        for target in (memcpy, cont, digest):
            hits = [i for i,w in enumerate(words) if w >> 26 == 0x25
                    and pc+4*i+4*sign_extend(w % 2**26, 26) == target]
            require(hits and (len(hits) == 1 or target == memcpy), "missing segment call")
            indices.append(hits[0])
        copy, inner, hm = indices
        # All three windows use the same inner and digest ABI instruction counts.
        require(copy < inner - 7 < inner < hm - 9 < hm, "unexpected segmentation")
        lines.append(f"def words{n} : Array Nat := #[" + ",\n ".join(
            ", ".join(f"0x{w:08x}" for w in words[i:i+8]) for i in range(0,len(words),8)) + "]")
        for variant in "sf":
            name = f"sha2_{8*n}{variant}"
            stub, code = image.function(f"{len(name)}{name}17slh_sign_internal".encode(), b"6slhdsa4sets")
            (j,) = [j for j,w in enumerate(code) if w & 0x9f00001f == 0x90000000]
            w = code[j]
            require(code[j+1] & 0xffc003ff == 0x91000000, "unexpected parameter pointer")
            record = ((stub+4*j) & ~4095) + 4096*sign_extend((w>>5 & 0x7ffff)*4+(w>>29 & 3),21) + (code[j+1]>>10 & 4095)
            raw = list(image.read(b"__const", record, 36))
            lines += [
                f"def {name} : Image := ⟨Spec.{name},0x{record:x},{raw},0x{pc:x},0x{memcpy:x},"
                f"0x{cont:x},0x{digest:x},words{n},{copy},{inner-7},{inner},{hm-9},{hm}⟩",
                f"theorem {name}_checked : checked {name} = some expected := by decide +kernel",
            ]
            if variant == "s":
                controls = {16:[(0x390343ff,0x390343f4), (0x91004a84,0x91004684)],
                            24:[(0x3904e7f5,0x3904e7ff), (0xf94037e5,0xf9403be5)],
                            32:[(0x91018304,0x91010304), (0xf90003f9,0xf90003f7)]}[n]
                for old,new in controls:
                    (j,) = [j for j,w in enumerate(words) if w == old]
                    lines.append(f"theorem reject_{n}_{j} : checked {{ {name} with words := words{n}.set! "
                                 f"{j} 0x{new:08x} }} = none := by decide +kernel")
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
