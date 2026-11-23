"""Bind exported SHA-2 and SHAKE entry stubs to their target ABI and FIPS parameter row."""

import struct
from image import require, sign_extend


def inspect(image, name, target, arguments):
    pc, words = image.function(name, b"6slhdsa4sets")
    dst, _ = image.function(target, b"6slhdsa")
    regs = {i: f"x{i}" for i in range(31)}
    for i, w in enumerate(words[:-1]):
        d = w & 31
        require(d < len(arguments), "wrapper clobbers a non-argument register")
        if w & 0xFFE0FFE0 == 0xAA0003E0:
            regs[d] = regs[w >> 16 & 31]
        elif w & 0x9F000000 == 0x90000000:
            pages = sign_extend((w >> 5 & 0x7FFFF) << 2 | (w >> 29 & 3), 21)
            regs[d] = ((pc + 4 * i) & ~4095) + 4096 * pages
        elif w & 0xFFC00000 == 0x91000000:
            regs[d] = regs[w >> 5 & 31] + (w >> 10 & 4095)
        elif w & 0xFFE00000 == 0x52800000:
            regs[d] = w >> 5 & 65535
        else:
            raise ValueError(f"unmodeled entry instruction {w:08x}")
    tail = words[-1]
    require(
        tail & 0xFC000000 == 0x14000000
        and pc + 4 * (len(words) - 1 + sign_extend(tail & 0x3FFFFFF, 26)) == dst,
        "incorrect public-entry tail call",
    )
    require(
        [regs[i] for i in range(1, len(arguments))] == arguments[1:],
        "incorrect forwarded public arguments",
    )
    # Native Params layout for this ABI. Ignore trailing padding.
    return struct.unpack("<QQIIIII", image.read(b"__const", regs[0], 36))


def certificate(image):
    result = [
        "import Spec.SlhDsa",
        "namespace LinkedEntries",
        "def fields (p : Spec.Params) := [p.n, p.m, p.h, p.d, p.hp, p.a, p.k]",
    ]
    for family in ("sha2", "shake"):
        for width in (16, 24, 32):
            for variant in ("s", "f"):
                label = f"{family}_{8 * width}{variant}"
                prefix = ("6slhdsa4sets" + str(len(label)) + label).encode()
                impl = b"6slhdsa" + (b"5shake" if family == "shake" else b"")
                mono = f"Kj{width:x}_EB{6 if family == 'shake' else 4}_".encode()
                operations = [
                    (
                        b"6keygen",
                        b"3api",
                        [None, "x0", 3 * width, "x1", 4 * width, "x2", 2 * width],
                    ),
                    (
                        b"17slh_sign_internal",
                        b"3slh",
                        [None, "x0", "x1", "x2", 4 * width, "x3"],
                    ),
                    (
                        b"19slh_verify_internal",
                        b"3slh",
                        [None, "x0", "x1", "x2", "x3", "x4", 2 * width],
                    ),
                ]
                for op, mod, args in operations:
                    row = inspect(image, prefix + op, impl + mod + op + mono, args)
                    result.append(
                        f"example : fields Spec.{label} = {list(row)} := by rfl"
                    )
    return "\n".join(result + ["end LinkedEntries", ""])
