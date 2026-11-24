# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Prove the linked MGF1 seed/counter encoding, digest collection and truncation used by H_msg."""

import argparse
import hashlib
import struct
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    HEAP,
    KEY,
    RESULT,
    STACK,
    STRIDE,
    Driver,
    Image,
    blob,
    c,
    clobber_scratch,
    equal,
    integer,
    load,
    objects,
    put,
    require,
    unsigned,
    wrbytes,
)
from segmented import Compression, execute


class Mask(Driver):
    def __init__(self, row, param):
        super().__init__(row, param, "slh_sign_internal", "sha2")
        self.sha = Compression(self.n, None)
        self.d = self.sha.bits
        self.seedlen = 2 * self.n + self.d
        self.seed = blob("MGF_seed", self.seedlen)
        self.outputs = [
            blob("MGF_hash", self.d) for _ in range((self.m + self.d - 1) // self.d)
        ]

    def start(self, s):
        super().start(s)
        wrbytes(s, KEY, self.seed)
        s.regs.x0, s.regs.x1, s.regs.x2 = KEY, self.seedlen, self.m

    def extra_access(self, s, kind, ptr, size):
        return kind == "read" and KEY <= ptr and ptr + size <= KEY + self.seedlen

    def check_range(self, s, ptr, size, reading):
        if reading and KEY <= ptr and ptr + size <= KEY + self.seedlen:
            return
        if reading and STACK - 2048 <= ptr and ptr + size <= STACK:
            return
        for base, (cap, align, _) in s.globals["allocations"].items():
            off = ptr - int(base)
            if 0 <= off and off + size <= STRIDE:
                equal(s, c.ULE(off + size, cap * align), True, "MGF live byte span")
                return
        raise ValueError("MGF memory outside live buffers")

    def call(self, s, name):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        alloc = dict(s.globals["allocations"])
        if name == "reserve":
            desc = integer(s, x[0])
            self.workspace(s, desc, 24)
            used = integer(s, unsigned(s, desc + 16))
            old = integer(s, unsigned(s, desc + 8))
            add = integer(s, x[2])
            require(0 < add <= 256 and used + add <= 512, "bounded capacity request")
            equal(s, x[1], used, "MGF used prefix")
            equal(s, x[3], 1, "element size")
            equal(s, x[4], 1, "alignment")
            if old == 1:
                require(used == 0, "invalid empty buffer")
                equal(s, unsigned(s, desc), 0, "empty buffer capacity")
            else:
                self.check_range(s, old, used, True)
                equal(s, unsigned(s, desc), alloc.pop(str(old))[0], "MGF old owner")
            cap = c.BVS("new_cap", 64)
            s.add_constraints(c.UGE(cap, used + add), c.ULE(cap, (1 << 63) - 1))
            addr = HEAP + s.globals["serial"] * STRIDE
            s.globals["serial"] += 1
            if used:
                wrbytes(s, addr, load(s, old, used))
            alloc[str(addr)] = (cap, 1, "MGF buffer")
            s.globals["allocations"] = alloc
            put(s, desc, cap, 8)
            put(s, desc + 8, addr, 8)
        elif name == "copy":
            dest, src, size = [integer(s, v) for v in x[:3]]
            require(0 < size <= 256, "bounded MGF copy")
            self.check_range(s, dest, size, False)
            self.check_range(s, src, size, True)
            require(src + size <= dest or dest + size <= src, "nonoverlapping MGF copy")
            wrbytes(s, dest, load(s, src, size))
            clobber_scratch(s)
            s.regs.x0 = dest
            return
        elif name == "sha_from":
            count = len(s.globals["calls"])
            require(count < len(self.outputs), "too many MGF hash calls")
            equal(
                s,
                load(s, x[0], self.d),
                c.Concat(*(v.reversed for v in self.sha.initial)),
                "MGF initial SHA state",
            )
            equal(s, x[1], 0, "no MGF prehashed bytes")
            equal(s, x[3], self.seedlen + 4, "MGF seed and counter length")
            src = integer(s, x[2])
            self.check_range(s, src, self.seedlen + 4, True)
            equal(s, load(s, src, self.seedlen), self.seed, "MGF hash seed")
            equal(
                s,
                load(s, src + self.seedlen, 4),
                count,
                "four-byte big-endian MGF counter",
            )
            wrbytes(s, self.workspace(s, x[8], self.d), self.outputs[count])
            s.globals["calls"] += (name,)
        elif name == "free":
            self.release(s, integer(s, x[0]), x[1], integer(s, x[2]))
        else:
            raise ValueError("unexpected MGF call " + name)
        clobber_scratch(s)

    def finish(self, s):
        require(len(s.globals["calls"]) == len(self.outputs), "wrong MGF hash count")
        ptr = integer(s, unsigned(s, RESULT + 8))
        alloc = s.globals["allocations"]
        require(set(alloc) == {str(ptr)}, "incorrect MGF final allocation")
        equal(s, unsigned(s, RESULT), alloc[str(ptr)][0], "capacity")
        equal(s, unsigned(s, RESULT + 16), self.m, "truncated MGF length")
        self.check_range(s, ptr, self.m, True)
        digest = c.Concat(*self.outputs) if len(self.outputs) > 1 else self.outputs[0]
        equal(
            s,
            load(s, ptr, self.m),
            digest.get_bytes(0, self.m),
            "truncated MGF digest stream",
        )
        self.check_abi(s)
        self.final_paths += 1


def verify(path, image, n, v):
    row, param, _, _, hooks = objects(path, image, n, v, "sha2")
    driver = Mask(row, param)
    sha = driver.d * 8
    hooks[image.function(f"6sha{sha}11sha{sha}_from".encode(), b"6slhdsa")[0]] = (
        "sha_from"
    )
    pc, words = image.function(f"4hash11mgf1_sha{sha}".encode(), b"6slhdsa")
    execute(path, image, pc, words, hooks, driver)
    require(
        driver.final_paths == (8 if len(driver.outputs) == 2 else 2),
        "MGF path coverage",
    )
    print(
        f"SHA2-{8 * n}{v} MGF1: {driver.final_paths} normal paths, {len(driver.outputs)} SHA digests",
        flush=True,
    )


def mutations(image):
    # Counter one is reachable at SHA2-128f. A wrong counter source fails the
    # exact seed || I2OSP(counter,4) assertion even with arbitrary SHA outputs.
    name = b"4hash11mgf1_sha256"
    pc, words = image.function(name, b"6slhdsa")
    with tempfile.TemporaryDirectory() as d:
        path = Path(d) / "wrong-mgf-counter"
        data = bytearray(image.data)
        require(words[24] & 0xFFC003FF == 0x1100037B, "unexpected counter increment")
        struct.pack_into("<I", data, pc - image.base + 4 * 24, words[24] ^ (3 << 10))
        path.write_bytes(data)
        try:
            verify(path, Image(data), 16, "f")
        except ValueError as err:
            require(
                "four-byte big-endian MGF counter" in str(err),
                f"unexpected mutation result: {err}",
            )
        else:
            raise AssertionError("accepted wrong MGF counter")
    print("Rejected a mutated MGF counter increment", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    image = Image(args.binary.read_bytes())
    for n in (16, 24, 32):
        for v in ("s", "f"):
            verify(args.binary, image, n, v)
    if args.self_test:
        mutations(image)
    print("Mach-O SHA-256", hashlib.sha256(image.data).hexdigest())
