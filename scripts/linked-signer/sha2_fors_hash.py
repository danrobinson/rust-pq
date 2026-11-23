# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check linked FORS roots hashing and both Apple two-lane SHA-512 parent kernels.

The roots checker verifies general address compression, the seeded SHA finalizer
input and digest truncation at each public FORS length; allocation success and
memcpy use ABI contracts. The finalizer is verified by sha_from.py. The paired
kernel runs all native instructions on two independent symbolic 128-byte
messages and an arbitrary common chaining state, compared to two independent
applications of the SHA-512 round reference in segmented.py.
"""

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
from hypertree import instructions
from segmented import Compression, execute
from sha2_tree_hash import seed_record

ADDRESS, INPUT = KEY + 512, KEY + 1024


class Roots(Driver):
    def __init__(self, row, param):
        super().__init__(row, param, "slh_sign_internal", "sha2")
        self.sha = Compression(self.n, None)
        self.wide = self.n != 16
        self.b = 128 if self.wide else 64
        self.roots = blob("all_FORS_roots", self.n * self.k)
        self.out = blob("SHA_digest", self.b // 2)
        self.fields = [
            blob(label, size)
            for label, size in (
                ("tree", 8),
                ("layer", 4),
                ("typ", 4),
                ("kp", 4),
                ("word2", 4),
                ("word3", 4),
            )
        ]
        tree, layer, typ, kp, w2, w3 = self.fields
        self.address = c.Concat(layer[7:0], tree, typ[7:0], kp, w2, w3)
        h256 = [blob("h256", 4) for _ in range(8)]
        h512 = [blob("h512", 8) for _ in range(8)]
        self.record = seed_record(self.n, blob("PK_seed", self.n), h256, h512)
        self.state = c.Concat(*(w.reversed for w in (h512 if self.wide else h256)))

    def start(self, s):
        super().start(s)
        wrbytes(s, KEY, self.record)
        for off, val in zip((0, 8, 12, 16, 20, 24), self.fields):
            put(s, ADDRESS + off, val, val.size() // 8)
        wrbytes(s, INPUT, self.roots)
        s.regs.x0, s.regs.x1, s.regs.x2, s.regs.x3 = (
            KEY,
            ADDRESS,
            INPUT,
            self.k * self.n,
        )

    def extra_access(self, s, kind, p, l):
        if kind == "read" and any(
            a <= p and p + l <= a + k
            for a, k in [(KEY, 96 + self.n), (ADDRESS, 28), (INPUT, self.n * self.k)]
        ):
            return True
        return bool(kind == "write" and RESULT <= p and p + l <= RESULT + self.n)

    def call(self, s, name):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        alloc = dict(s.globals["allocations"])
        count = self.k * self.n
        if name == "reserve":
            desc = self.workspace(s, x[0], 24)
            old = integer(s, unsigned(s, desc + 8))
            used = integer(s, x[1])
            extra = integer(s, x[2])
            equal(s, unsigned(s, desc + 16), used, "roots buffer initialized length")
            equal(s, x[3], 1, "byte size")
            equal(s, x[4], 1, "byte alignment")
            if used == 0:
                require(
                    not alloc and old == 1 and extra == 22,
                    "initial address reservation",
                )
                equal(s, unsigned(s, desc), 0, "empty buffer capacity")
            else:
                require(
                    used == 22 and extra == count and str(old) in alloc,
                    "valid roots reservation",
                )
                oldcap = alloc.pop(str(old))[0]
                equal(s, unsigned(s, desc), oldcap, "old capacity")
                equal(
                    s,
                    load(s, old, 22),
                    self.address,
                    "compressed address before growth",
                )
            cap = blob("successful_capacity", 8)
            s.add_constraints(c.UGE(cap, used + extra), c.ULE(cap, (1 << 63) - 1))
            addr = HEAP + STRIDE * s.globals["serial"]
            s.globals["serial"] += 1
            if used:
                wrbytes(s, addr, load(s, old, used))
            put(s, desc, cap, 8)
            put(s, desc + 8, addr, 8)
            alloc[str(addr)] = (cap, 1, "roots")
            s.globals["allocations"] = alloc
        elif name == "copy":
            require(s.globals["calls"] == (), "single copy of all roots")
            (base,) = alloc
            addr = int(base)
            equal(s, x[0], addr + 22, "roots follow compressed address")
            equal(s, x[1], INPUT, "original concatenated roots")
            equal(s, x[2], count, "all root bytes")
            self.live_bytes(s, addr, 22 + count)
            wrbytes(s, addr + 22, self.roots)
            s.globals["calls"] += ("copy",)
            clobber_scratch(s)
            s.regs.x0 = addr + 22
            return
        elif name == "sha":
            require(s.globals["calls"] == ("copy",), "root hash call order")
            equal(
                s,
                x[0],
                KEY + (0 if self.wide else 64),
                "correct precomputed seed state",
            )
            equal(s, load(s, x[0], self.b // 2), self.state, "seed chaining words")
            equal(s, x[1], self.b, "absorbed seed block length")
            (base,) = alloc
            addr = int(base)
            equal(s, x[2], addr, "root hash prefix pointer")
            equal(s, x[3], 22 + count, "root hash message length")
            self.live_bytes(s, addr, 22 + count)
            equal(
                s,
                load(s, addr, 22 + count),
                c.Concat(self.address, self.roots),
                "compressed address and all roots",
            )
            wrbytes(s, self.workspace(s, x[8], self.b // 2), self.out)
            s.globals["calls"] += ("sha",)
        elif name == "free":
            self.release(s, integer(s, x[0]), x[1], integer(s, x[2]))
        else:
            raise ValueError("unexpected root hash call " + name)
        clobber_scratch(s)

    def finish(self, s):
        require(
            s.globals["calls"] == ("copy", "sha") and not s.globals["allocations"],
            "roots result ownership",
        )
        equal(
            s,
            load(s, RESULT, self.n),
            self.out.get_bytes(0, self.n),
            "truncated root hash",
        )
        self.check_abi(s)
        self.final_paths += 1


class Paired(Driver):
    def __init__(self, row, param):
        super().__init__(row, param, "slh_sign_internal", "sha2")
        self.sha = Compression(self.n, None)
        self.initial = [blob("chaining_word", 8) for _ in range(8)]
        self.blocks = [blob("parent_block", 128) for _ in range(2)]
        self.expected = c.Concat(
            *(
                c.Concat(*self.sha.block(self.initial, b)).get_bytes(0, self.n)
                for b in self.blocks
            )
        )

    def start(self, s):
        super().start(s)
        wrbytes(s, KEY, c.Concat(*(v.reversed for v in self.initial)))
        wrbytes(s, INPUT, c.Concat(*self.blocks))
        s.regs.x0, s.regs.x1, s.regs.x2 = KEY, INPUT, RESULT

    def extra_access(self, s, kind, p, l):
        if kind == "read" and (
            (KEY <= p and p + l <= KEY + 64) or (INPUT <= p and p + l <= INPUT + 256)
        ):
            return True
        if kind == "write" and RESULT <= p and p + l <= RESULT + 2 * self.n:
            return True
        base, size = self.constants_range
        require(
            STACK - 2048 <= p
            and p + l <= STACK
            or kind == "read"
            and base <= p
            and p + l <= base + size,
            "paired kernel out-of-bounds access",
        )
        return True

    def finish(self, s):
        equal(
            s,
            load(s, RESULT, 2 * self.n),
            self.expected,
            "both ordered SHA-512 digests",
        )
        self.check_abi(s)
        self.final_paths += 1


def verify(path, image, n, v, mode):
    row, param, *_, hooks = objects(path, image, n, v, "sha2")
    if mode == "paired":
        driver = Paired(row, param)
        hooks = {}
        pc, words = image.function(
            f"6paired16compress_parentsKj{n:x}_EB6_".encode(), b"6slhdsa6sha512"
        )
    else:
        driver = Roots(row, param)
        bits = 256 if n == 16 else 512
        hooks = {
            a: name for a, name in hooks.items() if name in ("reserve", "copy", "free")
        }
        hooks[image.function(f"6sha{bits}11sha{bits}_from".encode(), b"6slhdsa")[0]] = (
            "sha"
        )
        pc, words = image.function(f"4hash5thashKj{n:x}_EB4_".encode(), b"6slhdsa")
    execute(path, image, pc, words, hooks, driver)
    require(
        driver.final_paths == (1 if mode == "paired" else 2), "normal path coverage"
    )
    label = (
        f"n={n} shared two-lane kernel"
        if mode == "paired"
        else f"SHA2-{8 * n}{v} roots"
    )
    print(f"{label}: verified {driver.final_paths} normal path(s)", flush=True)


def mutations(path, image):
    tests = [
        (
            16,
            "roots",
            b"4hash5thashKj10_EB4_",
            81,
            1 << 5,
            "mov",
            "absorbed seed block length",
        ),
        (
            24,
            "paired",
            b"6paired16compress_parentsKj18_EB6_",
            25,
            1 << 5,
            "sha512h.2d",
            "both ordered SHA-512 digests",
        ),
    ]
    with tempfile.TemporaryDirectory() as directory:
        bad = Path(directory) / "altered-fors-hash"
        for n, mode, func, i, mask, op, msg in tests:
            pc, words = image.function(func, b"6slhdsa")
            require(
                instructions(path, pc, words)[i][0] == op, "unexpected mutation site"
            )
            data = bytearray(image.data)
            struct.pack_into("<I", data, pc - image.base + i * 4, words[i] ^ mask)
            bad.write_bytes(data)
            try:
                verify(bad, Image(data), n, "s", mode)
            except ValueError as err:
                require(msg in str(err), f"unexpected mutation result: {err}")
            else:
                raise AssertionError(f"accepted alteration to {msg}")
    print("Rejected altered root-prefix length and paired SHA-512 operand", flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("binary", type=Path)
    p.add_argument("--width", type=int, choices=(16, 24, 32))
    p.add_argument("--mode", choices=("roots", "paired"))
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    img = Image(a.binary.read_bytes())
    for n in [a.width] if a.width else [16, 24, 32]:
        if a.mode in (None, "paired") and n > 16:
            verify(a.binary, img, n, "s", "paired")
        if a.mode in (None, "roots"):
            for v in "sf":
                verify(a.binary, img, n, v, "roots")
    if a.self_test:
        mutations(a.binary, img)
    print("Mach-O SHA-256", hashlib.sha256(img.data).hexdigest())
