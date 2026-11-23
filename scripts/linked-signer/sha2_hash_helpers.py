# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Native SHA-2 PRF_msg and H_msg proofs for the measured Apple ABI.

VEX executes all three entries on each profile, including inline SHA operations.
PRF_msg permits representable randomizer-plus-message buffers. Ordinary H_msg
checks both sides of the first-block boundary; segmented H_msg checks the two
slices and every live byte of its pure context prefix. The byte-copy, allocation,
SHA-from-state, segmented continuation and MGF1 calls have named contracts.
The native results include all returned bytes and Vec ownership on normal return.
"""

import argparse
import hashlib
import struct
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    CONTEXT,
    HEAP,
    KEY,
    MESSAGE,
    RANDOM,
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
from pure_sign import symbol
from segmented import Segmented, execute


class Helpers(Segmented):
    def __init__(self, row, param, kind):
        super().__init__(row, param)
        self.kind = kind
        if kind == "hmsg":
            self.head = self.sha.bits * 2 - 3 * self.n
            self.headbytes = blob("message_prefix", self.head)
            raw = c.Concat(self.rand, self.sk[2], self.sk[3], self.headbytes)
            self.first_state = c.Concat(
                *(v.reversed for v in self.sha.block(self.sha.initial, raw))
            )

    def start(self, s):
        Driver.start(self, s)
        n = self.n
        if self.kind == "prf":
            args = [KEY + n, RANDOM, MESSAGE, self.msglen]
            s.add_constraints(c.ULE(self.msglen, (1 << 63) - 1 - n))
        elif self.kind == "hmsg":
            args = [self.param, RANDOM, KEY + 2 * n, KEY + 3 * n, MESSAGE, self.msglen]
            wrbytes(s, MESSAGE, self.headbytes)
        else:
            args = [
                RESULT,
                self.m,
                RANDOM,
                KEY + 2 * n,
                KEY + 3 * n,
                CONTEXT,
                self.ctxlen,
                MESSAGE,
            ]
            put(s, STACK, self.msglen, 8)
            wrbytes(s, CONTEXT, self.context)
            s.add_constraints(c.ULE(self.ctxlen, 255))
        for i, arg in enumerate(args):
            setattr(s.regs, f"x{i}", arg)
        s.regs.x8 = RESULT

    def extra_access(self, s, kind, ptr, length):
        if (
            self.kind == "hmsg"
            and kind == "read"
            and MESSAGE <= ptr
            and ptr + length <= MESSAGE + self.head
        ):
            equal(
                s,
                c.ULE(ptr + length - MESSAGE, self.msglen),
                True,
                "valid first-block slice load",
            )
            return True
        if self.kind == "prf" and RESULT <= ptr and ptr + length <= RESULT + self.n:
            return True
        if (
            self.kind == "seg_digest"
            and kind == "read"
            and STACK <= ptr
            and ptr + length <= STACK + 8
        ):
            return True
        # Arbitrarily long message copies are owned by memcpy's contract. Native
        # instructions in the PRF can only write the concrete randomizer prefix.
        if kind == "write" and self.kind == "prf":
            for base in s.globals["allocations"]:
                if int(base) <= ptr < int(base) + STRIDE:
                    require(
                        ptr + length <= int(base) + self.n,
                        "native overwrite of abstract message",
                    )
        return False

    def ordered(self, s, name):
        s.globals["calls"] += (name,)

    def call(self, s, name):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        n = self.n
        alloc = dict(s.globals["allocations"])
        if name == "reserve":
            require(self.kind in ("prf", "hmsg"), "unexpected reserve")
            desc = integer(s, x[0])
            self.workspace(s, desc, 24)
            cap, ptr, used = [unsigned(s, desc + i) for i in (0, 8, 16)]
            current = integer(s, ptr)
            equal(s, x[1], used, "reserve used length")
            equal(s, x[3], 1, "reserve element size")
            equal(s, x[4], 1, "reserve alignment")
            used_len = integer(s, used)
            if current == 1:
                equal(s, used, 0, "reserve on empty vec")
                equal(s, cap, 0, "initial cap")
                equal(s, current, 1, "empty sentinel")
                equal(s, x[2], n, "first reserve size")
            else:
                require(str(current) in alloc, "reserve on freed buffer")
                require(used_len in (n, 2 * n, 3 * n), "initialized prefix length")
                equal(s, cap, alloc.pop(str(current))[0], "old capacity")
                if self.kind == "prf":
                    equal(s, x[2], self.msglen, "additional message length")
                else:
                    equal(s, c.ULE(x[2], self.sha.bits * 2), True, "bounded append")
            newcap = c.BVS("new_capacity", 64)
            s.add_constraints(c.UGE(newcap, used + x[2]), c.ULE(newcap, (1 << 63) - 1))
            fresh = HEAP + STRIDE * s.globals["serial"]
            s.globals["serial"] += 1
            if current != 1:
                wrbytes(s, fresh, load(s, current, used_len))
            put(s, desc, newcap, 8)
            put(s, desc + 8, fresh, 8)
            alloc[str(fresh)] = (newcap, 1, "buffer")
            s.globals["allocations"] = alloc
        elif name == "copy":
            if self.kind == "prf":
                require(len(alloc) == 1, "invalid PRF temporary")
                dst = int(next(iter(alloc))) + n
                equal(s, x[0], dst, "message copy destination")
                equal(s, x[1], MESSAGE, "message copy source")
                equal(s, x[2], self.msglen, "message copy span")
                equal(
                    s,
                    c.ULE(n + self.msglen, next(iter(alloc.values()))[0]),
                    True,
                    "room for message copy",
                )
                s.globals["message_copy"] = dst
            elif self.kind == "hmsg":
                equal(s, x[1], MESSAGE, "short hash message copy source")
                equal(s, x[2], self.msglen, "short hash message copy length")
                equal(s, c.ULT(self.msglen, self.head), True, "short hash copy bound")
                dst = integer(s, x[0])
                require(str(dst - 3 * n) in alloc, "short hash copy outside owned Vec")
                equal(
                    s,
                    c.ULE(3 * n + self.msglen, alloc[str(dst - 3 * n)][0]),
                    True,
                    "short hash copy capacity",
                )
                for i in range(self.head):
                    wrbytes(
                        s,
                        dst + i,
                        c.If(
                            c.ULT(i, self.msglen),
                            self.headbytes.get_byte(i),
                            load(s, dst + i, 1),
                        ),
                    )
            else:
                dst = self.workspace(s, x[0], 255)
                equal(s, x[1], CONTEXT, "context copy source")
                equal(s, x[2], self.ctxlen, "context copy span")
                for i in range(255):
                    wrbytes(
                        s,
                        dst + i,
                        c.If(
                            c.ULT(i, self.ctxlen),
                            self.context.get_byte(i),
                            load(s, dst + i, 1),
                        ),
                    )
        elif name == "sha_from":
            self.ordered(s, name)
            b = self.sha.bits * 2
            if self.kind == "hmsg":
                if integer(s, x[1]) == 0:
                    equal(s, c.ULT(self.msglen, self.head), True, "short hash path")
                    equal(
                        s,
                        load(s, x[0], b // 2),
                        c.Concat(*(v.reversed for v in self.sha.initial)),
                        "initial hash state",
                    )
                    src = integer(s, x[2])
                    require(str(src) in alloc, "hash reads live buffer")
                    equal(s, x[3], 3 * n + self.msglen, "short hash input length")
                    equal(
                        s,
                        c.ULE(x[3], alloc[str(src)][0]),
                        True,
                        "short hash prefix capacity",
                    )
                    equal(
                        s,
                        load(s, src, 3 * n),
                        c.Concat(self.rand, self.sk[2], self.sk[3]),
                        "short hash R, seed, root",
                    )
                    mismatch = [
                        c.And(
                            c.ULT(i, self.msglen),
                            load(s, src + 3 * n + i, 1) != self.headbytes.get_byte(i),
                        )
                        for i in range(self.head)
                    ]
                    equal(s, c.Or(*mismatch), False, "short hash message content")
                else:
                    equal(
                        s, c.UGE(self.msglen, self.head), True, "full hash block path"
                    )
                    equal(s, x[1], b, "prehashed block")
                    equal(
                        s,
                        load(s, x[0], b // 2),
                        self.first_state,
                        "compressed first hash block",
                    )
                    equal(s, x[2], MESSAGE + self.head, "remaining message")
                    equal(s, x[3], self.msglen - self.head, "remaining length")
            else:
                equal(s, load(s, x[0], b // 2), self.ipad, "inner HMAC state")
                equal(s, x[1], b, "inner prehashed width")
                msg = integer(s, x[2])
                require(str(msg) in alloc, "hash reads freed buffer")
                equal(s, load(s, msg, n), self.rand, "randomizer prefix")
                equal(s, x[3], n + self.msglen, "randomizer and message length")
                if "message_copy" in s.globals:
                    equal(
                        s,
                        s.globals["message_copy"],
                        msg + n,
                        "message follows randomizer",
                    )
                else:
                    equal(s, self.msglen, 0, "nonempty message was skipped")
            wrbytes(s, self.workspace(s, x[8], b // 2), self.inner)
        elif name == "continued":
            self.ordered(s, name)
            b = self.sha.bits * 2
            equal(
                s,
                load(s, x[1], b // 2),
                c.Concat(*(w.reversed for w in self.sha.initial)),
                "initial SHA state",
            )
            equal(s, x[2], 0, "digest starts at byte zero")
            ptr = integer(s, x[3])
            for i, val in enumerate([self.rand, self.sk[2], self.sk[3]]):
                equal(s, load(s, ptr + n * i, n), val, "R, public seed and root")
            equal(s, load(s, ptr + 3 * n, 2), self.ctxlen[15:0], "pure context frame")
            mismatches = [
                c.And(
                    c.ULT(i, self.ctxlen),
                    load(s, ptr + 3 * n + 2 + i, 1) != self.context.get_byte(i),
                )
                for i in range(255)
            ]
            equal(s, c.Or(*mismatches), False, "digest context contents")
            equal(s, x[4], self.ctxlen + 3 * n + 2, "digest prefix length")
            equal(s, x[5], MESSAGE, "digest message")
            equal(s, x[6], self.msglen, "digest message length")
            wrbytes(s, self.workspace(s, x[0], b // 2), self.inner)
        elif name == "alloc_shim":
            pass
        elif name == "new":
            equal(s, x[0], 2 * n + 64, "allocated seed capacity")
            equal(s, x[1], 1, "byte alignment")
            require(not alloc, "unexpected existing allocation")
            s.globals["allocations"] = {str(HEAP): (c.BVV(2 * n + 64, 64), 1, "seed")}
            clobber_scratch(s)
            s.regs.x0 = HEAP
            return
        elif name == "mgf":
            self.ordered(s, name)
            expected = c.Concat(self.rand, self.sk[2], self.inner)
            base = integer(s, x[0])
            require(str(base) in alloc, "MGF reads a live allocation")
            equal(
                s,
                c.ULE(expected.size() // 8, alloc[str(base)][0]),
                True,
                "entire MGF seed is live",
            )
            equal(s, load(s, x[0], expected.size() // 8), expected, "MGF1 seed")
            equal(s, x[1], expected.size() // 8, "MGF seed length")
            equal(s, x[2], self.m, "MGF request")
            equal(s, x[8], RESULT, "MGF output slot")
            # The callee returns an arbitrary valid Vec of m bytes.
            cap = c.BVS("mgf_cap", 64)
            s.add_constraints(c.UGE(cap, self.m), c.ULE(cap, (1 << 63) - 1))
            s.globals["mgf_cap"] = cap
            put(s, RESULT, cap, 8)
            put(s, RESULT + 8, HEAP + 16 * STRIDE, 8)
            put(s, RESULT + 16, self.m, 8)
            wrbytes(s, HEAP + 16 * STRIDE, self.digest)
            alloc[str(HEAP + 16 * STRIDE)] = (cap, 1, "digest")
            s.globals["allocations"] = alloc
        elif name == "free":
            self.release(s, integer(s, x[0]), x[1], integer(s, x[2]))
        else:
            raise ValueError("unexpected hash callee " + name)
        clobber_scratch(s)

    def finish(self, s):
        if self.kind == "prf":
            require(
                s.globals["calls"] == ("sha_from",) and not s.globals["allocations"],
                "PRF calls or ownership",
            )
            equal(s, load(s, RESULT, self.n), self.r, "truncated HMAC")
        else:
            require(
                s.globals["calls"]
                == (("continued" if self.kind == "seg_digest" else "sha_from"), "mgf"),
                "digest hash order",
            )
            require(
                set(s.globals["allocations"]) == {str(HEAP + 16 * STRIDE)},
                "digest ownership",
            )
            equal(s, unsigned(s, RESULT), s.globals["mgf_cap"], "digest capacity")
            equal(s, unsigned(s, RESULT + 8), HEAP + 16 * STRIDE, "digest pointer")
            equal(s, unsigned(s, RESULT + 16), self.m, "digest length")
            equal(s, load(s, HEAP + 16 * STRIDE, self.m), self.digest, "digest bytes")
        self.check_abi(s)
        self.final_paths += 1


def verify(path, image, n, v, kind):
    row, param, _, _, hooks = objects(path, image, n, v, "sha2")
    driver = Helpers(row, param, kind)
    bits = driver.sha.bits
    hooks[
        image.function(f"6sha{bits * 8}11sha{bits * 8}_from".encode(), b"6slhdsa")[0]
    ] = "sha_from"
    inner = f"9continuedKj{bits * 2:x}_NtB2_6Sha{bits * 8}EB6_".encode()
    hooks[image.function(inner, b"6slhdsa3slh7message")[0]] = "continued"
    hooks[image.function(f"4hash11mgf1_sha{bits * 8}".encode(), b"6slhdsa")[0]] = "mgf"
    hooks[symbol(image, b"___rustc", b"___rust_alloc")] = "new"
    hooks[symbol(image, b"___rustc", b"___rust_no_alloc_shim_is_unstable_v2")] = (
        "alloc_shim"
    )
    suffix = (
        f"4hash7prf_msgKj{n:x}_EB4_"
        if kind == "prf"
        else f"4hash5h_msgKj{n:x}_EB4_"
        if kind == "hmsg"
        else f"3slh7message6digestKj{n:x}_EB6_"
    ).encode()
    pc, words = image.function(suffix, b"6slhdsa")
    hooks.pop(pc, None)
    execute(path, image, pc, words, hooks, driver)
    require(
        driver.final_paths == {"prf": 3, "seg_digest": 1, "hmsg": 52}[kind],
        "unexpected hash path coverage",
    )
    print(f"SHA2-{8 * n}{v} {kind}: {driver.final_paths} normal paths", flush=True)


def mutations(image):
    tests = [
        (
            "prf",
            16,
            b"4hash7prf_msgKj10_EB4_",
            21,
            (20 ^ 21) << 5,
            ("randomizer prefix",),
        ),
        (
            "seg_digest",
            24,
            b"3slh7message6digestKj18_EB6_",
            41,
            31 ^ 21,
            ("pure context frame",),
        ),
        (
            "hmsg",
            32,
            b"4hash5h_msgKj20_EB4_",
            12,
            (1 ^ 2) << 16,
            ("short hash R, seed, root", "compressed first hash block"),
        ),
    ]
    with tempfile.TemporaryDirectory() as directory:
        for kind, n, fn, i, mask, expected in tests:
            pc, words = image.function(fn, b"6slhdsa")
            data = bytearray(image.data)
            struct.pack_into("<I", data, pc - image.base + 4 * i, words[i] ^ mask)
            path = Path(directory) / "altered-hash"
            path.write_bytes(data)
            try:
                verify(path, Image(data), n, "s", kind)
            except ValueError as err:
                require(
                    any(m in str(err) for m in expected),
                    f"unexpected mutation error: {err}",
                )
            else:
                raise AssertionError(f"altered {kind} passed")
    print("Rejected three independent hash argument or framing mutations", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("--kind", choices=("prf", "seg_digest", "hmsg"))
    parser.add_argument("--width", type=int, choices=(16, 24, 32))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    image = Image(args.binary.read_bytes())
    for n in [args.width] if args.width else (16, 24, 32):
        for kind in [args.kind] if args.kind else ("prf", "seg_digest", "hmsg"):
            for v in ("s", "f"):
                verify(args.binary, image, n, v, kind)
    if args.self_test:
        mutations(image)
    print("Mach-O SHA-256", hashlib.sha256(image.data).hexdigest())
