# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Verify the two linked segmented SHA-2 continuation bodies on public signer/verifier inputs.

The PRF prefix has N+2+ctxlen bytes, and H_msg has 3N+2+ctxlen bytes.
For every possible block quotient and alignment, the remainder, prefix contents,
message contents, and message length >=1024 remain symbolic. The initial chaining
state is unconstrained. Inlined SHA instructions use the same uninterpreted
applications as the reference rounds. sha_from.py verifies the finalizer used here.
"""

import argparse
import hashlib
import struct
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    MESSAGE,
    RESULT,
    STACK,
    Driver,
    Image,
    blob,
    c,
    clobber_scratch,
    equal,
    integer,
    load,
    objects,
    require,
    wrbytes,
)
from hypertree import instructions
from pure_sign import memcpy_address
from segmented import Compression, execute

PREFIX, STATE = 0x180000, 0x190000


class Continuation(Driver):
    def __init__(self, row, param, bits, q, partial):
        super().__init__(row, param, "slh_sign_internal", "sha2")
        self.sha = Compression(self.n, None)
        self.b = bits // 4
        self.q = q
        self.partial = partial
        self.rem = c.BVS("prefix_remainder", 64) if partial else c.BVV(0, 64)
        self.pre = c.BVS("aligned_absorbed_byte_count", 64)
        self.prefixlen = q * self.b + self.rem
        self.prefix = blob("prefix_bytes", (q + 1) * self.b)
        self.initial = blob("initial_chaining_words", self.b // 2)
        self.digest = blob("finalizer_digest", self.b // 2)
        self.msgwindow = blob("message_head_in_joined_block", self.b)
        # msgwindow[i], when i >= rem, represents input message byte i-rem.
        # This is an arbitrary symbolic reindexing of at most one message block.
        tail = self.prefix.get_bytes(q * self.b, self.b)
        self.joined = c.Concat(
            *(
                c.If(c.ULT(i, self.rem), tail.get_byte(i), self.msgwindow.get_byte(i))
                for i in range(self.b)
            )
        )
        width = self.b // 16
        state = [
            self.initial.get_bytes(i, width).reversed
            for i in range(0, self.b // 2, width)
        ]
        blocks = [self.prefix.get_bytes(i * self.b, self.b) for i in range(q)]
        if partial:
            blocks.append(self.joined)
        for block in blocks:
            state = self.sha.block(state, block)
        self.expected = c.Concat(*(w.reversed for w in state))

    def start(self, s):
        super().start(s)
        lower, upper = (18, 305) if self.b == 64 else (26, 353)
        s.add_constraints(
            c.UGE(self.prefixlen, lower),
            c.ULE(self.prefixlen, upper),
            c.UGE(self.msglen, 1024),
            c.Or(self.pre == 0, self.pre == self.b),
        )
        if self.partial:
            s.add_constraints(c.UGT(self.rem, 0), c.ULT(self.rem, self.b))
        require(s.solver.satisfiable(), "empty prefix domain")
        wrbytes(s, STATE, self.initial)
        wrbytes(s, PREFIX, self.prefix)
        for i, v in enumerate(
            (RESULT, STATE, self.pre, PREFIX, self.prefixlen, MESSAGE, self.msglen)
        ):
            setattr(s.regs, f"x{i}", v)

    def extra_access(self, s, kind, p, n):
        if STATE <= p and p + n <= STATE + self.b // 2:
            return True
        if kind == "read" and PREFIX <= p and p + n <= PREFIX + (self.q + 1) * self.b:
            equal(
                s,
                c.ULE(p + n - PREFIX, self.prefixlen),
                True,
                "bounded native prefix loads",
            )
            return True
        base, size = self.constants_range
        require(
            STACK - 2048 <= p
            and p + n <= STACK
            or kind == "read"
            and base <= p
            and p + n <= base + size,
            f"unexpected native continuation {kind} at {p:#x}",
        )
        return True

    def call(self, s, kind):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        calls = s.globals["calls"]
        b = self.b
        if kind == "copy":
            require(self.partial, "aligned prefix copied")
            if not calls:
                dst = integer(s, x[0])
                require(
                    STACK - 2048 <= dst and dst + b <= STACK, "joined block workspace"
                )
                equal(s, x[1], PREFIX + self.q * b, "partial prefix pointer")
                equal(s, x[2], self.rem, "partial prefix length")
                tail = self.prefix.get_bytes(self.q * b, b)
                for i in range(b):
                    wrbytes(
                        s,
                        dst + i,
                        c.If(c.ULT(i, self.rem), tail.get_byte(i), load(s, dst + i, 1)),
                    )
                s.globals["head"] = dst
            else:
                require(calls == ("copy",), "unexpected boundary copy")
                dst = s.globals["head"]
                equal(s, x[0], dst + self.rem, "message follows partial prefix")
                equal(s, x[1], MESSAGE, "message head pointer")
                equal(s, x[2], b - self.rem, "message bytes to boundary")
                for i in range(b):
                    v = c.If(
                        c.ULT(i, self.rem),
                        load(s, dst + i, 1),
                        self.msgwindow.get_byte(i),
                    )
                    equal(s, v, self.joined.get_byte(i), "formed prefix/message block")
                wrbytes(s, dst, self.joined)
            result = x[0]
            clobber_scratch(s)
            s.regs.x0 = result
        else:
            require(kind == "finish", "unexpected continuation call")
            require(
                calls == (("copy", "copy") if self.partial else ()),
                "prefix and message boundary calls",
            )
            equal(s, x[0], STATE, "finalizer chaining pointer")
            equal(
                s,
                load(s, STATE, b // 2),
                self.expected,
                "chained all full prefix and joined blocks",
            )
            equal(
                s,
                x[1],
                self.pre + (self.q + int(self.partial)) * b,
                "total absorbed bytes",
            )
            used = b - self.rem if self.partial else 0
            equal(s, x[2], MESSAGE + used, "unconsumed message pointer")
            equal(s, x[3], self.msglen - used, "unconsumed message length")
            equal(s, x[8], RESULT, "final digest return address")
            wrbytes(s, RESULT, self.digest)
            clobber_scratch(s)
        s.globals["calls"] = calls + (kind,)

    def finish(self, s):
        require(s.globals["calls"][-1:] == ("finish",), "missing finalizer")
        equal(s, load(s, RESULT, self.b // 2), self.digest, "returned finalizer digest")
        self.check_abi(s)
        self.final_paths += 1


def check(task):
    path, bits, q, partial = task
    image = Image(path.read_bytes())
    row, param, *_ = objects(path, image, 16 if bits == 256 else 32, "s", "sha2")
    name = f"9continuedKj{bits // 4:x}_NtB2_6Sha{bits}EB6_".encode()
    pc, words = image.function(name, b"6slhdsa3slh7message")
    final, _ = image.function(f"6sha{bits}11sha{bits}_from".encode(), b"6slhdsa")
    driver = Continuation(row, param, bits, q, partial)
    execute(
        path,
        image,
        pc,
        words,
        {final: "finish", memcpy_address(image, path): "copy"},
        driver,
    )
    require(driver.final_paths == 1, "missing or duplicate normal continuation path")


def mutations(path, image, bits):
    pc, words = image.function(
        f"9continuedKj{bits // 4:x}_NtB2_6Sha{bits}EB6_".encode(),
        b"6slhdsa3slh7message",
    )
    decoded = instructions(path, pc, words)
    add = [
        i for i, (op, args) in decoded.items() if op == "add" and args == "x2, x22, x24"
    ]
    require(len(add) == 1, "unique finalizer message offset")
    rounds = [i for i, (op, args) in decoded.items() if op.startswith(f"sha{bits}h.")]
    require(rounds, "missing hardware rounds")
    # The last static round loop compresses the mixed prefix/message block.
    for i, mask, error in [
        (add[0], 1 << 16, "unconsumed message pointer"),
        (rounds[-1], 1 << 5, "chained all full prefix and joined blocks"),
    ]:
        data = bytearray(image.data)
        struct.pack_into("<I", data, pc - image.base + 4 * i, words[i] ^ mask)
        with tempfile.TemporaryDirectory() as directory:
            candidate = Path(directory) / "altered-continuation"
            candidate.write_bytes(data)
            try:
                check((candidate, bits, 0, True))
            except ValueError as err:
                require(error in str(err), f"unexpected mutation result: {err}")
            else:
                raise AssertionError(f"accepted alteration to {error}")
    print(
        f"Rejected SHA-{bits} message-offset and compression-operand mutations",
        flush=True,
    )


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("binary", type=Path)
    p.add_argument("--bits", type=int, choices=(256, 512))
    p.add_argument("--jobs", type=int, default=1)
    p.add_argument("--self-test", action="store_true")
    a = p.parse_args()
    image = Image(a.binary.read_bytes())
    require(a.jobs >= 1, "jobs must be positive")
    for bits in [a.bits] if a.bits else [256, 512]:
        high = 305 if bits == 256 else 353
        tasks = [
            (a.binary, bits, q, partial)
            for q in range(high // (bits // 4) + 1)
            for partial in [False, True]
            if partial or q
        ]
        if a.jobs == 1:
            for task in tasks:
                check(task)
        else:
            with ProcessPoolExecutor(a.jobs) as pool:
                list(pool.map(check, tasks))
        print(
            f"SHA-{bits} continued: {len(tasks)} prefix classes, every valid context and segmented message length",
            flush=True,
        )
        if a.self_test:
            mutations(a.binary, image, bits)
    print("Mach-O SHA-256", hashlib.sha256(image.data).hexdigest())
