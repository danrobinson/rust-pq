# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check linked Apple SHA-256 chain schedules against the four-instruction round circuit."""

import argparse
import hashlib
import struct
import tempfile
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from driver import (
    Image,
    STACK,
    RETURN,
    KEY,
    angr,
    c,
    blob,
    put,
    wrbytes,
    load,
    integer,
    require,
)
from signer_inventory import import_stubs
from wots_chains import ImageEnv, agrees, return_call
from segmented import Compression
import arm_vector_ir

BLOCKS, START, END = KEY + 0x10000, KEY + 0x20000, KEY + 0x30000


def verify(path, image, n, bounds):
    env = ImageEnv(path, image, n)
    pc, words = image.function(
        b"4hash12chain_blocks" + f"Kj{n:x}_EB4_".encode(), b"6slhdsa"
    )
    (zero,) = [a for a, name in import_stubs(image, path).items() if name == "_bzero"]
    s = env.blank(pc)
    count = len(bounds)
    lengths = [c.BVS("available_bounds", 64) for _ in range(2)]
    for available in lengths:
        s.add_constraints(
            c.UGE(available, count), c.ULE(available, ((1 << 63) - 1) // 4)
        )
    for i, v in enumerate([KEY, BLOCKS, count, START, lengths[0], END, lengths[1]]):
        setattr(s.regs, f"x{i}", v)
    h = [c.BVS("initial_word", 32) for _ in range(8)]
    for i, v in enumerate(h):
        put(s, KEY + 4 * i, v, 4)
    hash = Compression(16, None)
    head = blob("common_header", 16)
    expected = []
    for i, (a, b) in enumerate(bounds):
        put(s, START + 4 * i, a, 4)
        put(s, END + 4 * i, b, 4)
        block = c.Concat(
            head,
            c.BVV(i, 16),
            blob("original_round", 4),
            blob("value", n),
            blob("tail", 42 - n),
        )
        wrbytes(s, BLOCKS + 64 * i, block)
        for t in range(a, b):
            src = c.Concat(
                block.get_bytes(0, 18), c.BVV(t, 32), block.get_bytes(22, 42)
            )
            digest = c.Concat(*hash.block(h, src)).get_bytes(0, n)
            block = c.Concat(
                src.get_bytes(0, 22), digest, src.get_bytes(22 + n, 42 - n)
            )
        expected.append(block)
    hash.hooks(env.project, path, pc, words)
    regs = [getattr(s.regs, f"x{i}") for i in range(18, 30)]
    simd = [getattr(s.regs, f"q{i}")[63:0] for i in range(8, 16)]

    def access(st, kind):
        if not st.globals.get("chain_native", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        ranges = [(STACK - 2048, 2048), (BLOCKS, 64 * count)]
        if kind == "read":
            ranges.extend([(KEY, 32), (START, 4 * count), (END, 4 * count), env.const])
        require(
            any(a <= ptr and ptr + size <= a + l for a, l in ranges),
            "chain memory extent",
        )

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )
    steps = 0
    while s.addr != RETURN:
        steps += 1
        require(steps < 400000, "chain execution bound")
        s.globals["chain_native"] = False
        if s.addr == zero:
            ptr, size = integer(s, s.regs.x0), integer(s, s.regs.x1)
            require(
                integer(s, s.regs.sp) <= ptr <= STACK - size and size == 640,
                "zero slots extent",
            )
            wrbytes(s, ptr, c.BVV(0, 8 * size))
            return_call(s)
            continue
        require(
            pc <= s.addr < pc + 4 * len(words), f"unexpected SHA chain exit {s.addr:#x}"
        )
        s.globals["chain_native"] = True
        nx = env.project.factory.successors(s)
        require(
            len(nx.flat_successors) == 1 and not nx.unconstrained_successors,
            f"unresolved chain control {s.addr:#x}",
        )
        s = nx.flat_successors[0]
    s.globals["chain_native"] = False
    for i, v in enumerate(expected):
        agrees(s, load(s, BLOCKS + 64 * i, 64), v, f"chain {i} result")
    agrees(s, s.regs.sp, STACK, "restored stack")
    for i, v in enumerate(regs, 18):
        agrees(s, getattr(s.regs, f"x{i}"), v, "preserved register")
    for i, v in enumerate(simd, 8):
        agrees(s, getattr(s.regs, f"q{i}")[63:0], v, "preserved vector")
    require(s.solver.satisfiable(), "vacuous chain return")
    print(n, count, steps, flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("binary", type=Path)
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--width", type=int, choices=(16, 24, 32))
    p.add_argument("--slots", type=int)
    p.add_argument("--rounds", type=int, choices=(1, 15))
    a = p.parse_args()
    data = a.binary.read_bytes()
    image = Image(data)
    for width in [a.width] if a.width else (16, 24, 32):
        for rounds in [a.rounds] if a.rounds else (1, 15):
            verify(a.binary, image, width, [(0, rounds)] * (a.slots or (2 * width + 3)))
    if a.self_test:
        pc, words = image.function(b"4hash12chain_blocksKj10_EB4_", b"6slhdsa")
        # Mutate the shared precomputation of SHA256H over the first four rounds.
        index = next(i for i, w in enumerate(words) if w & 0xFFE0FC00 == 0x5E004000)
        altered = bytearray(data)
        struct.pack_into(
            "<I", altered, pc - image.base + index * 4, words[index] ^ 0x1000
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "consumer"
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, [(0, 1)] * 4)
            except ValueError as exc:
                require(
                    "chain 0 result" in str(exc), f"unexpected mutation failure: {exc}"
                )
            else:
                raise AssertionError("accepted an incorrect native SHA chain round")
        print("Rejected a mutated round in the SHA256 chain scheduler")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
