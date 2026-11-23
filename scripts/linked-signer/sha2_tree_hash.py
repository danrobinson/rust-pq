# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Compare linked SHA-2 seed setup, short tweakable hashes and two-child hashes to SHA rounds."""

import argparse
import hashlib
import struct
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    Image,
    STACK,
    KEY,
    RESULT,
    RETURN,
    angr,
    c,
    objects,
    clobber_scratch,
    blob,
    equal,
    integer,
    load,
    put,
    require,
    wrbytes,
)
from segmented import Compression
import arm_vector_ir

ADDRESS, LEFT, RIGHT = KEY + 256, KEY + 512, KEY + 768


def zeros(count):
    return c.BVV(0, 8 * count)


def seed_record(n, seed, h256, h512):
    # At width 32 the measured Rust ABI stores the equally sized public seed
    # before the SHA-256 words. At widths 16 and 24 their order is reversed.
    sha256_words = c.Concat(*(word.reversed for word in h256))
    sha512_words = c.Concat(*(word.reversed for word in h512))
    return (
        c.Concat(sha512_words, seed, sha256_words)
        if n == 32
        else c.Concat(sha512_words, sha256_words, seed)
    )


def verify(path, image, n, operation):
    _, _, _, _, hooks = objects(path, image, n, "s", "sha2")
    stem = {"prefix": b"8seed_ctx", "short": b"11thash_short", "pair": b"10thash_pair"}[
        operation
    ]
    pc, words = image.function(
        b"6slhdsa4hash" + stem + f"Kj{n:x}_EB4_".encode(), b"6slhdsa"
    )
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    state = project.factory.blank_state(
        addr=pc,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    state.regs.sp, state.regs.lr, state.regs.x8 = STACK, RETURN, RESULT
    sha256 = Compression(16, None)
    sha512 = Compression(32, None)
    seed = blob("PK_seed", n)
    if operation == "prefix":
        state.regs.x0 = KEY
        wrbytes(state, KEY, seed)
        h256 = sha256.block(sha256.initial, c.Concat(seed, zeros(64 - n)))
        h512 = sha512.block(sha512.initial, c.Concat(seed, zeros(128 - n)))
        expected = seed_record(n, seed, h256, h512)
    else:
        state.regs.x0, state.regs.x1, state.regs.x2, state.regs.x3 = (
            KEY,
            ADDRESS,
            LEFT,
            (RIGHT if operation == "pair" else n),
        )
        h256 = [c.BVS("SHA256_seed_word", 32) for i in range(8)]
        h512 = [c.BVS("SHA512_seed_word", 64) for i in range(8)]
        wrbytes(state, KEY, seed_record(n, seed, h256, h512))
        tree = c.BVS("tree", 64)
        layer, typ, keypair, w2, w3 = [
            c.BVS(name, 32) for name in ("layer", "type", "keypair", "word2", "word3")
        ]
        for off, width, val in [
            (0, 8, tree),
            (8, 4, layer),
            (12, 4, typ),
            (16, 4, keypair),
            (20, 4, w2),
            (24, 4, w3),
        ]:
            put(state, ADDRESS + off, val, width)
        compressed = c.Concat(layer[7:0], tree, typ[7:0], keypair, w2, w3)
        left, right = blob("left", n), blob("right", n)
        wrbytes(state, LEFT, left)
        wrbytes(state, RIGHT, right)
        msg = (
            c.Concat(compressed, left, right)
            if operation == "pair"
            else c.Concat(compressed, left)
        )
        wide = operation == "pair" and n != 16
        width = 128 if wide else 64
        msglen = msg.size() // 8
        tail = c.Concat(
            msg,
            c.BVV(0x80, 8),
            zeros(width - msglen - 3),
            c.BVV(8 * (width + msglen), 16),
        )
        new = (sha512 if wide else sha256).block(h512 if wide else h256, tail)
        expected = c.Concat(*new).get_bytes(0, n)
    sha256.hooks(project, path, pc, words)
    sha512.hooks(project, path, pc, words)
    saved = [getattr(state.regs, f"x{i}") for i in range(18, 30)]
    simd = [getattr(state.regs, f"q{i}")[63:0] for i in range(8, 16)]

    def access(st, kind):
        if not st.globals.get("native", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        ranges = [(STACK - 2048, 2048), (RESULT, expected.size() // 8)]
        if kind == "read":
            ranges.extend(
                [
                    (KEY, n if operation == "prefix" else 96 + n),
                    (ADDRESS, 28),
                    (LEFT, n),
                    (RIGHT, n),
                    image.sections[b"__const"][:2],
                ]
            )
        require(
            any(a <= ptr and ptr + size <= a + length for a, length in ranges),
            "SHA-2 tree hash memory extent",
        )

    for kind in ("read", "write"):
        state.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )
    todo = [(state, 0)]
    completed = 0
    while todo:
        st, steps = todo.pop()
        require(steps < 1000, "SHA-2 tree hash execution bound")
        st.globals["native"] = False
        if st.addr == RETURN:
            require(st.solver.satisfiable(), "infeasible SHA tree hash")
            equal(
                st,
                load(st, RESULT, expected.size() // 8),
                expected,
                "SHA tree hash result",
            )
            equal(st, st.regs.sp, STACK, "restored SHA tree hash stack")
            for i, val in enumerate(saved, 18):
                equal(
                    st,
                    getattr(st.regs, f"x{i}"),
                    val,
                    "preserved SHA tree hash register",
                )
            for i, val in enumerate(simd, 8):
                equal(
                    st,
                    getattr(st.regs, f"q{i}")[63:0],
                    val,
                    "preserved SHA tree hash vector",
                )
            completed += 1
            continue
        if hooks.get(st.addr) == "copy":
            require(operation == "short", "unexpected SHA tree hash copy")
            equal(st, st.regs.x1, LEFT, "short hash message pointer")
            equal(st, st.regs.x2, n, "short hash message length")
            dst = integer(st, st.regs.x0)
            require(STACK - 2048 <= dst <= STACK - n, "short hash copy bounds")
            wrbytes(st, dst, load(st, LEFT, n))
            clobber_scratch(st)
            st.regs.pc = st.regs.lr
            todo.append((st, steps + 1))
            continue
        require(
            pc <= st.addr < pc + 4 * len(words),
            f"unexpected SHA tree hash exit {st.addr:#x}",
        )
        st.globals["native"] = True
        nx = project.factory.successors(st)
        require(
            nx.flat_successors and not nx.unconstrained_successors,
            "unresolved SHA tree hash transfer",
        )
        todo.extend((child, steps + 1) for child in nx.flat_successors)
    require(completed == 1, "missing SHA-2 tree hash return")
    print(
        f"SHA2-{n * 8} {operation}: all output bytes agree with the compression circuit",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "consumer"
        path.write_bytes(data)
        image = Image(data)
        for n in (16, 24, 32):
            for operation in (
                ["short", "pair"] if n == 16 else ["prefix", "short", "pair"]
            ):
                verify(path, image, n, operation)
        if args.self_test:
            pc, words = image.function(b"6slhdsa4hash10thash_pairKj10_EB4_", b"6slhdsa")
            i = next(j for j, w in enumerate(words) if w & 0xFFE0FC00 == 0x5E004000)
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + 4 * i, words[i] ^ 0x1000)
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, "pair")
            except ValueError as ex:
                require(
                    "SHA tree hash result" in str(ex), f"wrong mutation failure: {ex}"
                )
            else:
                raise AssertionError("accepted incorrect SHA round")
            print("Rejected incorrect SHA-256 tree hash round")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
