# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check linked Apple SHAKE tree hashing down to the exact padded Keccak permutation input."""

import argparse
import hashlib
import struct
import sys
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
    clobber_scratch,
    blob,
    equal,
    integer,
    load,
    put,
    require,
    wrbytes,
)
import arm_vector_ir  # Register the three vector operations absent from the lifter backend.

ADDRESS = KEY + 256
LEFT = KEY + 512
RIGHT = KEY + 768


def verify(image, n):
    family = b"6slhdsa5shake"
    pair = image.function(f"4hash10thash_pairKj{n:x}_EB6_".encode(), family)
    absorb = image.function(b"6Sponge6absorb", b"6slhdsa8shake256")
    finish = image.function(b"6Sponge6finish", b"6slhdsa8shake256")
    single, _ = image.function(b"parallel6single", b"6slhdsa8shake256")
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    s = project.factory.blank_state(
        addr=pair[0],
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    s.regs.sp, s.regs.lr, s.regs.x8 = STACK, RETURN, RESULT
    s.regs.x0, s.regs.x1, s.regs.x2, s.regs.x3 = KEY, ADDRESS, LEFT, RIGHT
    seed, left, right = [
        blob(label, n) for label in ("public_seed", "left_child", "right_child")
    ]
    for ptr, val in [(KEY, seed), (LEFT, left), (RIGHT, right)]:
        wrbytes(s, ptr, val)
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
        put(s, ADDRESS + off, val, width)
    message = c.Concat(
        seed, layer, c.BVV(0, 32), tree, typ, keypair, w2, w3, left, right
    )
    # 24-round Keccak-f uses 25 LE lanes. In memory these are already in
    # message byte order; the outer 64 capacity bytes are zero.
    padded = c.Concat(
        message,
        c.BVV(0x1F, 8),
        c.BVV(0, (134 - message.size() // 8) * 8),
        c.BVV(0x80, 8),
        c.BVV(0, 64 * 8),
    )
    output = blob("Keccak_result_in_memory", 200)
    saved = [getattr(s.regs, f"x{i}") for i in range(18, 30)]
    vec = [getattr(s.regs, f"q{i}")[63:0] for i in range(8, 16)]

    def access(st, kind):
        if not st.globals.get("native", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        regions = [(STACK - 4096, 4096), (RESULT, n)]
        if kind == "read":
            regions.extend(
                [
                    (KEY, n),
                    (LEFT, n),
                    (RIGHT, n),
                    (ADDRESS, 28),
                    image.sections[b"__const"][:2],
                ]
            )
        require(
            any(a <= ptr and ptr + size <= a + length for a, length in regions),
            "tree hash memory extent",
        )

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )
    count = 0
    todo = [(s, False, 0)]
    while todo:
        st, hashed, steps = todo.pop()
        require(steps < 1000, "tree hash execution bound")
        st.globals["native"] = False
        if st.addr == RETURN:
            require(
                hashed and st.solver.satisfiable(),
                "tree hash returned without permutation",
            )
            equal(
                st, load(st, RESULT, n), output.get_bytes(0, n), "truncated tree hash"
            )
            equal(st, st.regs.sp, STACK, "tree hash restored stack")
            for i, val in enumerate(saved, 18):
                equal(
                    st, getattr(st.regs, f"x{i}"), val, "tree hash preserved register"
                )
            for i, val in enumerate(vec, 8):
                equal(
                    st,
                    getattr(st.regs, f"q{i}")[63:0],
                    val,
                    "tree hash preserved vector",
                )
            # The normal path is straight-line for these fixed input lengths.
            # A concretization must not have excluded any symbolic input value.
            require(
                not c.Solver().satisfiable(
                    extra_constraints=[c.Not(c.And(*st.solver.constraints))]
                ),
                "tree hash terminal excludes admissible inputs",
            )
            count += 1
            continue
        if st.addr == single:
            require(not hashed, "extra tree hash permutation")
            ptr = integer(st, st.regs.x0)
            require(
                max(STACK - 4096, integer(st, st.regs.sp)) <= ptr <= STACK - 200,
                "tree hash state outside active frame",
            )
            equal(
                st,
                load(st, ptr, 200),
                padded,
                "full padded tree hash permutation input",
            )
            wrbytes(st, ptr, output)
            clobber_scratch(st)
            st.regs.pc = st.regs.lr
            todo.append((st, True, steps + 1))
            continue
        require(
            any(
                start <= st.addr < start + 4 * len(words)
                for start, words in [pair, absorb, finish]
            ),
            f"unexpected tree hash transfer {st.addr:#x}",
        )
        st.globals["native"] = True
        nx = project.factory.successors(st)
        require(
            nx.flat_successors and not nx.unconstrained_successors,
            "unresolved tree hash control flow",
        )
        todo.extend((child, hashed, steps + 1) for child in nx.flat_successors)
    require(count == 1, "missing tree hash result")
    print(
        f"SHAKE-{n * 8}: linked tree hash agrees with the FIPS padded permutation input",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    image = Image(data)
    for width in (16, 24, 32):
        verify(image, width)
    if args.self_test:
        pc, words = image.function(b"4hash10thash_pairKj10_EB6_", b"6slhdsa5shake")
        (i,) = [j for j, w in enumerate(words) if w == 0xAA1403E1]
        altered = bytearray(data)
        struct.pack_into("<I", altered, pc - image.base + 4 * i, 0xAA1503E1)
        try:
            verify(Image(altered), 16)
        except ValueError as ex:
            require(
                "full padded tree hash permutation input" in str(ex),
                f"wrong mutation failure: {ex}",
            )
        else:
            raise AssertionError("accepted duplicate left child")
        print("Rejected duplicate tree hash child")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
