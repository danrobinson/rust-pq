# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the Algorithm 9 recursion equations in three linked SHAKE XMSS node bodies."""

import argparse
import hashlib
import struct
import sys
from pathlib import Path

sys.dont_write_bytecode = True

from driver import (
    angr,
    c,
    Image,
    blob,
    equal,
    integer,
    load,
    put,
    require,
    unsigned,
    wrbytes,
    STACK,
    KEY,
    RESULT,
    RETURN,
    clobber_scratch,
)

PUBLIC_SEED = KEY + 128
ADDRESS = KEY + 256


def verify_node(image: Image, n):
    family = b"6slhdsa5shake"
    suffix = f"Kj{n:x}_EB6_".encode()
    node, words = image.function(b"4xmss9xmss_node" + suffix, family)
    keygen, _ = image.function(b"5batch6keygen" + suffix, family)
    pair, _ = image.function(b"4hash10thash_pair" + suffix, family)
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    s = project.factory.blank_state(
        addr=node,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    index, height, layer = [c.BVS(name, 32) for name in ("index", "height", "layer")]
    tree = c.BVS("tree", 64)
    put(s, ADDRESS, tree, 8)
    put(s, ADDRESS + 8, layer, 4)
    s.regs.sp, s.regs.lr, s.regs.x8 = STACK, RETURN, RESULT
    s.regs.x0, s.regs.x3, s.regs.x4 = KEY, PUBLIC_SEED, ADDRESS
    s.regs.x1, s.regs.x2 = index.zero_extend(32), height.zero_extend(32)
    # All FIPS rows have subtree height <= 9. At every recursive step valid
    # children remain within the 512 leaves of that maximal-height subtree.
    s.add_constraints(c.ULE(height, 9), c.ULT(index, c.LShR(c.BVV(512, 32), height)))
    saved = [getattr(s.regs, f"x{i}") for i in range(18, 30)]
    vectors = [getattr(s.regs, f"q{i}")[63:0] for i in range(8, 16)]
    children = [blob("child", n), blob("child", n)]
    leaf, parent = blob("WOTS_public_key", n), blob("tree_hash", n)

    def watch(st, kind):
        address = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        raw_size = getattr(st.inspect, f"mem_{kind}_length")
        size = (
            getattr(st.inspect, f"mem_{kind}_expr").size() // 8
            if raw_size is None
            else integer(st, raw_size)
        )
        ranges = [(STACK - 256, STACK), (RESULT, RESULT + n)]
        if kind == "read":
            ranges.append((ADDRESS, ADDRESS + 28))
        require(
            any(a <= address and address + size <= b for a, b in ranges),
            "XMSS node memory extent",
        )

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: watch(st, k)
        )

    def address_fields(st, address, fields):
        for off, size, val in zip((0, 8, 12, 16, 20, 24), (8, 4, 4, 4, 4, 4), fields):
            equal(
                st,
                unsigned(st, address + off, size),
                val,
                "XMSS address field " + str(off),
            )

    todo = [(s, (), 0)]
    terminals = []
    while todo:
        st, trace, steps = todo.pop()
        require(steps < 100, "XMSS recursion equation did not terminate")
        pc = st.addr
        x = [getattr(st.regs, f"x{i}") for i in range(9)]

        def reg(i, val):
            equal(st, x[i], val, "XMSS node x" + str(i))

        if pc == RETURN:
            require(
                trace in (("keygen",), ("left", "right", "pair")),
                "invalid XMSS node equation",
            )
            base = trace == ("keygen",)
            equal(st, height == 0, base, "XMSS recursion base")
            equal(st, load(st, RESULT, n), leaf if base else parent, "XMSS node result")
            equal(st, st.regs.sp, STACK, "XMSS restored sp")
            for i, val in enumerate(saved, 18):
                equal(st, getattr(st.regs, f"x{i}"), val, "XMSS preserved register")
            for i, val in enumerate(vectors, 8):
                equal(st, getattr(st.regs, f"q{i}")[63:0], val, "XMSS preserved vector")
            require(st.solver.satisfiable(), "infeasible XMSS case")
            terminals.append(trace)
            continue
        if pc in (keygen, pair) or (steps and pc == node):
            if pc == node:
                side = len(trace)
                require(trace in ((), ("left",)), "unexpected recursive invocation")
                reg(0, KEY)
                reg(1, (2 * index + side).zero_extend(32))
                reg(2, (height - 1).zero_extend(32))
                reg(3, PUBLIC_SEED)
                reg(4, ADDRESS)
                equal(
                    st,
                    c.ULT(x[2], height.zero_extend(32)),
                    True,
                    "recursive height strictly decreases",
                )
                equal(
                    st,
                    c.ULT(x[1], c.LShR(c.BVV(512, 64), x[2])),
                    True,
                    "valid recursive index",
                )
                require(
                    STACK - 256 <= integer(st, x[8]) <= STACK - n,
                    "recursive output frame",
                )
                output, event = children[side], ("left", "right")[side]
            elif pc == keygen:
                require(trace == (), "unexpected WOTS key generation")
                reg(0, KEY)
                reg(1, PUBLIC_SEED)
                reg(8, RESULT)
                address_fields(st, integer(st, x[2]), (tree, layer, 0, index, 0, 0))
                output, event = leaf, "keygen"
            else:
                require(trace == ("left", "right"), "hash before children")
                reg(0, PUBLIC_SEED)
                reg(8, RESULT)
                address_fields(
                    st, integer(st, x[1]), (tree, layer, 2, 0, height, index)
                )
                for i, child in enumerate(children, 2):
                    equal(st, load(st, x[i], n), child, "ordered XMSS children")
                output, event = parent, "pair"
            wrbytes(st, x[8], output)
            clobber_scratch(st)
            st.regs.pc = st.regs.lr
            todo.append((st, (*trace, event), steps + 1))
            continue
        require(node <= pc < node + len(words) * 4, "unexpected XMSS node exit")
        nxt = project.factory.successors(st)
        require(
            nxt.flat_successors and not nxt.unconstrained_successors,
            "unresolved XMSS control flow",
        )
        todo.extend((child, trace, steps + 1) for child in nxt.flat_successors)
    require(
        set(terminals) == {("keygen",), ("left", "right", "pair")}
        and len(terminals) == 2,
        "missing XMSS recursion equation",
    )
    print(f"SHAKE-{n * 8} XMSS node: leaf and decreasing recursive case", flush=True)


def mutations(image):
    node, words = image.function(b"4xmss9xmss_nodeKj10_EB6_", b"6slhdsa5shake")
    for old, new, expected in [
        (0x51000442, 0x51000042, "XMSS node x2"),
        (0x910043E3, 0x910003E3, "ordered XMSS children"),
    ]:
        (pos,) = [i for i, w in enumerate(words) if w == old]
        data = bytearray(image.data)
        struct.pack_into("<I", data, node - image.base + 4 * pos, new)
        try:
            verify_node(Image(data), 16)
        except ValueError as ex:
            require(expected in str(ex), f"unexpected mutation failure: {ex}")
        else:
            raise ValueError("accepted mutated XMSS recursion")
        print(f"Rejected XMSS mutation {old:#010x} ({expected})", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    image = Image(data)
    for width in (16, 24, 32):
        verify_node(image, width)
    if args.self_test:
        mutations(image)
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
