# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Follow each linked XMSS authentication climb for arbitrary indices and signature bytes."""

import argparse
import hashlib
import struct
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    Image,
    Driver,
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
    unsigned,
    wrbytes,
    guard_access,
)

ADDRESS = KEY + 256
SIGNATURE = 0x21000000


def verify(path, image, n, variant, family):
    row, param, _, _, hooks = objects(path, image, n, variant, family)
    shake = family == "shake"
    model = Driver(row, param, "slh_sign_internal", family)
    model.constants_range = image.sections[b"__const"][:2]
    mono = f"Kj{n:x}_EB{6 if shake else 4}_".encode()
    crate = b"6slhdsa5shake" if shake else b"6slhdsa"

    def function(name):
        return image.function(crate + name + mono, crate)

    pc, words = function(b"4xmss16xmss_pk_from_sig")
    pair, _ = function(b"4hash10thash_pair")
    wots, _ = function(b"5batch7recover" if shake else b"4wots16wots_pk_from_sig")
    digits, _ = image.function(
        f"4wots11wots_digitsKj{n:x}_EB4_".encode(), b"6slhdsa4wots"
    )
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    s = project.factory.blank_state(
        addr=pc,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    model.start(s)
    tree = c.BVS("tree_coordinate", 64)
    layer = c.BVS("layer", 32)
    index = c.BVS("leaf_index", 32)
    s.add_constraints(c.ULT(index, 1 << model.hp))
    put(s, ADDRESS, tree, 8)
    put(s, ADDRESS + 8, layer, 4)
    seed_address = KEY + 512
    args = [
        index.zero_extend(32),
        SIGNATURE,
        model.layerlen,
        KEY,
        seed_address,
        ADDRESS,
    ]
    args = [param, *args] if shake else [RESULT, model.hp, *args]
    for i, value in enumerate(args):
        setattr(s.regs, f"x{i}", value)
    s.regs.x8 = RESULT
    count = 2 * n + 3
    ds = blob("WOTS_digits", 4 * count)
    roots = [blob("recovered_node", n) for j in range(model.hp + 1)]
    auth = [blob("authentication_node", n) for j in range(model.hp)]
    for j, value in enumerate(auth):
        wrbytes(s, SIGNATURE + (count + j) * n, value)

    def access(st, kind):
        if not st.globals.get("in_driver", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        if kind == "read" and any(
            a <= ptr and ptr + size <= b
            for a, b in [
                (ADDRESS, ADDRESS + 28),
                (SIGNATURE, SIGNATURE + model.layerlen),
            ]
        ):
            return
        # The indirect result is an n-byte node and KEY is one n-byte message.
        # The general signing driver uses a larger Vec descriptor and a full SK.
        guard_access(st, kind, model, result_size=n, key_size=n)

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )

    def address_fields(st, p, values):
        for off, size, val in zip((0, 8, 12, 16, 20, 24), (8, 4, 4, 4, 4, 4), values):
            equal(
                st,
                unsigned(st, p + off, size),
                val,
                "XMSS recovery address " + str(off),
            )

    todo = [s]
    for height in range(-1, model.hp + 1):
        stop = defaultdict(list)
        terminal = 0
        reached = set()
        blocks = 0
        while todo:
            st = todo.pop()
            blocks += 1
            require(blocks < 400, "XMSS recovery stage execution bound")
            st.globals["in_driver"] = False
            dest = st.addr
            x = [getattr(st.regs, f"x{i}") for i in range(9)]

            def reg(i, value):
                equal(st, x[i], value, f"XMSS recovery x{i}")

            if dest == RETURN:
                require(
                    height == model.hp and not st.globals["allocations"],
                    "XMSS returned early or leaked digits",
                )
                equal(st, load(st, RESULT, n), roots[-1], "XMSS root output")
                model.check_abi(st)
                require(st.solver.satisfiable(), "infeasible XMSS root")
                terminal += 1
                continue
            if dest == digits and shake:
                require(
                    height == -1 and not st.globals.get("digits"),
                    "unexpected WOTS digits",
                )
                reg(0, KEY)
                model.vec(st, integer(st, x[8]), "digits", count, 4, [(0, ds)])
            elif dest == wots:
                require(height == -1, "unexpected WOTS recovery")
                reg(0, SIGNATURE)
                reg(1, model.layerlen)
                if shake:
                    reg(2, seed_address)
                    address_fields(st, integer(st, x[3]), (tree, layer, 0, index, 0, 0))
                    reg(4, st.globals["digits"])
                    reg(5, count)
                    equal(st, load(st, x[4], count * 4), ds, "WOTS recovery digits")
                else:
                    reg(2, KEY)
                    reg(3, seed_address)
                    address_fields(st, integer(st, x[4]), (tree, layer, 0, index, 0, 0))
                wrbytes(st, model.workspace(st, x[8], n), roots[0])
            elif dest == pair:
                require(0 <= height < model.hp, "unexpected parent hash")
                reg(0, seed_address)
                address_fields(
                    st,
                    integer(st, x[1]),
                    (tree, layer, 2, 0, height + 1, c.LShR(index, height + 1)),
                )
                odd = index[height:height] == 1
                left, right = load(st, x[2], n), load(st, x[3], n)
                equal(
                    st,
                    left,
                    c.If(odd, auth[height], roots[height]),
                    "left XMSS hash operand",
                )
                equal(
                    st,
                    right,
                    c.If(odd, roots[height], auth[height]),
                    "right XMSS hash operand",
                )
                require(st.solver.satisfiable(), "infeasible parent hash")
                reached.add(integer(st, index[height:height]))
                wrbytes(st, model.workspace(st, x[8], n), roots[height + 1])
            elif hooks.get(dest) == "free":
                model.release(st, integer(st, x[0]), x[1], integer(st, x[2]))
            else:
                require(
                    pc <= dest < pc + 4 * len(words),
                    f"unexpected XMSS recovery exit {dest:#x}",
                )
                st.globals["in_driver"] = True
                nxt = project.factory.successors(st)
                require(
                    nxt.flat_successors and not nxt.unconstrained_successors,
                    "unresolved XMSS recovery control flow",
                )
                todo.extend(nxt.flat_successors)
                continue
            clobber_scratch(st)
            st.regs.pc = st.regs.lr
            if dest in (wots, pair):
                stop[st.addr].append(st)
            else:
                todo.append(st)
        if height == model.hp:
            require(terminal == 1 and not stop, "missing XMSS return")
        else:
            require(len(stop) == 1 and not terminal, "inconsistent XMSS call returns")
            states = next(iter(stop.values()))
            if height < 0:
                require(len(states) == 1, "missing WOTS result")
                todo = states
            else:
                require(
                    reached == {0, 1} and len(states) == 2,
                    "missing left/right sibling choice",
                )
                merged, _, _ = states[0].merge(states[1])
                todo = [merged]
    print(
        f"{family}-{n * 8}{variant}: checked ordered XMSS recovery at every height",
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
        for family in ("shake", "sha2"):
            for n in (16, 24, 32):
                for variant in "sf":
                    verify(path, image, n, variant, family)
        if args.self_test:
            pc, words = image.function(
                b"4xmss16xmss_pk_from_sigKj10_EB6_", b"6slhdsa5shake"
            )
            (i,) = [j for j, w in enumerate(words) if w == 0x3707FD33]
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + 4 * i, 0x3607FD33)
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, "s", "shake")
            except ValueError as ex:
                require(
                    "left XMSS hash operand" in str(ex), f"wrong mutation failure: {ex}"
                )
            else:
                raise AssertionError("accepted reversed XMSS children")
            print("Rejected reversed XMSS authentication hash")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
