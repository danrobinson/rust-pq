# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check linked SHAKE XMSS signing and every authentication-vector growth branch."""

import argparse
import hashlib
import struct
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    Image,
    Driver,
    STACK,
    KEY,
    RESULT,
    RETURN,
    angr,
    c,
    objects,
    clobber_scratch,
    blob,
    chunks,
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


def verify(path, image, n, variant):
    row, param, _, _, hooks = objects(path, image, n, variant, "shake")
    model = Driver(row, param, "slh_sign_internal", "shake")
    model.constants_range = image.sections[b"__const"][:2]
    mono = f"Kj{n:x}_EB6_".encode()
    family = b"6slhdsa5shake"

    def function(stem):
        return image.function(family + stem + mono, family)

    pc, words = function(b"4xmss9xmss_sign")
    wots, _ = function(b"5batch4sign")
    node, _ = function(b"4xmss9xmss_node")
    digits, _ = image.function(
        f"4wots11wots_digitsKj{n:x}_EB4_".encode(), b"6slhdsa4wots"
    )
    hooks.update({wots: "wots", node: "node", digits: "digits"})
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
    for i, value in enumerate(
        [param, KEY + n, KEY, index.zero_extend(32), KEY + 2 * n, ADDRESS]
    ):
        setattr(s.regs, f"x{i}", value)
    s.regs.x8 = RESULT
    count = 2 * n + 3
    wots_sig = chunks("WOTS_signature", count * n)
    node_values = [blob("auth_node", n) for j in range(model.hp)]
    ds = blob("WOTS_digits", 4 * count)

    def access(st, kind):
        if not st.globals.get("in_driver", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        if kind == "read" and ADDRESS <= ptr and ptr + size <= ADDRESS + 28:
            return
        guard_access(st, kind, model)

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )
    paths = []
    todo = [(s, (), 0, 0)]
    while todo:
        st, schedule, height, steps = todo.pop()
        st.globals["in_driver"] = False
        require(steps < 500, "XMSS signing execution bound")
        if st.addr == RETURN:
            require(
                height == model.hp and schedule == ("digits", "wots"),
                "incomplete XMSS signature",
            )
            ptr = st.globals["sig"]
            cap, _, _ = st.globals["allocations"][str(ptr)]
            require(
                set(st.globals["allocations"]) == {str(ptr)},
                "XMSS allocation ownership",
            )
            equal(st, unsigned(st, RESULT), cap, "XMSS capacity")
            equal(st, unsigned(st, RESULT + 8), ptr, "XMSS output pointer")
            equal(
                st, unsigned(st, RESULT + 16), model.layerlen, "XMSS signature length"
            )
            model.check_chunks(st, ptr, wots_sig)
            for j, node_value in enumerate(node_values):
                equal(
                    st,
                    load(st, ptr + (count + j) * n, n),
                    node_value,
                    "authentication path",
                )
            model.check_abi(st)
            require(st.solver.satisfiable(), "infeasible XMSS signing return")
            paths.append(st.globals.get("reserve_height"))
            continue
        name = hooks.get(st.addr)
        x = [getattr(st.regs, f"x{i}") for i in range(9)]

        def reg(i, value):
            equal(st, x[i], value, f"{name}: x{i}")

        if st.addr == pc or name is None:
            require(pc <= st.addr < pc + 4 * len(words), "unexpected XMSS signing exit")
            st.globals["in_driver"] = True
            nx = project.factory.successors(st)
            require(
                nx.flat_successors and not nx.unconstrained_successors,
                "unresolved XMSS signing control transfer",
            )
            todo.extend(
                (child, schedule, height, steps + 1) for child in nx.flat_successors
            )
            continue
        if name == "digits":
            require(schedule == (), "unexpected WOTS digit extraction")
            reg(0, KEY + n)
            model.vec(st, integer(st, x[8]), "digits", count, 4, [(0, ds)])
            schedule += ("digits",)
        elif name == "wots":
            require(schedule == ("digits",), "unexpected WOTS signing call")
            reg(0, KEY)
            reg(1, KEY + 2 * n)
            address = integer(st, x[2])
            equal(st, unsigned(st, address), tree, "WOTS tree")
            equal(st, unsigned(st, address + 8, 4), layer, "WOTS layer")
            equal(st, unsigned(st, address + 12, 4), 0, "WOTS address type")
            equal(st, unsigned(st, address + 16, 4), index, "WOTS keypair")
            equal(st, unsigned(st, address + 20), 0, "other WOTS address fields")
            reg(3, st.globals["digits"])
            reg(4, count)
            equal(st, load(st, x[3], count * 4), ds, "WOTS signing digits")
            model.vec(st, integer(st, x[8]), "sig", count * n, 1, wots_sig)
            schedule += ("wots",)
        elif name == "node":
            require(
                schedule == ("digits", "wots") and height < model.hp,
                "unexpected authentication node",
            )
            reg(0, KEY)
            reg(1, (c.LShR(index, height) ^ 1).zero_extend(32))
            reg(2, height)
            reg(3, KEY + 2 * n)
            reg(4, ADDRESS)
            wrbytes(st, model.workspace(st, x[8], n), node_values[height])
            height += 1
        elif name == "reserve":
            # A successful RawVec grows at least twofold. This suffices for all
            # remaining auth nodes, even if the incoming WOTS capacity was exact.
            used = (count + height - 1) * n
            reg(1, used)
            reg(2, n)
            reg(3, 1)
            reg(4, 1)
            desc = model.workspace(st, x[0], 24)
            old = st.globals["sig"]
            cap, _, _ = st.globals["allocations"][str(old)]
            equal(st, unsigned(st, desc + 8), old, "XMSS reserve pointer")
            equal(st, unsigned(st, desc + 16), used, "XMSS reserve length")
            equal(st, unsigned(st, desc), cap, "XMSS reserve capacity")
            equal(
                st,
                c.And(c.UGE(cap, used), c.ULT(cap, used + n)),
                True,
                "XMSS reserve threshold",
            )
            require(st.globals.get("reserve_height") is None, "repeated XMSS growth")
            data = [
                (i, load(st, old + i, min(128, used - i))) for i in range(0, used, 128)
            ]
            model.release(st, old, cap, 1)
            new = model.vec(st, desc, "sig", used, 1, data)
            newcap = st.globals["allocations"][str(new)][0]
            st.add_constraints(c.UGE(newcap, cap * 2))
            st.globals["reserve_height"] = height
        elif name == "free":
            model.release(st, integer(st, x[0]), x[1], integer(st, x[2]))
        else:
            raise ValueError(f"unknown XMSS signing callee {name}")
        clobber_scratch(st)
        st.regs.pc = st.regs.lr
        todo.append((st, schedule, height, steps + 1))
    require(
        len(paths) == model.hp + 1 and set(paths) == {None, *range(1, model.hp + 1)},
        "XMSS growth cases",
    )
    print(
        f"SHAKE-{n * 8}{variant}: XMSS signing checked across {len(paths)} capacity cases",
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
            for variant in "sf":
                verify(path, image, n, variant)
        if args.self_test:
            pc, words = image.function(b"4xmss9xmss_signKj10_EB6_", b"6slhdsa5shake")
            (i,) = [j for j, w in enumerate(words) if w == 0x52000121]
            altered = bytearray(data)
            struct.pack_into(
                "<I", altered, pc - image.base + 4 * i, 0x2A0903E1
            )  # mov w1,w9: omit sibling XOR
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, "s")
            except ValueError as ex:
                require("node: x1" in str(ex), f"wrong mutation failure: {ex}")
            else:
                raise AssertionError("accepted incorrect XMSS sibling")
            print("Rejected incorrect XMSS sibling index")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
