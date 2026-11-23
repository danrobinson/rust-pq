# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check linked SHA-2 hypertree signing including inlined XMSS signature construction."""

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
    require,
    unsigned,
    wrbytes,
    guard_access,
)

SEED = KEY + 512


def verify(path, image, n, v, exact):
    row, param, _, _, hooks = objects(path, image, n, v, "sha2")
    model = Driver(row, param, "slh_sign_internal", "sha2")
    model.constants_range = image.sections[b"__const"][:2]

    def function(name):
        return image.function(b"6slhdsa" + name + f"Kj{n:x}_EB4_".encode(), b"6slhdsa")

    pc, words = function(b"2ht7ht_sign")
    for stem, name in [
        (b"4wots9wots_sign", "wots"),
        (b"4xmss9xmss_node", "node"),
        (b"4xmss16xmss_pk_from_sig", "recover"),
    ]:
        hooks[function(stem)[0]] = name
    hooks.pop(pc)
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
    count = 2 * n + 3
    tree = c.BVS("initial_tree", 64)
    leaf = c.BVS("initial_leaf", 32)
    s.add_constraints(c.ULT(leaf, 1 << model.hp))
    for i, val in enumerate([param, KEY, KEY + n, SEED, tree, leaf.zero_extend(32)]):
        setattr(s.regs, f"x{i}", val)
    roots = [model.sk[0]] + [blob("XMSS_root", n) for j in range(model.d - 1)]
    wots = [chunks("WOTS_signature", count * n) for j in range(model.d)]
    nodes = [
        [blob("auth_node", n) for j in range(model.hp)] for layer in range(model.d)
    ]
    layers = [
        wots[i] + [((count + h) * n, val) for h, val in enumerate(nodes[i])]
        for i in range(model.d)
    ]
    s.globals["ht_ret"] = RETURN
    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}",
            when=angr.BP_BEFORE,
            action=lambda st, k=kind: guard_access(st, k, model),
        )
    schedule = []
    for j in range(model.d):
        schedule += [("wots", j, 0)] + [("node", j, h) for h in range(model.hp)]
        if j + 1 < model.d:
            schedule.append(("recover", j, 0))
        schedule.append(("copy", j, 0))
    todo = [(s, 0, 0)]
    completed = 0
    while todo:
        st, event, steps = todo.pop()
        st.globals["in_driver"] = False
        require(steps < 4000, "SHA-2 hypertree execution bound")
        if st.addr == RETURN:
            require(event == len(schedule), "missing SHA-2 hypertree event")
            addr = st.globals["ht"]
            require(
                set(st.globals["allocations"]) == {str(addr)},
                "hypertree allocation ownership",
            )
            cap = st.globals["allocations"][str(addr)][0]
            equal(st, unsigned(st, RESULT), cap, "hypertree capacity")
            equal(st, unsigned(st, RESULT + 8), addr, "hypertree pointer")
            equal(
                st, unsigned(st, RESULT + 16), model.htlen, "hypertree returned length"
            )
            for j, layer in enumerate(layers):
                model.check_chunks(st, addr + j * model.layerlen, layer)
            require(st.solver.satisfiable(), "infeasible SHA-2 hypertree return")
            model.check_abi(st)
            completed += 1
            continue
        name = hooks.get(st.addr)
        x = [getattr(st.regs, f"x{i}") for i in range(9)]

        def reg(i, val):
            equal(st, x[i], val, f"SHA-2 {name} x{i}")

        if name in ("wots", "node", "recover", "copy"):
            require(
                event < len(schedule) and schedule[event][0] == name,
                "SHA-2 hypertree call order",
            )
            _, j, h = schedule[event]
            layer_tree = c.LShR(tree, j * model.hp)
            idx = (
                leaf
                if j == 0
                else c.LShR(tree, (j - 1) * model.hp)[model.hp - 1 : 0].zero_extend(
                    32 - model.hp
                )
            )

            def address(ptr, typ, keypair):
                a = integer(st, ptr)
                equal(st, unsigned(st, a), layer_tree, "SHA-2 subtree index")
                equal(st, unsigned(st, a + 8, 4), j, "SHA-2 layer number")
                equal(st, unsigned(st, a + 12, 4), typ, "SHA-2 address type")
                equal(st, unsigned(st, a + 16, 4), keypair, "SHA-2 address keypair")
                equal(st, unsigned(st, a + 20), 0, "SHA-2 address remainder")

            if name == "wots":
                equal(st, load(st, x[0], n), roots[j], "message to sign at layer")
                reg(1, KEY + n)
                reg(2, SEED)
                address(x[3], 0, idx)
                cap = count if exact else 1 << (count - 1).bit_length()
                model.vec(
                    st,
                    integer(st, x[8]),
                    "layer",
                    count * n,
                    1,
                    wots[j],
                    capacity=cap * n,
                )
            elif name == "node":
                reg(0, KEY + n)
                reg(1, (c.LShR(idx, h) ^ 1).zero_extend(32))
                reg(2, h)
                reg(3, SEED)
                address(x[4], 0, 0)
                wrbytes(st, model.workspace(st, x[8], n), nodes[j][h])
            elif name == "recover":
                reg(1, model.hp)
                reg(2, idx.zero_extend(32))
                reg(3, st.globals["layer"])
                reg(4, model.layerlen)
                model.check_chunks(st, integer(st, x[3]), layers[j])
                equal(st, load(st, x[5], n), roots[j], "XMSS recovery input root")
                reg(6, SEED)
                address(x[7], 0, 0)
                wrbytes(st, model.workspace(st, x[0], n), roots[j + 1])
            else:
                reg(0, st.globals["ht"] + j * model.layerlen)
                reg(1, st.globals["layer"])
                model.check_chunks(st, integer(st, x[1]), layers[j])
                model.call(st, "copy")
            event += 1
        elif name == "reserve":
            if integer(st, x[2]) == model.layerlen:
                model.call(st, "reserve")
            else:
                desc = model.workspace(st, x[0], 24)
                used = integer(st, x[1])
                reg(2, n)
                reg(3, 1)
                reg(4, 1)
                old = st.globals["layer"]
                cap = integer(st, st.globals["allocations"][str(old)][0])
                require(used == cap == count * n, "XMSS auth vector first growth")
                equal(st, unsigned(st, desc), cap, "XMSS capacity before growth")
                equal(st, unsigned(st, desc + 8), old, "XMSS pointer before growth")
                equal(st, unsigned(st, desc + 16), used, "XMSS length before growth")
                data = [
                    (i, load(st, old + i, min(128, used - i)))
                    for i in range(0, used, 128)
                ]
                model.release(st, old, cap, 1)
                model.vec(st, desc, "layer", used, 1, data, capacity=2 * cap)
        elif name == "free":
            model.call(st, "free")
        else:
            require(
                pc <= st.addr < pc + 4 * len(words), "unexpected SHA-2 hypertree target"
            )
            st.globals["in_driver"] = True
            nx = project.factory.successors(st)
            require(
                nx.flat_successors and not nx.unconstrained_successors,
                "unresolved SHA-2 hypertree transfer",
            )
            todo.extend((child, event, steps + 1) for child in nx.flat_successors)
            continue
        clobber_scratch(st)
        st.regs.pc = st.regs.lr
        todo.append((st, event, steps + 1))
    require(completed == 1, "missing SHA-2 hypertree return")
    print(
        f"SHA2-{n * 8}{v}: all {model.d} layers, WOTS capacity {'exact' if exact else 'geometric'}",
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
                for exact in (False, True):
                    verify(path, image, n, variant, exact)
        if args.self_test:
            pc, words = image.function(b"6slhdsa2ht7ht_signKj10_EB4_", b"6slhdsa")
            (i,) = [j for j, w in enumerate(words) if w == 0x54000162]
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + 4 * i, 0x54000168)
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, "s", False)
            except ValueError as ex:
                require(
                    "SHA-2 hypertree call order" in str(ex),
                    f"wrong mutation failure: {ex}",
                )
            else:
                raise AssertionError("accepted extra root recovery")
            print("Rejected redundant final-layer root recovery")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
