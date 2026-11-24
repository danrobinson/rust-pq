# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the linked SHA-2 FORS signature constructor for all digest indices and address inputs."""

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
    equal,
    integer,
    load,
    put,
    require,
    unsigned,
    wrbytes,
    guard_access,
)
import arm_vector_ir

MD, SEED, ADDRESS = KEY + 256, KEY + 512, KEY + 768


def verify(path, image, n, v):
    row, param, _, _, hooks = objects(path, image, n, v, "sha2")
    model = Driver(row, param, "slh_sign_internal", "sha2")
    model.constants_range = image.sections[b"__const"][:2]

    def function(stem):
        return image.function(b"6slhdsa" + stem + f"Kj{n:x}_EB4_".encode(), b"6slhdsa")

    pc, words = function(b"4fors9fors_sign")
    hooks.pop(pc)
    hooks[function(b"4fors9fors_node")[0]] = "node"
    hooks[function(b"4hash11thash_short")[0]] = "secret"
    base, basewords = image.function(b"6slhdsa4util7base_2b", b"6slhdsa")
    hooks[base] = "indices"
    model.schedule = ("indices",)
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    st = project.factory.blank_state(
        addr=pc,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    model.start(st)
    for i, val in enumerate([param, MD, model.md, KEY, SEED, ADDRESS]):
        setattr(st.regs, f"x{i}", val)
    wrbytes(st, MD, model.digest.get_bytes(0, model.md))
    tree, layer, keypair = c.BVS("tree", 64), c.BVS("layer", 32), c.BVS("keypair", 32)
    for off, width, val in [
        (0, 8, tree),
        (8, 4, layer),
        (12, 4, 3),
        (16, 4, keypair),
        (20, 4, 0),
        (24, 4, 0),
    ]:
        put(st, ADDRESS + off, val, width)
    blocks = [blob("FORS_block", n) for i in range(model.k * (1 + model.a))]

    def access(s, kind):
        if not s.globals.get("in_driver", False):
            return
        ptr = integer(s, getattr(s.inspect, f"mem_{kind}_address"))
        size = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
        if kind == "read" and any(
            a <= ptr and ptr + size <= a + l for a, l in [(MD, model.md), (ADDRESS, 28)]
        ):
            return
        guard_access(s, kind, model)

    for kind in ("read", "write"):
        st.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda s, k=kind: access(s, k)
        )
    todo = [(st, 0, 0)]
    completed = 0
    while todo:
        s, event, steps = todo.pop()
        require(steps < 12000, "FORS execution bound")
        s.globals["in_driver"] = False
        if s.addr == s.globals.get("base_ret"):
            model.indices_return(s)
        if s.addr == RETURN:
            addr = s.globals["signature"]
            require(
                event == len(blocks) and set(s.globals["allocations"]) == {str(addr)},
                "incomplete FORS signature",
            )
            equal(
                s,
                unsigned(s, RESULT),
                s.globals["allocations"][str(addr)][0],
                "FORS capacity",
            )
            equal(s, unsigned(s, RESULT + 8), addr, "FORS pointer")
            equal(s, unsigned(s, RESULT + 16), model.forslen, "FORS signature length")
            model.check_chunks(
                s, addr, [(n * i, value) for i, value in enumerate(blocks)]
            )
            model.check_abi(s)
            require(s.solver.satisfiable(), "infeasible FORS return")
            completed += 1
            continue
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        name = hooks.get(s.addr)

        def reg(i, val):
            equal(s, x[i], val, f"FORS {name} x{i}")

        if name in ("secret", "node"):
            require(
                event < len(blocks) and s.globals["calls"] == ("indices",),
                "FORS call order",
            )
            i, pos = divmod(event, model.a + 1)
            digit = model.idx.get_bytes(4 * i, 4).reversed
            require((pos == 0) == (name == "secret"), "FORS secret/node position")
            if name == "secret":
                reg(0, SEED)
                a = integer(s, x[1])
                for off, size, val in [
                    (0, 8, tree),
                    (8, 4, layer),
                    (12, 4, 6),
                    (16, 4, keypair),
                    (20, 4, 0),
                    (24, 4, (i << model.a) + digit),
                ]:
                    equal(
                        s,
                        unsigned(s, a + off, size),
                        val,
                        "FORS secret address " + str(off),
                    )
                reg(2, KEY)
                reg(3, n)
                dest = x[8]
            else:
                h = pos - 1
                reg(1, KEY)
                reg(2, ((i << (model.a - h)) + (c.LShR(digit, h) ^ 1)).zero_extend(32))
                reg(3, h)
                reg(4, SEED)
                reg(5, ADDRESS)
                dest = x[0]
            wrbytes(s, model.workspace(s, dest, n), blocks[event])
            event += 1
            clobber_scratch(s)
        elif name in ("grow", "free"):
            model.call(s, name)
        elif name == "reserve":
            desc = model.workspace(s, x[0], 24)
            used = integer(s, x[1])
            reg(2, n)
            reg(3, 1)
            reg(4, 1)
            cap = integer(s, unsigned(s, desc))
            old = integer(s, unsigned(s, desc + 8))
            equal(s, unsigned(s, desc + 16), used, "FORS vector growth length")
            require(used <= cap < used + n, "FORS vector growth condition")
            data = []
            if used:
                require(old == s.globals["signature"], "FORS old allocation")
                data = [
                    (i, load(s, old + i, min(128, used - i)))
                    for i in range(0, used, 128)
                ]
                model.release(s, old, cap, 1)
            else:
                require(old == 1 and cap == 0, "FORS empty vector")
            model.vec(
                s, desc, "signature", used, 1, data, capacity=max(8, used + n, 2 * cap)
            )
            clobber_scratch(s)
        else:
            if name == "indices":
                model.call(s, name)
            require(
                pc <= s.addr < pc + 4 * len(words)
                or base <= s.addr < base + 4 * len(basewords),
                "unexpected SHA-2 FORS signing exit",
            )
            s.globals["in_driver"] = True
            nx = project.factory.successors(s)
            require(
                nx.flat_successors and not nx.unconstrained_successors,
                "unresolved FORS control flow",
            )
            todo.extend((child, event, steps + 1) for child in nx.flat_successors)
            continue
        s.regs.pc = s.regs.lr
        todo.append((s, event, steps + 1))
    require(completed == 1, "missing SHA-2 FORS signature return")
    print(
        f"SHA2-{n * 8}{v}: checked all {len(blocks)} FORS signature blocks", flush=True
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
            for v in "sf":
                verify(path, image, n, v)
        if args.self_test:
            pc, words = image.function(b"6slhdsa4fors9fors_signKj10_EB4_", b"6slhdsa")
            (i,) = [j for j, w in enumerate(words) if w == 0x52000108]
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + 4 * i, 0x2A0803E8)
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, "s")
            except ValueError as ex:
                require("FORS node x2" in str(ex), f"wrong mutation failure: {ex}")
            else:
                raise AssertionError("accepted incorrect sibling index")
            print("Rejected incorrect SHA-2 FORS sibling")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
