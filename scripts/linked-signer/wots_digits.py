# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the linked base-16 WOTS message and checksum digits for every message block."""

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
    equal,
    integer,
    load,
    require,
    unsigned,
    wrbytes,
    guard_access,
)


def verify(path, image, n):
    row, param, _, _, hooks = objects(path, image, n, "s", "shake")
    pc, words = image.function(
        f"4wots11wots_digitsKj{n:x}_EB4_".encode(), b"6slhdsa4wots"
    )
    base, basewords = image.function(b"6slhdsa4util7base_2b", b"6slhdsa")
    model = Driver(row, param, "slh_sign_internal", "shake")
    model.constants_range = image.sections[b"__const"][:2]
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
    st.regs.x0 = KEY
    st.regs.x8 = RESULT
    message = model.sk[0]
    length = 2 * n
    digits = [
        message[n * 8 - 1 - 4 * i : n * 8 - 4 - 4 * i].zero_extend(28)
        for i in range(length)
    ]
    # Verify the unrolled sum in the ring of 32-bit words. Replacing that
    # register by an arbitrary word after the equality check proves the
    # remaining checksum encoding for every value the sum might take.
    (position,) = [i for i, word in enumerate(words) if word == 0x4B081128]
    sum_pc = pc + 4 * position
    digit_sum = c.BVS("proved_digit_sum", 32)
    checksum = 15 * length - digit_sum
    expected = digits + [checksum[4 * j + 3 : 4 * j].zero_extend(28) for j in (2, 1, 0)]
    for kind in ("read", "write"):
        st.inspect.b(
            f"mem_{kind}",
            when=angr.BP_BEFORE,
            action=lambda s, k=kind: guard_access(s, k, model),
        )
    completed = 0
    todo = [(st, 0, 0)]
    while todo:
        s, phase, steps = todo.pop()
        require(steps < 1000, "WOTS digits execution bound")
        s.globals["in_driver"] = False
        if s.addr == RETURN:
            ptr = s.globals["message"]
            require(
                phase == 2 and set(s.globals["allocations"]) == {str(ptr)},
                "WOTS digits ownership",
            )
            equal(
                s,
                unsigned(s, RESULT),
                s.globals["allocations"][str(ptr)][0],
                "returned digit capacity",
            )
            equal(s, unsigned(s, RESULT + 8), ptr, "returned digit pointer")
            equal(s, unsigned(s, RESULT + 16), length + 3, "number of WOTS digits")
            for i, expected_digit in enumerate(expected):
                equal(
                    s,
                    unsigned(s, ptr + 4 * i, 4),
                    expected_digit,
                    "WOTS digit " + str(i),
                )
            model.check_abi(s)
            require(s.solver.satisfiable(), "infeasible WOTS digit return")
            completed += 1
            continue
        x = [getattr(s.regs, f"x{i}") for i in range(9)]

        def reg(i, value):
            equal(s, x[i], value, "WOTS digit x" + str(i))

        if s.addr == sum_pc:

            def terms(expr):
                if expr.op == "__add__":
                    return [term for arg in expr.args for term in terms(arg)]
                return [c.backends.z3.convert(c.simplify(expr)).sexpr()]

            require(
                sorted(terms(s.regs.w8))
                == sorted(term for digit in digits for term in terms(digit)),
                "unrolled sum of all message digits",
            )
            s.regs.w8 = digit_sum
            s.globals["checked_sum"] = True
        if s.addr == base:
            phase += 1
            require(phase <= 2, "extra radix conversion")
            reg(1, n if phase == 1 else 2)
            reg(2, 4)
            reg(3, length if phase == 1 else 3)
            if phase == 1:
                reg(0, KEY)
            else:
                require(s.globals.get("checked_sum"), "missing WOTS checksum sum")
                equal(
                    s, load(s, x[0], 2), (checksum << 4)[15:0], "encoded WOTS checksum"
                )
        name = hooks.get(s.addr)
        if name == "grow":
            region = "message" if phase == 1 else "checksum"
            desc = model.workspace(s, x[0], 24)
            old = integer(s, unsigned(s, desc + 8))
            used = integer(s, unsigned(s, desc + 16))
            equal(s, unsigned(s, desc), used, "full WOTS digit vector growth")
            data = []
            if used:
                require(old == s.globals[region], "growing incorrect WOTS digit vector")
                data = [(0, load(s, old, 4 * used))]
                model.release(s, old, 4 * used, 4)
            else:
                require(old == 4, "WOTS digit sentinel")
            model.vec(s, desc, region, used, 4, data, capacity=max(4, 2 * used))
        elif name == "reserve":
            desc = model.workspace(s, x[0], 24)
            reg(1, length)
            reg(2, 3)
            reg(3, 4)
            reg(4, 4)
            old = s.globals["message"]
            equal(s, unsigned(s, desc + 8), old, "WOTS append pointer")
            equal(s, unsigned(s, desc + 16), length, "WOTS append length")
            cap = s.globals["allocations"][str(old)][0]
            equal(s, unsigned(s, desc), cap, "WOTS append capacity")
            equal(s, c.ULT(cap, length + 3), True, "WOTS append requires growth")
            data = [(0, load(s, old, 4 * length))]
            model.release(s, old, cap * 4, 4)
            new = model.vec(s, desc, "message", length, 4, data)
            s.add_constraints(c.UGE(s.globals["allocations"][str(new)][0], length + 3))
        elif name == "copy":
            reg(0, s.globals["message"] + 4 * length)
            reg(1, s.globals["checksum"])
            reg(2, 12)
            wrbytes(s, x[0], load(s, x[1], 12))
        elif name == "free":
            model.release(s, integer(s, x[0]), x[1], integer(s, x[2]))
        else:
            require(
                pc <= s.addr < pc + 4 * len(words)
                or base <= s.addr < base + 4 * len(basewords),
                "unexpected WOTS digit exit",
            )
            s.globals["in_driver"] = True
            nx = project.factory.successors(s, extra_stop_points={sum_pc})
            require(
                nx.flat_successors and not nx.unconstrained_successors,
                "unresolved WOTS digit transfer",
            )
            todo.extend((child, phase, steps + 1) for child in nx.flat_successors)
            continue
        clobber_scratch(s)
        s.regs.pc = s.regs.lr
        todo.append((s, phase, steps + 1))
    require(completed == 1, "missing or duplicate WOTS digit return")
    print(
        f"WOTS-{n * 8}: all {length + 3} base-16 message and checksum digits",
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
        for width in (16, 24, 32):
            verify(path, image, width)
        if args.self_test:
            pc, words = image.function(b"4wots11wots_digitsKj10_EB4_", b"6slhdsa4wots")
            (i,) = [j for j, w in enumerate(words) if w == 0x5283C009]
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + 4 * i, 0x5283C209)
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16)
            except ValueError as ex:
                require(
                    "encoded WOTS checksum" in str(ex), f"wrong mutation failure: {ex}"
                )
            else:
                raise AssertionError("accepted altered WOTS checksum")
            print("Rejected altered WOTS checksum constant")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
