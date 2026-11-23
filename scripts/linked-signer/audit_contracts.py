"""Regression checks for native proof memory regions and supplemental VEX operations."""

import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True

from arm_vector_ir import irop
from driver import (
    Driver,
    HEAP,
    KEY,
    RESULT,
    STACK,
    STRIDE,
    angr,
    c,
    guard_access,
    require,
)


def reject(action, expected):
    try:
        action()
    except ValueError as error:
        require(expected in str(error), f"unexpected rejection: {error}")
        return
    raise ValueError("invalid access accepted: " + expected)


def memory_regions():
    model = SimpleNamespace(n=16, param=0x10000, constants_range=(0x20000, 8))
    state = angr.SimState(arch="aarch64")
    state.globals["in_driver"] = True
    state.globals["serial"] = 1
    state.globals["allocations"] = {}
    address = HEAP + STRIDE

    def access(kind, ptr):
        setattr(state.inspect, f"mem_{kind}_address", ptr)
        setattr(state.inspect, f"mem_{kind}_length", 8)
        guard_access(state, kind, model, result_size=16, key_size=16)

    access("write", RESULT + 8)
    reject(lambda: access("write", RESULT + 16), "out-of-contract")
    access("read", KEY + 8)
    reject(lambda: access("read", KEY + 16), "out-of-contract")
    state.regs.sp = STACK - 32
    Driver.workspace(state, STACK - 32, 32)
    reject(lambda: Driver.workspace(state, STACK - 40, 32), "outside stack frame")
    state.globals["allocations"] = {str(address): (c.BVV(4, 64), 4, "digits")}
    Driver.live_bytes(state, address, 16)
    reject(
        lambda: Driver.argument_bytes(state, address + 12, 8), "exceeds live allocation"
    )
    state.globals["allocations"] = {}
    reject(lambda: Driver.argument_bytes(state, address + 4, 4), "retired allocation")


def vector_operations():
    value = c.BVS("input", 128)
    solver = c.Solver()

    def check(op, expected, *args):
        actual = irop.operations["Iop_" + op].calculate(value, *args)
        require(not solver.satisfiable(extra_constraints=[actual != expected]), op)

    check("ZeroHI64ofV128", c.Concat(c.BVV(0, 64), value[63:0]))
    check("Reverse8sIn32_x4", c.Concat(*(value.get_byte(i ^ 3) for i in range(16))))
    for count in range(256):
        counts = [(count + 67 * j) % 256 for j in range(4)]
        # Upper 24 count bits are arbitrary. Every lane receives all low bytes.
        control = c.Concat(
            *(c.Concat(c.BVS("ignored", 24), c.BVV(n, 8)) for n in counts)
        )
        expected = []
        for lane, n in enumerate(counts):
            delta = n if n < 128 else n - 256
            for bit in range(31, -1, -1):
                source = bit - delta
                pos = 32 * (3 - lane) + source
                expected.append(value[pos:pos] if 0 <= source < 32 else c.BVV(0, 1))
        check("Sh32Ux4", c.Concat(*expected), control)


if __name__ == "__main__":
    memory_regions()
    vector_operations()
    print(
        "Passed memory-region controls and symbolic checks for all three supplemental VEX operations"
    )
