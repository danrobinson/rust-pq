"""Narrow bitvector semantics missing from the pinned VEX engine, used on Apple arm64."""

from driver import c, require
from angr.engines.vex.claripy import irop


class ZeroHigh64:
    """VEX Iop_ZeroHI64ofV128 retains bits 63:0 and clears bits 127:64."""

    _float = False

    @staticmethod
    def calculate(value):
        require(value.size() == 128, "wrong ZeroHI64 operand")
        return value[63:0].zero_extend(64)


irop.operations.setdefault("Iop_ZeroHI64ofV128", ZeroHigh64())


class Reverse8sIn32:
    """AArch64 REV32 byte order within each 32-bit word of a vector."""

    _float = False

    @staticmethod
    def calculate(value):
        require(value.size() == 128, "wrong REV32 operand")
        return c.Concat(*(word.reversed for word in value.chop(32)))


irop.operations.setdefault("Iop_Reverse8sIn32_x4", Reverse8sIn32())


class UnsignedLaneShift:
    """USHL uses the signed low byte of each count to shift an unsigned lane."""

    def __init__(self, width):
        self.width = width

    _float = False

    def calculate(self, value, shifts):
        require(value.size() == shifts.size() == 128, "wrong USHL width")
        result = []
        for word, count in zip(value.chop(self.width), shifts.chop(self.width)):
            count = c.simplify(count[7:0])
            require(count.concrete, "expected static USHL count")
            delta = (count.concrete_value ^ 128) - 128
            result.append(word << delta if delta >= 0 else c.LShR(word, -delta))
        return c.Concat(*result)


irop.operations.setdefault("Iop_Sh32Ux4", UnsignedLaneShift(32))
irop.operations.setdefault("Iop_Sh64Ux2", UnsignedLaneShift(64))


class NarrowUnsigned:
    """Narrow each lane by retaining its low half."""

    _float = False

    def __init__(self, width):
        self.width = width

    def calculate(self, value):
        require(value.size() == 128, "wrong narrow operand width")
        return c.Concat(
            *(lane[self.width // 2 - 1 : 0] for lane in value.chop(self.width))
        )


for width in (16, 32, 64):
    name = f"Iop_NarrowUn{width}to{width // 2}x{128 // width}"
    irop.operations.setdefault(name, NarrowUnsigned(width))
