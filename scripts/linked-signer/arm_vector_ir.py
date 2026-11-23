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
    """USHL.4S uses each signed low byte as an unsigned-lane shift count."""

    _float = False

    @staticmethod
    def calculate(value, shifts):
        require(value.size() == shifts.size() == 128, "wrong USHL width")
        result = []
        for word, count in zip(value.chop(32), shifts.chop(32)):
            count = c.simplify(count[7:0])
            require(count.concrete, "expected static USHL count")
            delta = (count.concrete_value ^ 128) - 128
            result.append(word << delta if delta >= 0 else c.LShR(word, -delta))
        return c.Concat(*result)


irop.operations.setdefault("Iop_Sh32Ux4", UnsignedLaneShift())
