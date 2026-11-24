"""The live Apple SHA-256 scheduler registers and stack words at its loop cutpoints."""

from driver import c, load, integer, wrbytes

ENTRY = {16: 0x1AC, 24: 0x1C4, 32: 0x1B0}
CUTS = {16: (0x228, 0x218), 24: (0x248, 0x238), 32: (0x234, 0x224)}


def persistent(st, n):
    vector_live = {
        16: (0, 4, 8, 9, 10, 12, 13, 14, 15, 24, 25, 26, 27, 30, 31),
        24: (0, 1, 4, 8, 9, 10, 12, 13, 15, 22, 23, 25, 26, 27, 29, 30, 31),
        32: (0, 1, 4, 8, 9, 10, 11, 12, 13, 14, 15, 25, 26, 27, 29, 30, 31),
    }[n]
    stack_live = {
        16: (0, 16, 32, 48, 64, 80, 96, *range(560, 800, 16)),
        24: (0, 16, 32, 48, 64, 80, *range(544, 800, 16)),
        32: (0, 16, 32, 48, 64, *range(464, 736, 16)),
    }[n]
    scalar_live = (8, 9, 10, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 27, 28, 29)
    sp = integer(st, st.regs.sp)
    return (
        [(j, getattr(st.regs, f"x{j}")) for j in scalar_live],
        [(j, getattr(st.regs, f"q{j}")) for j in vector_live],
        [(off, load(st, sp + off, 16)) for off in stack_live],
    )


def set_context(st, scalar, vec, stack):
    for j, v in scalar:
        setattr(st.regs, f"x{j}", v)
    for j, v in vec:
        setattr(st.regs, f"q{j}", v)
    for off, v in stack:
        wrbytes(st, integer(st, st.regs.sp) + off, v)


def activate(context, n, head, a1, e1):
    """Update only the first-block cache in a scheduler context."""
    scalar, vec, stack = context
    flag = 11 if n == 32 else 12
    hot = {
        9: head.get_bytes(0, 8).reversed,
        10: head.get_bytes(8, 8).reversed,
        flag: c.BVV(1, 64),
    }
    offset = 64 if n == 16 else 48
    cache = {offset: e1.reversed, offset + 16: a1.reversed}
    return (
        [(j, hot.get(j, v)) for j, v in scalar],
        vec,
        [(o, cache.get(o, v)) for o, v in stack],
    )


def check_context(st, actual, expected, reason):
    from wots_chains import agrees

    for observed, wanted in zip(actual, expected):
        for (j, x), (k, y) in zip(observed, wanted):
            assert j == k
            agrees(st, x, y, f"{reason} at field {j}")
