"""Decode the two independent 64-bit lanes of the linked arm64 SHA3 leaf function."""

import struct
from image import require, sign_extend


def vector(word, regs, rc):
    d, n, m, a = word & 31, (word >> 5) & 31, (word >> 16) & 31, (word >> 10) & 31
    if word & 0xFFE08000 == 0xCE000000:  # EOR3
        expr = f"({regs[n]} ^^^ {regs[m]} ^^^ {regs[a]})"
    elif word & 0xFFE08000 == 0xCE200000:  # BCAX: n XOR (m AND NOT a)
        expr = f"({regs[n]} ^^^ ((~~~{regs[a]}) &&& {regs[m]}))"
    elif word & 0xFFE0FC00 == 0xCE608C00:  # RAX1
        expr = f"({regs[n]} ^^^ ({regs[m]}).rotateLeft 1)"
    elif word & 0xFFE00000 == 0xCE800000:  # XAR ROR imm6
        rot = (-((word >> 10) & 63)) % 64
        expr = f"(({regs[n]} ^^^ {regs[m]}).rotateLeft {rot})"
    elif word & 0xFFE0FC00 == 0x4EA01C00 and n == m:  # ORR (MOV)
        expr = regs[n]
    elif word & 0xFFE0FC00 == 0x6E201C00:  # EOR
        expr = f"({regs[n]} ^^^ {regs[m]})"
    elif word == 0x4D40CD40 and rc:  # LD1R {v0.2d}, [x10]
        expr = "rc"
    else:
        raise ValueError(f"unexpected round instruction {word:08x}")
    regs[d] = expr


def row_access(word, load):
    """Each 128-bit row is a pair of independent little-endian u64s, based at x0."""
    require((word >> 5) & 31 == 0, "unexpected state base")
    imm = (word >> 15) & 127
    if word & 0xFFC00000 == (0xAD400000 if load else 0xAD000000):
        idx = sign_extend(imm, 7)
        return [(idx, word & 31), (idx + 1, (word >> 10) & 31)]
    require(
        word & 0xFFC00000 == (0x3DC00000 if load else 0x3D800000),
        "unexpected state access",
    )
    return [((word >> 10) & 4095, word & 31)]


def decode(image):
    pc, words = image.function(b"4sha37permute")
    # Save/restore d8..d15 in the 64-byte stack frame. x0 holds the 400-byte matrix.
    require(
        words[:5] == [0x6DBC3BEF, 0x6D0133ED, 0x6D022BEB, 0x6D0323E9, 0xD2800008],
        "prologue or zero counter differs",
    )
    require(
        words[-5:] == [0x6D4323E9, 0x6D422BEB, 0x6D4133ED, 0x6CC43BEF, 0xD65F03C0],
        "epilogue or return differs",
    )
    registers = {}
    loaded = []
    table = None
    i = 5
    while words[i] & 0xFFE08000 != 0xCE000000:
        w = words[i]
        if w & 0x9F00001F == 0x90000009:  # ADRP x9; ADD x9,x9,#imm12
            add = words[i + 1]
            require(
                table is None and add & 0xFFC003FF == 0x91000129,
                "bad round table setup",
            )
            pages = sign_extend(((w >> 5 & 0x7FFFF) << 2) | (w >> 29 & 3), 21)
            va = ((pc + 4 * i) & ~4095) + 4096 * pages + (add >> 10 & 4095)
            table = list(struct.unpack("<24Q", image.read(b"__const", va, 192)))
            i += 2
        else:
            for row, reg in row_access(w, True):
                require(reg not in registers, "overwritten input register")
                registers[reg] = f"a[{row}]!"
                loaded.append((row, reg))
            i += 1
    require(
        sorted(row for row, _ in loaded) == list(range(25)) and table is not None,
        "incomplete inputs",
    )
    start = i
    counter = "old"
    rc_address = rc_load = False
    while words[i] != 0xF103011F:  # CMP x8,#192
        w = words[i]
        if w == 0x8B08012A:  # ADD x10,x9,x8
            require(counter == "old" and not rc_address, "wrong constant index")
            rc_address = True
        elif w == 0x91002108:  # ADD x8,x8,#8
            require(counter == "old", "counter advances twice")
            counter = "next"
        else:
            vector(w, registers, rc_address)
            if w == 0x4D40CD40:
                require(not rc_load, "multiple constant loads")
                rc_load = True
        i += 1
    branch = words[i + 1]
    require(
        counter == "next"
        and rc_load
        and branch & 0xFF00001F == 0x54000001
        and i + 1 + sign_extend(branch >> 5 & 0x7FFFF, 19) == start,
        "unexpected round backedge",
    )
    stored = [slot for w in words[i + 2 : -5] for slot in row_access(w, False)]
    require(
        sorted(loaded) == sorted(stored),
        "round registers or stores do not preserve the state layout",
    )
    layout = [r for _, r in sorted(stored)]
    return pc, [registers[r] for r in layout], table, words[start:i], layout
