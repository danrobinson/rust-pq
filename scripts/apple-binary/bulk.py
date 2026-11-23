"""Symbolically verify the linked SHAKE aligned rate-block kernel and its only callee.

The argument is a valid slice whose byte length is 136 times the block count.
The loop cut point is the register layout at the start of each rate block. Inputs,
message words and scratch registers are independent symbols; vector instructions act
on both 64-bit halves. The separately kernel-checked round proves the permutation on
arbitrary values in this same layout. Byte offsets refer to the supported schedule.
"""

import copy
import struct
from image import require, sign_extend
from permute import vector


class Transfer:
    """The stack offsets are relative to the final (lowest) SP of the bulk routine.
    Its saved ABI registers start at +624. All scratch accesses stay below that frame.
    State and one block of message words are independent, disjoint ABI regions.
    """

    def __init__(self):
        self.x = {0: ("state", 0), 1: ("data", 0), 2: ("length", 0), 31: ("stack", 0)}
        self.v = {}
        self.data_reads = []
        self.mem = {("state", 8 * i): ("lane", i) for i in range(25)}
        self.mem.update({("data", 8 * i): ("msg", i) for i in range(17)})

    def addr(self, n, delta=0):
        space, off = self.x[n]
        require(space in ("state", "data", "stack"), "non-pointer used for bulk access")
        return space, off + delta

    def access(self, ptr, idx, write=None):
        space, off = ptr
        off += idx
        require(
            off % 8 == 0
            and 0 <= off < {"stack": 624, "state": 200, "data": 136}[space],
            "bulk memory bounds",
        )
        if write is not None:
            require(space != "data", "bulk mutates the message")
            self.mem[space, off] = write
        else:
            require((space, off) in self.mem, "bulk reads an undefined word")
            if space == "data":
                self.data_reads.append(off)
            return self.mem[space, off]

    def run(self, words, mapper=False):
        for w in words:
            d, n, m = w & 31, w >> 5 & 31, w >> 16 & 31
            kind = w & 0xFFC00000
            if (
                w & 0xFFE0FFE0 == 0xAA0003E0
                or kind in (0x91000000, 0xF9400000)
                or w == 0x9E660108
            ):
                require(
                    d in ({9} if mapper else {0, 8, 9, 11, 19, 20, 21, 22}),
                    "unexpected GP register clobber",
                )
            if mapper and (
                kind in (0xAD400000, 0x3DC00000)
                or w & 0xFFFFFC00 == 0x4D40CC00
                or w in (0x3CCB801F, 0x4E0807E8, 0x4E1807FF)
            ):
                require(d not in range(10, 16), "unsaved vector register clobber")
            if w & 0xFFE0FFE0 == 0xAA0003E0:
                self.x[d] = self.x[m]
            elif kind == 0x91000000:
                self.x[d] = self.addr(n, w >> 10 & 4095)
            elif kind in (
                0xAD400000,
                0xAD000000,
                0x3DC00000,
                0x3D800000,
                0xF9400000,
                0xF9000000,
            ):
                pair = kind in (0xAD400000, 0xAD000000)
                simd = kind not in (0xF9400000, 0xF9000000)
                size = 16 if simd else 8
                base = self.addr(
                    n,
                    size * (sign_extend(w >> 15 & 127, 7) if pair else w >> 10 & 4095),
                )
                regs = [d, w >> 10 & 31] if pair else [d]
                require(len(set(regs)) == len(regs), "overlapping pair transfer")
                for i, r in enumerate(regs):
                    if w & (1 << 22):
                        if simd:
                            self.v[r] = tuple(
                                self.access(base, size * i + 8 * j) for j in (0, 1)
                            )
                        else:
                            self.x[r] = self.access(base, size * i)
                    elif simd:
                        for j, val in enumerate(self.v[r]):
                            self.access(base, size * i + 8 * j, val)
                    else:
                        self.access(base, size * i, self.x[r])
            elif w & 0xFFFFFC00 in (0x4D40CC00, 0x4DDFCC00):
                ptr = self.addr(n)
                self.v[d] = (self.access(ptr, 0),) * 2
                if w & (1 << 23):
                    self.x[n] = self.addr(n, 8)
            elif w == 0x3CCB801F:  # LDUR Q31,[X0,#184]
                self.v[31] = tuple(
                    self.access(self.addr(0), 184 + 8 * j) for j in (0, 1)
                )
            elif w in (0x4E0807E8, 0x4E1807FF):
                self.v[d] = (self.v[n][w >> 20 & 1],) * 2
            elif w & 0xFFFFFC00 == 0x4D408400:
                self.v[d] = (self.v[d][0], self.access(self.addr(n), 0))
            elif w & 0xFFE0FC00 == 0x6E201C00:
                self.v[d] = tuple(
                    frozenset((a, b)) for a, b in zip(self.v[n], self.v[m])
                )
            elif w & 0xFFE0FC00 == 0x4EC03800:
                self.v[d] = (self.v[n][0], self.v[m][0])
            elif w == 0x9E660108:
                self.x[8] = self.v[8][0]
            else:
                raise ValueError(f"unsupported bulk transfer {w:08x}")


def target(w, index):
    if w >> 26 in (5, 37):
        return index + sign_extend(w & 0x3FFFFFF, 26)
    return index + sign_extend(w >> 5 & 0x7FFFF, 19)


def decode(image):
    pc, words = image.function(b"4sha36blocks")

    def cut(a, b):
        return words[a // 4 : b // 4]

    def exact(a, expected, why):
        require(cut(a, a + 4 * len(expected)) == expected, why)

    def edge(at, op, to):
        w = words[at // 4]
        require(
            w & 0xFF00001F == op and target(w, at // 4) * 4 == to,
            "bulk conditional branch",
        )

    def jump(at, to):
        w = words[at // 4]
        require(w >> 26 == 5 and target(w, at // 4) * 4 == to, "bulk bypass target")

    exact(
        0,
        [
            0x6DB83BEF,
            0x6D0133ED,
            0x6D022BEB,
            0x6D0323E9,
            0xA9046FFC,
            0xA90557F6,
            0xA9064FF4,
            0xA9077BFD,
            0x9101C3FD,
            0xD109C3FF,
        ],
        "bulk frame setup",
    )
    exact(
        0x3DC,
        [
            0x9109C3FF,
            0xA9477BFD,
            0xA9464FF4,
            0xA94557F6,
            0xA9446FFC,
            0x6D4323E9,
            0x6D422BEB,
            0x6D4133ED,
            0x6CC83BEF,
            0xD65F03C0,
        ],
        "bulk frame restoration",
    )
    require(len(words) == 0x404 // 4, "bulk function extent")

    t = Transfer()
    t.run(cut(0x28, 0x78))
    (mapper,) = [
        name
        for name, _ in image.symbols
        if b"4core5array" in name
        and b"parallel4sha36blocks0" in name
        and b"map" in name
    ]
    map_pc, map_words = image.function(mapper, b"4core5array")
    call = words[0x78 // 4]
    require(
        call >> 26 == 37 and pc + 4 * target(call, 0x78 // 4) == map_pc,
        "bulk map target",
    )
    require(
        map_words[0] == 0x6DBF23E9 and map_words[-2:] == [0x6CC123E9, 0xD65F03C0],
        "mapper frame",
    )
    # The mapper's only frame accesses are its matched D8/D9 save and restore.
    # Its body receives caller-stack pointers in x0/x8 and must not use SP.
    require(
        all(
            (w >> 5 & 31) != 31
            for w in map_words[1:-2]
            if w not in (0x4E0807E8, 0x4E1807FF)
        ),
        "mapper unexpectedly addresses SP",
    )
    t.run(map_words[1:-2], mapper=True)
    require(
        all(
            t.mem["stack", 16 + 16 * i + 8 * j] == ("lane", i)
            for i in range(25)
            for j in range(2)
        ),
        "map failed to duplicate state",
    )
    t.x = {r: v for r, v in t.x.items() if r in (19, 20, 21, 22, 31)}
    t.v = {}
    require(
        t.x[19] == ("state", 0) and t.x[20] == ("data", 0) and t.x[21] == ("length", 0),
        "bulk arguments clobbered",
    )

    # floor(n * multiplier / 2^64) >> 7 == n / 136 (Lean rateQuotient).
    exact(
        0x7C,
        [
            0xB204CFE8,
            0xF29E1E28,
            0x9BC87EA8,
            0xD347FD08,
            0x8B081108,
            0xD37DF108,
            0xF1021D1F,
        ],
        "bulk count arithmetic",
    )
    edge(0x98, 0x54000008, 0x138)
    empty = copy.deepcopy(t)
    empty.run(cut(0x9C, 0x134))
    jump(0x134, 0x3C0)
    empty.run(cut(0x3C0, 0x3DC))
    require(not empty.data_reads, "message access on empty input")
    require(
        all(empty.mem["state", 8 * i] == ("lane", i) for i in range(25)),
        "zero-block projection",
    )

    t.run(cut(0x138, 0x168))
    adrp, add = cut(0x168, 0x170)
    require(
        adrp & 0x9F00001F == 0x90000009 and add & 0xFFC003FF == 0x91000129,
        "round constants base",
    )
    table_va = (
        ((pc + 0x168) & ~4095)
        + 4096 * sign_extend(((adrp >> 5 & 0x7FFFF) << 2) | (adrp >> 29 & 3), 21)
        + (add >> 10 & 4095)
    )
    table = list(struct.unpack("<24Q", image.read(b"__const", table_va, 192)))
    t.run(cut(0x170, 0x174))
    layout = []
    for i in range(25):
        (reg,) = [r for r, v in t.v.items() if v == (("lane", i),) * 2]
        layout.append(reg)
    require(len(set(layout)) == 25, "bulk register layout")
    # Re-establish the loop invariant with arbitrary rows and no other SIMD registers.
    t.v = {r: (("lane", i),) * 2 for i, r in enumerate(layout)}
    exact(0x174, [0xD280000A], "nonzero round counter")
    t.x.update({8: ("remaining", 0), 9: ("table", table_va), 10: ("roundOffset", 0)})
    t.run(cut(0x178, 0x240))
    for reg, expected in [
        (8, ("remaining", 0)),
        (9, ("table", table_va)),
        (10, ("roundOffset", 0)),
        (19, ("state", 0)),
        (20, ("data", 0)),
        (31, ("stack", 0)),
    ]:
        require(t.x[reg] == expected, "block preparation clobbered a loop input")
    require(
        t.data_reads == [8 * i for i in range(17)], "message footprint or word order"
    )
    for i, r in enumerate(layout):
        lane = ("lane", i)
        require(
            t.v[r] == ((frozenset((lane, ("msg", i))) if i < 17 else lane),) * 2,
            "wrong message word or XOR lane",
        )

    regs = {r: f"a[{i}]!" for i, r in enumerate(layout)}
    instructions = cut(0x240, 0x374)
    address = advanced = fetched = False
    for w in instructions:
        if w == 0x8B0A012B:
            require(not advanced and not address, "wrong round table address")
            address = True
        elif w == 0x9100214A:
            require(not advanced, "wrong round counter")
            advanced = True
        elif w == 0x4D40CD60:
            require(address and not fetched, "wrong RC load")
            regs[0] = "rc"
            fetched = True
        elif w == 0x3D8003E5:
            regs[32] = regs[5]
        elif w == 0x3DC003E4:
            regs[4] = regs[32]
        else:
            vector(w, regs, False)
    require(advanced and fetched, "missing round count or constant")
    exact(0x374, [0xF103015F], "wrong round count bound")
    edge(0x378, 0x54000001, 0x240)
    exact(0x37C, [0x91022294, 0xD1022108, 0xF1021D1F], "wrong next rate block")
    edge(0x388, 0x54000008, 0x174)
    # The round theorem holds for arbitrary scratch values after every block. Low
    # and high lanes each carry their own round result. Output must use the low lane.
    t.v = {r: (("out", i), ("high", i)) for i, r in enumerate(layout)}
    t.data_reads.clear()
    t.run(cut(0x38C, 0x3DC))
    require(not t.data_reads, "message access after last block")
    require(
        all(t.mem["state", 8 * i] == ("out", i) for i in range(25)),
        "wrong output projection",
    )
    return [regs[r] for r in layout], table, instructions, layout


def mutation_tests(image):
    from image import Image

    pc, words = image.function(b"4sha36blocks")
    section, _, file_offset = image.sections[b"__text"]
    for off, bit, reason in [
        (0x18C, 1 << 13, "message footprint"),
        (0x378, 1 << 5, "conditional branch"),
        (0x38C, 1 << 5, "output projection"),
    ]:
        altered = bytearray(image.data)
        struct.pack_into(
            "<I", altered, file_offset + pc - section + off, words[off // 4] ^ bit
        )
        try:
            decode(Image(altered))
        except ValueError as err:
            require(reason in str(err), f"unexpected bulk control failure: {err}")
        else:
            raise ValueError(f"mutated bulk kernel passed at +{off:x}")
