"""Inductive symbolic execution of the linked arm64 SHAKE256 Sponge::absorb.

The loop invariant compares the actual 25-lane array, cursor and consumed slice prefix
to a scalar SHAKE specification. We start separately at each loop cut point with arbitrary
inputs satisfying its invariant, fork both feasible branch outcomes and prove each successor.
The lexicographic variant is (unconsumed bytes, cut-point rank). No input length is unrolled.
Requires the existing peer-proof dependency z3-solver==4.15.4.0.
"""

import copy
from dataclasses import dataclass
import z3 as z
from image import require, sign_extend

WORD = 1 << 64
WIDTH = z.BitVecSort(64)
LANES = z.ArraySort(z.IntSort(), WIDTH)
BYTES = z.ArraySort(z.IntSort(), z.BitVecSort(8))
PERM = z.Function("KeccakF1600", LANES, LANES)
BLOCKS = z.Function(
    "absorb_whole_rate_blocks", LANES, BYTES, z.IntSort(), z.IntSort(), LANES
)
N, I, P = z.Ints("length consumed pos")
INPUT, A = z.Const("input", BYTES), z.Const("lanes", LANES)

# Byte offsets in this version of the linked function, each checked as an induction cut.
ENTRY, HEAD, PREP, BULK, WORDS, TAIL, EXIT = 0, 0x38, 0xA4, 0x1C0, 0x148, 0x21C, 0x268
RANK = {ENTRY: 6, HEAD: 5, PREP: 4, BULK: 3, WORDS: 2, TAIL: 1, EXIT: 0}


@dataclass(frozen=True)
class Ptr:
    space: str
    offset: object = 0


def equal(a, b):
    if isinstance(a, Ptr) or isinstance(b, Ptr):
        return (
            isinstance(a, Ptr)
            and isinstance(b, Ptr)
            and a.space == b.space
            and equal(a.offset, b.offset)
        )
    return a == b


def predicate(p):
    return z.BoolVal(p) if isinstance(p, bool) else p


def number(n):
    return z.IntVal(n) if isinstance(n, int) else n


def div(n, d):
    return number(n) / d


class Machine:
    def __init__(self, source, code, targets):
        self.source, self.code, self.targets = source, code, targets
        self.reg = {i: z.Int(f"x{i}") for i in range(31)}
        self.pos = self.spec_pos = P
        self.state = self.spec_state = A
        self.i = I
        self.path = [N >= 0, N < 2**63, I >= 0, I <= N, P >= 0, P < 136]
        self.path += self.invariant(source, install=True)
        self.flags = None
        self.covered = set()
        self.edges = set()

    def fork(self):
        other = copy.copy(self)
        other.reg = self.reg.copy()
        other.path = self.path.copy()
        return other

    def possible(self, extra):
        solver = z.Solver()
        solver.set(timeout=10000)
        solver.add(*self.path, predicate(extra))
        ans = solver.check()
        if ans == z.unknown:
            raise ValueError(
                f"unresolved obligation at {self.source:x}->{self.pc:x}: {solver.reason_unknown()}"
            )
        return ans == z.sat

    def prove(self, p, why):
        p = z.simplify(predicate(p))
        if not z.is_true(p) and self.possible(z.Not(p)):
            raise ValueError(f"failed {why} at {self.source:x}->{self.pc:x}: {p}")

    def invariant(self, cut, install=False):
        r, i, pos = self.reg, self.i, self.pos

        def regs(expected):
            if install:
                r.update(expected)
                return []
            return [equal(r[k], v) for k, v in expected.items()]

        if cut == ENTRY:
            return [i == 0] + regs({0: Ptr("state"), 1: Ptr("msg"), 2: N})
        common = {19: Ptr("state"), 20: N, 21: Ptr("msg")}
        if cut == HEAD:
            return [i < N, pos % 8 != 0] + regs(common | {8: pos, 9: pos % 8, 23: i})
        if cut == PREP:
            # The bulk threshold was satisfied before finishing the partial rate.
            return [pos > 0, pos % 8 == 0, N - i >= 136 - pos + 136] + regs(
                common | {8: pos, 22: i}
            )
        if cut == BULK:
            return [pos == 0] + regs(common | {0: i, 23: N - i})
        if cut == WORDS:
            return [N - i >= 8, pos % 8 == 0] + regs(common | {22: i, 24: N - i})
        if cut == TAIL:
            return [i < N] + regs(
                {19: Ptr("state"), 20: N - i, 21: Ptr("msg", i), 8: pos}
            )
        if cut == EXIT:
            return [i == N]
        raise ValueError("unrecognized cut")

    def read_message(self, ptr, size):
        self.prove(equal(ptr, Ptr("msg", self.i)), "input pointer")
        self.prove(self.i + size <= N, "input bounds")
        bits = [z.Select(INPUT, self.i + j) for j in reversed(range(size))]
        v = z.Concat(*bits) if size > 1 else z.ZeroExt(56, bits[0])
        pos = self.spec_pos
        if size == 8:
            self.prove(pos % 8 == 0, "aligned sponge lane")
            val = v
        else:
            val = v << z.Int2BV(8 * (pos % 8), 64)
        state = z.Store(
            self.spec_state, div(pos, 8), z.Select(self.spec_state, div(pos, 8)) ^ val
        )
        self.spec_state = z.If(pos + size == 136, PERM(state), state)
        self.spec_pos = (pos + size) % 136
        self.i += size
        return v

    def call(self, dst):
        self.prove(equal(self.reg[0], Ptr("state")), "callee state argument")
        if dst == self.targets[0]:
            self.state = PERM(self.state)
        elif dst == self.targets[1]:
            self.prove(equal(self.reg[1], Ptr("msg", self.i)), "bulk input pointer")
            count = self.reg[2]
            self.prove(
                z.And(
                    self.pos == 0,
                    self.spec_pos == 0,
                    count >= 0,
                    count % 136 == 0,
                    self.i + count <= N,
                ),
                "bulk slice contract",
            )
            self.prove(
                count == div(N - self.i, 136) * 136, "maximal whole-block prefix"
            )
            self.state = BLOCKS(self.state, INPUT, self.i, count)
            self.spec_state = BLOCKS(self.spec_state, INPUT, self.i, count)
            self.i += count
        else:
            raise ValueError("unexpected reachable call or panic")
        # The result must be independent of all caller-saved state.
        self.reg.update({j: z.FreshInt("clobber") for j in [*range(18), 30]})
        self.flags = None

    def norm(self, x):
        return number(x) % WORD

    def add(self, a, b):
        if isinstance(a, Ptr):
            return Ptr(a.space, a.offset + b)
        return self.norm(a + b)

    def split(self, pc, yes, no, test):
        for dest, cond in [(yes, predicate(test)), (no, z.Not(predicate(test)))]:
            if self.possible(cond):
                sibling = self.fork()
                sibling.path.append(cond)
                sibling.walk(dest, pc)
        return True

    def walk(self, pc, previous=None):
        for _ in range(150):
            self.pc = pc
            if previous is not None and pc in RANK:
                for pred in [
                    self.state == self.spec_state,
                    self.pos == self.spec_pos,
                    self.i >= I,
                    self.i <= N,
                    self.pos >= 0,
                    self.pos < 136,
                    z.Or(self.i > I, RANK[pc] < RANK[self.source]),
                ] + self.invariant(pc):
                    self.prove(pred, "cut-point invariant or decreasing variant")
                self.edges.add((self.source, pc))
                return
            self.covered.add(pc)
            require(
                pc % 4 == 0 and 0 <= pc < 4 * len(self.code), "branch outside absorb"
            )
            w = self.code[pc // 4]
            r = self.reg
            d, n, m = w & 31, (w >> 5) & 31, (w >> 16) & 31
            imm = (w >> 10) & 4095
            previous = pc
            pc += 4
            if previous == ENTRY:
                require(
                    self.code[:5]
                    == [0xA9BC5FF8, 0xA90157F6, 0xA9024FF4, 0xA9037BFD, 0x9100C3FD],
                    "wrong 64-byte prologue",
                )
                pc = 20
            elif w & 0xFFE0FFE0 == 0xAA0003E0:
                require(d < 31 and m < 31, "unsupported zero register move")
                r[d] = r[m]
            elif w & 0xFFFFFFE0 == 0xD2800000:
                r[d] = 0
            elif w & 0xFF000000 == 0xB4000000:  # CBZ Xd
                if self.split(
                    previous,
                    previous + 4 * sign_extend((w >> 5) & 0x7FFFF, 19),
                    pc,
                    r[d] == 0,
                ):
                    return
            elif w & 0xFF000010 == 0x54000000:
                require(self.flags is not None, "stale condition flags")
                eq, carry = self.flags
                tests = {
                    0: eq,
                    1: z.Not(predicate(eq)),
                    2: carry,
                    3: z.Not(predicate(carry)),
                    8: z.And(carry, z.Not(predicate(eq))),
                    9: z.Or(z.Not(predicate(carry)), eq),
                }
                if self.split(
                    previous,
                    previous + 4 * sign_extend((w >> 5) & 0x7FFFF, 19),
                    pc,
                    tests[w & 15],
                ):
                    return
            elif w >> 26 == 5:
                pc = previous + 4 * sign_extend(w & 0x3FFFFFF, 26)
            elif w >> 26 == 37:
                self.call(previous + 4 * sign_extend(w & 0x3FFFFFF, 26))
            elif w & 0xFFC00000 in (0x91000000, 0xD1000000, 0xF1000000, 0xB1000000):
                require(n < 31, "unexpected SP")
                sub = bool(w & (1 << 30))
                flags = bool(w & (1 << 29))
                if flags:
                    self.flags = (
                        self.norm(r[n] + (-imm if sub else imm)) == 0,
                        r[n] >= imm if sub else r[n] + imm >= WORD,
                    )
                if d < 31:
                    r[d] = self.add(r[n], -imm if sub else imm)
            elif w & 0xFFE00000 in (0x8B000000, 0xCB000000, 0xAB000000, 0xEB000000):
                sub = bool(w & (1 << 30))
                flags = bool(w & (1 << 29))
                a, b = r[n], r[m] * (1 << ((w >> 10) & 63))
                if flags:
                    self.flags = (
                        self.norm(a + (-b if sub else b)) == 0,
                        a >= b if sub else a + b >= WORD,
                    )
                if d < 31:
                    r[d] = self.add(a, -b if sub else b)
            elif w == 0xFA5412C2:  # CCMP X22,X20, #2, NE
                eq, _ = self.flags
                self.flags = (
                    z.And(z.Not(predicate(eq)), r[22] == r[20]),
                    z.Or(eq, r[22] >= r[20]),
                )
            elif w == 0x92400909:
                r[9] = r[8] % 8
            elif w in (0xD343FD00, 0xD347FD08):
                r[d] = div(r[n], 1 << (3 if w == 0xD343FD00 else 7))
            elif w in (0xD37DF129, 0xD37DF102):
                r[d] = self.norm(8 * r[n])
            elif w == 0xD37D0908:
                r[8] = 8 * (r[8] % 8)
            elif w & 0xFFE0FC00 == 0x9AC02000:
                r[d] = r[n] << z.Int2BV(number(r[m]) % 64, 64)
            elif w & 0xFFE0FC00 == 0xCA000000:
                r[d] = r[n] ^ r[m]
            elif w == 0xAA3703E8:
                r[8] = WORD - 1 - r[23]
            elif w == 0xB204CFE8:
                r[8] = 0xF0F0F0F0F0F0F0F0
            elif w == 0xF29E1E28:
                r[8] = div(r[8], 65536) * 65536 + 0xF0F1
            elif w == 0x9BC87EE8:
                r[8] = div(r[23] * r[8], WORD)
            elif w in (0xF9406408, 0xF9406668):
                self.prove(equal(r[n], Ptr("state")), "cursor load")
                r[d] = self.pos
            elif w in (0xF9006668, 0xF900667F):
                self.prove(equal(r[n], Ptr("state")), "cursor store")
                self.pos = r[d] if d < 31 else 0
            elif w in (0x38776AA8, 0xF8766AA8):
                r[d] = self.read_message(
                    self.add(r[n], r[m]), 1 if w == 0x38776AA8 else 8
                )
            elif w == 0x384016A9:
                r[d] = self.read_message(r[n], 1)
                r[n] = self.add(r[n], 1)
            elif w in (0xF8607A69, 0xF8207A68):
                self.prove(equal(r[n], Ptr("state")), "lane base")
                self.prove(z.And(r[m] >= 0, r[m] < 25), "lane bounds")
                if w == 0xF8607A69:
                    r[d] = z.Select(self.state, r[m])
                else:
                    self.state = z.Store(self.state, r[m], r[d])
            else:
                raise ValueError(
                    f"unhandled reachable instruction {w:08x} at +{previous:x}"
                )
        raise ValueError("cycle without an invariant")


def verify(image):
    base, words = image.function(b"6Sponge6absorb", b"6slhdsa8shake256")
    single, _ = image.function(b"parallel6single")
    bulk, _ = image.function(b"4sha36blocks")
    require(
        words[EXIT // 4 : EXIT // 4 + 5]
        == [0xA9437BFD, 0xA9424FF4, 0xA94157F6, 0xA8C45FF8, 0xD65F03C0],
        "wrong absorb epilogue",
    )
    edges = set()
    for source in RANK:
        if source == EXIT:
            continue
        m = Machine(source, words, (single - base, bulk - base))
        m.walk(source)
        require(m.edges, "vacuous absorb cut")
        edges.update(m.edges)
    return len(edges)


def mutation_tests(image):
    import struct
    from image import Image

    base, code = image.function(b"6Sponge6absorb", b"6slhdsa8shake256")
    text_va, _, text_off = image.sections[b"__text"]
    controls = [
        (0x60, 0x91000508, 0x91000108),  # ADD 0 after the head byte
        (0x224, 0x54000428, 0x54000429),  # unsigned bounds check reversed
        (0x188, 0xF102211F, 0xF102251F),  # wrap the word cursor at 137
    ]
    # Redirect the bulk call to the genuine one-state permutation. Both targets have
    # modeled contracts, so the failure concerns the sponge outcome or input consumption.
    pc = base + 0x1F0
    single, _ = image.function(b"parallel6single")
    old = code[0x1F0 // 4]
    require(old >> 26 == 37 and (single - pc) % 4 == 0, "missing bulk BL")
    controls.append((0x1F0, old, 0x94000000 | (((single - pc) // 4) & 0x3FFFFFF)))
    for off, old, new in controls:
        require(code[off // 4] == old, f"missing mutation site at +{off:x}")
        data = bytearray(image.data)
        struct.pack_into("<I", data, text_off + base - text_va + off, new)
        try:
            verify(Image(data))
        except ValueError as err:
            require(
                "failed" in str(err)
                or "unexpected reachable" in str(err)
                or "unhandled reachable" in str(err),
                f"wrong mutation failure: {err}",
            )
        else:
            raise AssertionError(f"absorb mutation passed at +{off:x}")


if __name__ == "__main__":
    import argparse
    import hashlib
    from pathlib import Path
    from check import release_consumer
    from image import Image

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", nargs="?", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    require(z.get_version_string() == "4.15.4", "use z3-solver==4.15.4.0")
    image = Image((args.binary or release_consumer()).read_bytes())
    print(
        f"Verified Sponge::absorb over {verify(image)} inductive edges for {hashlib.sha256(image.data).hexdigest()}"
    )
    if args.self_test:
        mutation_tests(image)
        print("Rejected four linked absorb mutations")
