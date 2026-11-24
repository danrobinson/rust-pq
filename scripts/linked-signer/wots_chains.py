# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Inductive proof of both masked Apple SHAKE WOTS chains, including their full hash addresses."""

import argparse
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
from driver import (
    angr,
    c,
    Image,
    blob,
    wrbytes,
    put,
    unsigned,
    load,
    integer,
    equal,
    clobber_scratch,
    require,
    STACK,
    KEY,
    RETURN,
    RESULT,
)
import arm_vector_ir

SEED, ADDRESS, VALUES = KEY + 128, KEY + 256, KEY + 512


def b32(x):
    return c.BVV(x, 32) if isinstance(x, int) else x


def packed(x):
    return c.Concat(x[1], x[0])


def matrix(lanes):
    return c.Concat(*(v.get_bytes(i, 8) for i in range(0, 200, 8) for v in lanes))


def agrees(st, x, y, why):
    if isinstance(x, (int, bool)) and isinstance(y, (int, bool)):
        require(x == y, why)
    elif not c.is_true(c.simplify(x == y)):
        equal(st, x, y, why)


def padded(message):
    used = message.size() // 8
    return c.Concat(message, c.BVV(b"\x1f" + bytes(134 - used) + b"\x80" + bytes(64)))


def return_call(st, ret=None):
    clobber_scratch(st)
    if ret is not None:
        st.regs.x0 = ret
    st.regs.pc = st.regs.lr


class ImageEnv:
    def __init__(self, path, image, n):
        self.image, self.n = image, n
        self.project = angr.load_shellcode(
            bytes(image.data), arch="aarch64", load_address=image.base
        )
        self.suffix = f"Kj{n:x}_EB6_".encode()
        self.const = image.sections[b"__const"][:2]
        start, size, _ = image.sections[b"__stubs"]
        stubs = subprocess.check_output(
            ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
        )
        self.stubs = {}
        for name in ("memcpy", "memset_pattern16"):
            (at,) = [
                int(s, 16)
                for s in re.findall(
                    r"^(0x[0-9a-f]+)\s+\d+\s+_" + name + "$", stubs, re.M
                )
                if start <= int(s, 16) < start + size
            ]
            self.stubs[at] = name
        self.permute = self.fun(b"4sha37permute", b"6slhdsa8shake2568parallel")[0]

    def fun(self, suffix, part=b"6slhdsa5shake"):
        pc, words = self.image.function(suffix, part)
        return pc, pc + len(words) * 4

    def blank(self, pc):
        s = self.project.factory.blank_state(
            addr=pc,
            add_options={
                angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
                angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            },
        )
        s.regs.sp, s.regs.lr = STACK, RETURN
        return s

    def library(self, s):
        dst, src, size = (integer(s, getattr(s.regs, "x" + str(j))) for j in range(3))
        memcopy = self.stubs[s.addr] == "memcpy"
        read = size if memcopy else 16
        require(
            0 < size <= 8192 and (src + read <= dst or dst + size <= src),
            "invalid overlap or library length",
        )
        data = load(s, src, read)
        if not memcopy:
            data = (
                c.Concat(*([data] * ((size + 15) // 16))).get_bytes(0, size)
                if size > 16
                else data.get_bytes(0, size)
            )
        wrbytes(s, dst, data)
        return_call(s, dst if memcopy else None)


class Chain:
    def __init__(self, env):
        self.e, self.n = env, env.n
        self.body = env.fun(b"5batch6chains" + env.suffix)
        self.header = env.fun(b"5batch6header" + env.suffix)
        self.seed = blob("seed", self.n)
        self.addr = [
            c.BVS("layer", 32),
            c.BVS("tree", 64),
            c.BVS("type", 32),
            c.BVS("keypair", 32),
        ]
        self.ids = [c.BVS("chain_id", 32) for _ in range(2)]
        self.index = [c.BVS("round_index", 32) for _ in range(2)]
        self.end = [c.BVS("end_index", 32) for _ in range(2)]
        self.val = [blob("value", self.n) for _ in range(2)]
        self.after = [blob("permuted", 200) for _ in range(2)]
        self.saved = {i: c.BVS("saved", 64) for i in range(18, 30)}
        self.saved[30] = RETURN
        self.vsaved = {i: c.BVS("saved_simd", 64) for i in range(8, 16)}
        # Loop head and the actual word caches kept in GPRs or spills (offsets in bytes).
        head, local, self.template, self.end1, self.idx1, self.caches = {
            16: (0xC8, 0x360, 0x40, 26, 27, [[23, 25], [24, 22]]),
            24: (0xD4, 0x370, 0x48, 28, 19, [[23, 25, 27], [24, 26, 22]]),
            32: (
                0xEC,
                0x380,
                0x58,
                23,
                24,
                [[("sp", 16), 25, 27, 19], [("sp", 8), 26, 28, 22]],
            ),
        }[self.n]
        self.sp = STACK - 96 - local
        self.head = self.body[0] + head

    def message(self, i, index, value):
        layer, tree, typ, kp = self.addr
        return padded(
            c.Concat(self.seed, layer, b32(0), tree, typ, kp, self.ids[i], index, value)
        )

    def statebytes(self, index, values):
        return matrix([self.message(j, index[j], values[j]) for j in range(2)])

    def invariant(self, s, indices, values, install=False):
        def reg(i, v, low=False):
            if install:
                setattr(
                    s.regs,
                    "x" + str(i),
                    c.Concat(c.BVS("dead_high", 32), v) if low else v,
                )
            else:
                x = getattr(s.regs, "x" + str(i))
                agrees(s, x[31:0] if low else x, v, "loop register " + str(i))

        def mem(addr, v):
            n = v.size() // 8
            if install:
                wrbytes(s, addr, v)
            else:
                agrees(s, load(s, addr, n), v, "loop memory")

        reg(20, packed(self.end))
        reg(21, indices[0], True)
        reg(self.end1, self.end[1], True)
        reg(self.idx1, indices[1], True)
        if self.n == 16:
            reg(19, RESULT)
        elif install:
            put(s, self.sp, RESULT, 8)
        else:
            agrees(s, unsigned(s, self.sp), RESULT, "result slot")
        mem(self.sp + self.template, self.statebytes([b32(0)] * 2, values))
        for k, cache in enumerate(self.caches):
            for j, entry in enumerate(cache):
                val = values[k].get_bytes(j * 8, 8)
                if isinstance(entry, int):
                    reg(entry, val.reversed)
                else:
                    mem(self.sp + entry[1], val)
        for offs, i in enumerate([28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 29, 30]):
            if install:
                put(s, STACK - 96 + 8 * offs, self.saved[i], 8)
            else:
                agrees(
                    s,
                    unsigned(s, STACK - 96 + 8 * offs),
                    self.saved[i],
                    "live saved register",
                )
        agrees(s, s.regs.sp, self.sp, "chain stack")
        agrees(s, s.regs.x18, self.saved[18], "platform register")
        for i in self.vsaved:
            agrees(s, getattr(s.regs, f"q{i}")[63:0], self.vsaved[i], "preserved SIMD")

    def run(self, step=False):
        s = self.e.blank(self.head if step else self.body[0])
        for i, v in self.saved.items():
            if not step or i == 18:
                setattr(s.regs, "x" + str(i), v)
        if step:
            s.regs.lr = c.BVS("iteration_LR", 64)
        for i, v in self.vsaved.items():
            setattr(s.regs, f"q{i}", c.Concat(c.BVS("other_half", 64), v))
        for a, b in zip(self.index, self.end):
            s.add_constraints(c.ULE(a, b), c.ULE(b, 15))
        if step:
            s.add_constraints(packed(self.index) != packed(self.end))
            s.regs.sp = self.sp
            self.invariant(s, self.index, self.val, install=True)
        else:
            for i, v in enumerate(
                [
                    RESULT,
                    SEED,
                    ADDRESS,
                    *[v.zero_extend(32) for v in self.ids],
                    VALUES,
                    packed(self.index),
                    packed(self.end),
                ]
            ):
                setattr(s.regs, "x" + str(i), v)
            wrbytes(s, SEED, self.seed)
            wrbytes(s, VALUES, c.Concat(*self.val))
            layer, tree, typ, kp = self.addr
            for off, size, val in [
                (0, 8, tree),
                (8, 4, layer),
                (12, 4, typ),
                (16, 4, kp),
                (20, 4, blob("previous_word2", 4)),
                (24, 4, blob("previous_word3", 4)),
            ]:
                put(s, ADDRESS + off, val, size)
        lo, size = self.e.const

        def guard(st, kind):
            expr = getattr(st.inspect, "mem_" + kind + "_address")
            length = getattr(st.inspect, "mem_" + kind + "_length")
            count = (
                integer(st, length)
                if length is not None
                else getattr(st.inspect, "mem_" + kind + "_expr").size() // 8
            )
            addr = integer(st, expr)
            ranges = [(self.sp - 1024, STACK), (RESULT, RESULT + 2 * self.n)]
            if kind == "read":
                ranges += [
                    (SEED, SEED + self.n),
                    (VALUES, VALUES + 2 * self.n),
                    (ADDRESS, ADDRESS + 28),
                    (lo, lo + size),
                ]
            require(
                any(a <= addr and addr + count <= b for a, b in ranges),
                "out-of-region chain " + kind,
            )

        for k in ("read", "write"):
            s.inspect.b(
                "mem_" + k, when=angr.BP_BEFORE, action=lambda st, k=k: guard(st, k)
            )
        valid = list(s.solver.constraints)
        todo = [(s, 0, 0)]
        domains = []
        while todo:
            st, count, hits = todo.pop()
            require(count < 120, "chain subpath bound")
            at = st.addr
            if at == RETURN or (at == self.head and count):
                still = [c.ULT(i, e) for i, e in zip(self.index, self.end)]
                index = (
                    [c.If(cond, i + 1, i) for i, cond in zip(self.index, still)]
                    if step
                    else self.index
                )
                vals = (
                    [
                        c.If(cond, v.get_bytes(0, self.n), old)
                        for cond, v, old in zip(still, self.after, self.val)
                    ]
                    if step
                    else self.val
                )
                agrees(st, hits, int(step), "permutation count")
                if step:
                    # Both differences are bounded by 15, so the sum has no 32-bit overflow.
                    agrees(
                        st,
                        c.ULT(
                            sum(e - i for i, e in zip(index, self.end)),
                            sum(e - i for i, e in zip(self.index, self.end)),
                        ),
                        True,
                        "decreasing chain rounds",
                    )
                if at == RETURN:
                    agrees(st, packed(index), packed(self.end), "early chain return")
                    agrees(
                        st,
                        load(st, RESULT, 2 * self.n),
                        c.Concat(*vals),
                        "returned selected endpoints",
                    )
                    agrees(st, st.regs.sp, STACK, "return SP")
                    for j, v in self.saved.items():
                        agrees(st, getattr(st.regs, "x" + str(j)), v, "return register")
                    for j, v in self.vsaved.items():
                        agrees(st, getattr(st.regs, f"q{j}")[63:0], v, "return SIMD")
                else:
                    agrees(
                        st,
                        packed(index) != packed(self.end),
                        True,
                        "spurious next round",
                    )
                    self.invariant(st, index, vals)
                domains.append(c.And(*st.solver.constraints))
                continue
            if at in self.e.stubs:
                self.e.library(st)
            elif at == self.e.permute:
                require(step and hits == 0, "unexpected chain permutation")
                p = integer(st, st.regs.x0)
                require(self.sp <= p <= STACK - 400, "permutation scratch")
                agrees(
                    st,
                    load(st, p, 400),
                    self.statebytes(self.index, self.val),
                    "complete chain Keccak matrix",
                )
                wrbytes(st, p, matrix(self.after))
                return_call(st)
                hits += 1
            else:
                require(
                    any(a <= at < b for a, b in (self.body, self.header)),
                    f"unknown chain transfer {at:x}",
                )
                nxt = self.e.project.factory.successors(st)
                require(
                    nxt.flat_successors and not nxt.unconstrained_successors,
                    "unexpected unresolved chain exit",
                )
                todo += [(v, count + 1, hits) for v in nxt.flat_successors]
                continue
            todo.append((st, count + 1, hits))
        solver = c.Solver()
        solver.add(tuple(valid))
        require(
            domains
            and not solver.satisfiable(extra_constraints=[c.Not(c.Or(*domains))]),
            "incomplete chain domain",
        )
        return len(domains)


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("image", type=Path)
    p.add_argument("--width", type=int, choices=(16, 24, 32))
    args = p.parse_args()
    image = Image(args.image.read_bytes())
    for n in [args.width] if args.width else (16, 24, 32):
        model = Chain(ImageEnv(args.image, image, n))
        for step in (False, True):
            print(n, "round" if step else "entry", model.run(step), flush=True)
