# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Verify the linked Apple SHAKE FORS two-lane signing/recovery and node equations.

Uses symbolic selections, addresses, signature bytes and hash outputs. For each
Keccak call, check the complete input matrix against two padded FIPS messages.
"""

import argparse
import hashlib
import os
from pathlib import Path
import struct
import re
import subprocess
import sys
import tempfile

sys.dont_write_bytecode = True
from driver import (
    angr,
    c,
    Image,
    objects,
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
    HEAP,
    RETURN,
    RESULT,
)
import arm_vector_ir  # noqa: F401  registers missing VEX bitvector operations
from angr.concretization_strategies import SimConcretizationStrategySolutions

SEED, ADRS, DIGITS, SIG = KEY + 128, KEY + 256, KEY + 512, KEY + 1024


def b32(x):
    return c.BVV(x, 32) if isinstance(x, int) else x


def agree(st, x, y, why):
    if isinstance(x, (int, bool)) and isinstance(y, (int, bool)):
        require(x == y, why)
    elif not c.is_true(c.simplify(x == y)):
        equal(st, x, y, why)


def interleave(lanes):
    return c.Concat(*(x.get_bytes(i, 8) for i in range(0, 200, 8) for x in lanes))


class Case:
    def __init__(self, path, image, n, variant, kind):
        row, param, _, _, _ = objects(path, image, n, variant, "shake")
        _, _, _, _, _, a, k = row
        self.n, self.a, self.k, self.kind = n, a, k, kind
        self.length = k * (a + 1) * n
        self.project = angr.load_shellcode(
            bytes(image.data), arch="aarch64", load_address=image.base
        )
        suffix = f"Kj{n:x}_EB6_".encode()

        def fun(ending, family=b"6slhdsa5shake"):
            pc, words = image.function(ending, family)
            return pc, (pc, pc + len(words) * 4)

        self.start, routine = fun(
            b"10fors_batch"
            + ({"sign": b"4sign", "recover": b"7recover"}.get(kind, b"5nodes"))
            + suffix
        )
        self.node, _ = fun(b"10fors_batch5nodes" + suffix)
        _, header = fun(b"5batch6header" + suffix)
        self.allowed = [routine, header]
        if n == 24:
            self.allowed.append(fun(b"5batch4pair" + suffix)[1])
        _, start_body = fun(b"4hash5start" + suffix)
        self.allowed.extend(
            [
                start_body,
                fun(b"6Sponge6absorb", b"8shake256")[1],
                fun(b"6Sponge6finish", b"8shake256")[1],
            ]
        )
        self.hooks = {
            fun(b"4sha37permute", b"6slhdsa8shake2568parallel")[0]: "permute",
            fun(b"parallel6single", b"8shake256")[0]: "single",
            fun(b"19___rust_alloc_zeroed", b"___rustc")[0]: "alloc",
            fun(b"35___rust_no_alloc_shim_is_unstable_v2", b"___rustc")[0]: "shim",
        }
        stubs = subprocess.check_output(
            ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
        )
        start, size, _ = image.sections[b"__stubs"]
        self.memory_hooks = {}
        for name in ("memcpy", "memset_pattern16"):
            (address,) = [
                int(x, 16)
                for x in re.findall(
                    r"^(0x[0-9a-f]+)\s+\d+\s+_" + name + "$", stubs, re.M
                )
                if start <= int(x, 16) < start + size
            ]
            self.memory_hooks[address] = name
        self.const = image.sections[b"__const"][:2]
        self.param = param
        st = self.project.factory.blank_state(
            addr=self.start,
            add_options={
                angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
                angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            },
        )
        self.st = st
        self.callees = [getattr(st.regs, f"x{i}") for i in range(18, 30)]
        self.vectors = [getattr(st.regs, f"q{i}")[63:0] for i in range(8, 16)]
        self.tree, self.layer, self.keypair = (
            c.BVS("tree", 64),
            c.BVS("layer", 32),
            c.BVS("keypair", 32),
        )
        self.sk, self.seed = blob("SK_seed", n), blob("PK_seed", n)
        wrbytes(st, KEY, self.sk)
        wrbytes(st, SEED, self.seed)
        for off, size, val in zip(
            (0, 8, 12, 16, 20, 24),
            (8, 4, 4, 4, 4, 4),
            (self.tree, self.layer, 3, self.keypair, 0, 0),
        ):
            put(st, ADRS + off, val, size)
        st.regs.sp, st.regs.lr = STACK, RETURN
        self.events = []
        self.sig = [
            [blob("signature_block", n) for _ in range(a + 1)] for _ in range(k)
        ]
        self.heap_live = False
        if kind in ("sign", "recover"):
            st.regs.x0, st.regs.x1, st.regs.x2 = param, DIGITS, k
            st.regs.x8 = RESULT
            digits = [c.BVS("selection", a).zero_extend(32 - a) for _ in range(k)]
            for i, d in enumerate(digits):
                put(st, DIGITS + 4 * i, d, 4)
            if kind == "sign":
                st.regs.x3, st.regs.x4, st.regs.x5 = KEY, SEED, ADRS
                self.events += [("shim",), ("alloc",)]
            else:
                st.regs.x3, st.regs.x4, st.regs.x5, st.regs.x6 = (
                    SIG,
                    self.length,
                    SEED,
                    ADRS,
                )
                wrbytes(st, SIG, c.Concat(*(b for row in self.sig for b in row)))
                self.sponge = [c.BVV(0, 64) for _ in range(25)]
                self.cursor = 0
                roots_address = c.Concat(
                    self.layer, b32(0), self.tree, b32(4), self.keypair, b32(0), b32(0)
                )
                self.feed(self.seed)
                self.feed(roots_address)
            for first in range(0, k, 2):
                trees = [first, min(first + 1, k - 1)]
                indices = [(i << a) + digits[i] for i in trees]
                if kind == "sign":
                    secret = self.hashes(6, 0, indices, [self.sk] * 2)
                    for lane, t in enumerate(trees[: min(k - first, 2)]):
                        self.sig[t][0] = secret[lane]
                    for level in range(a):
                        # Independent sum in FIPS Alg. 16; the linked code shifts the
                        # global leaf first. This equality includes tree boundaries.
                        sib = [
                            b32((t << (a - level))) + (c.LShR(digits[t], level) ^ 1)
                            for t in trees
                        ]
                        out = self.nodes(sib, level)
                        for lane, t in enumerate(trees[: min(k - first, 2)]):
                            self.sig[t][level + 1] = out[lane]
                else:
                    cur = self.hashes(3, 0, indices, [self.sig[t][0] for t in trees])
                    for level in range(a):
                        data = []
                        for lane, t in enumerate(trees):
                            sib = self.sig[t][level + 1]
                            even = digits[t][level:level] == 0
                            data.append(
                                c.Concat(
                                    c.If(even, cur[lane], sib),
                                    c.If(even, sib, cur[lane]),
                                )
                            )
                        indices = [c.LShR(i, 1) for i in indices]
                        cur = self.hashes(3, level + 1, indices, data)
                    for root in cur[: min(k - first, 2)]:
                        self.feed(root)
            if kind == "recover":
                # In this caller the cursor is always aligned to a whole word.
                self.sponge[self.cursor] = self.sponge[self.cursor] ^ c.BVV(
                    b"\x1f" + bytes(7)
                )
                self.sponge[16] = self.sponge[16] ^ c.BVV(bytes(7) + b"\x80")
                self.root = self.permute_single().get_bytes(0, n)
        else:
            base = kind == "leaf"
            height = b32(0) if base else c.BVS("height", 32)
            self.parent_height = height
            if not base:
                st.add_constraints(c.UGE(height, 1), c.ULE(height, 14))
            ids = [c.BVS("node_index", 32) for _ in range(2)]
            for idx in ids:
                st.add_constraints(c.ULE(idx, c.LShR(b32(2**20 - 1), height)))
            st.regs.x0, st.regs.x1, st.regs.x2, st.regs.x3 = RESULT, KEY, SEED, ADRS
            st.regs.x4, st.regs.x5 = c.Concat(ids[1], ids[0]), height.zero_extend(32)
            if base:
                vals = self.hashes(6, 0, ids, [self.sk] * 2)
            else:
                left = self.nodes([i * 2 for i in ids], height - 1)
                right = self.nodes([2 * i + 1 for i in ids], height - 1)
                vals = [c.Concat(x, y) for x, y in zip(left, right)]
            self.node_result = self.hashes(3, height, ids, vals)
        self.domain = tuple(st.solver.constraints)
        self.check_memory()

    def permute_single(self):
        state = blob("single_permuted", 200)
        self.events.append(("single", c.Concat(*self.sponge), state))
        self.sponge = state.chop(64)
        self.cursor = 0
        return state

    def feed(self, data):
        require(data.size() % 64 == 0, "FORS roots use whole words")
        for word in data.chop(64):
            self.sponge[self.cursor] = self.sponge[self.cursor] ^ word
            self.cursor += 1
            if self.cursor == 17:
                self.permute_single()

    def hashes(self, typ, level, indices, values):
        lanes = []
        for idx, val in zip(indices, values):
            addr = c.Concat(
                self.layer,
                b32(0),
                self.tree,
                b32(typ),
                self.keypair,
                b32(level),
                b32(idx),
            )
            message = c.Concat(self.seed, addr, val)
            used = message.size() // 8
            padded = b"\x1f" + bytes(134 - used) + b"\x80" + bytes(64)
            lanes.append(c.Concat(message, c.BVV(padded)))
        outputs = [blob("Keccak_lane", 200) for _ in range(2)]
        self.events.append(("permute", interleave(lanes), interleave(outputs)))
        return [x.get_bytes(0, self.n) for x in outputs]

    def nodes(self, indices, level):
        out = [blob("subtree_node", self.n) for _ in range(2)]
        self.events.append(("nodes", indices, b32(level), c.Concat(*out)))
        return out

    def check_memory(self):
        self.ro = [
            (KEY, KEY + self.n),
            (SEED, SEED + self.n),
            (ADRS, ADRS + 28),
            (DIGITS, DIGITS + 4 * self.k),
            (self.param, self.param + 36),
        ]
        self.ro.append((self.const[0], sum(self.const)))
        if self.kind == "recover":
            self.ro.append((SIG, SIG + self.length))
        self.rw = [
            (STACK - 8192, STACK),
            (
                RESULT,
                RESULT + ({"sign": 24, "recover": self.n}.get(self.kind, 2 * self.n)),
            ),
        ]
        if self.kind == "sign":
            self.rw.append((HEAP, HEAP + self.length))
        self.st.memory.read_strategies = [SimConcretizationStrategySolutions(2)]

        def watch(st, kind):
            addr = getattr(st.inspect, f"mem_{kind}_address")
            length = getattr(st.inspect, f"mem_{kind}_length")
            size = (
                integer(st, length)
                if length is not None
                else getattr(st.inspect, f"mem_{kind}_expr").size() // 8
            )
            writable = self.rw if self.kind != "sign" or self.heap_live else self.rw[:2]
            ranges = writable + self.ro if kind == "read" else writable
            if not isinstance(addr, int) and addr.symbolic:
                poss = st.solver.eval_upto(addr, 3)
                require(
                    0 < len(poss) <= 2
                    and all(any(l <= p <= r - size for l, r in ranges) for p in poss),
                    "symbolic access",
                )
                require(kind == "read", "data-dependent write")
            else:
                p = addr if isinstance(addr, int) else addr.concrete_value
                require(
                    any(l <= p <= r - size for l, r in ranges),
                    f"{kind} outside modeled regions: {p:#x} ({size})",
                )

        for k in ("read", "write"):
            self.st.inspect.b(
                f"mem_{k}", when=angr.BP_BEFORE, action=lambda st, key=k: watch(st, key)
            )

    def run(self):
        st = self.st
        event = 0
        for step in range(60000):
            pc = st.addr
            if pc == RETURN:
                require(
                    event == len(self.events) and st.solver.satisfiable(),
                    "missing event or infeasible path",
                )
                original = c.Solver()
                original.add(c.And(*self.domain))
                require(
                    not original.satisfiable(
                        extra_constraints=[c.Not(c.And(*st.solver.constraints))]
                    ),
                    "some admissible inputs were dropped",
                )
                for i, reg in enumerate(self.callees, 18):
                    agree(st, getattr(st.regs, f"x{i}"), reg, "saved register")
                for i, reg in enumerate(self.vectors, 8):
                    agree(st, getattr(st.regs, f"q{i}")[63:0], reg, "saved SIMD")
                agree(st, st.regs.sp, STACK, "stack restore")
                if self.kind == "sign":
                    for i, val in enumerate((self.length, HEAP, self.length)):
                        agree(st, unsigned(st, RESULT + 8 * i), val, "FORS Vec")
                    for t, row in enumerate(self.sig):
                        for j, b in enumerate(row):
                            agree(
                                st,
                                load(
                                    st, HEAP + (t * (self.a + 1) + j) * self.n, self.n
                                ),
                                b,
                                "signature block",
                            )
                else:
                    expected = (
                        self.root
                        if self.kind == "recover"
                        else c.Concat(*self.node_result)
                    )
                    agree(
                        st,
                        load(st, RESULT, expected.size() // 8),
                        expected,
                        "returned hash",
                    )
                return step, event
            if pc in self.memory_hooks:
                dest, src, size = [
                    integer(st, getattr(st.regs, f"x{i}")) for i in range(3)
                ]
                count = size if self.memory_hooks[pc] == "memcpy" else 16
                require(
                    0 < size <= 1024 and (src + count <= dest or dest + size <= src),
                    "invalid memory primitive",
                )
                data = load(st, src, count)
                if count != size:
                    require(size % 16 == 0, "nonuniform pattern extent")
                    data = c.Concat(*([data] * (size // 16)))
                wrbytes(st, dest, data)
                clobber_scratch(st)
                if self.memory_hooks[pc] == "memcpy":
                    st.regs.x0 = dest
                st.regs.pc = st.regs.lr
                continue
            name = "nodes" if pc == self.node and step else self.hooks.get(pc)
            if name is None:
                require(
                    any(l <= pc < h for l, h in self.allowed),
                    f"unexpected exit {pc:#x}",
                )
                nxt = self.project.factory.successors(st)
                require(
                    len(nxt.flat_successors) == 1 and not nxt.unconstrained_successors,
                    f"unresolved branch at {pc:#x}",
                )
                st = nxt.flat_successors[0]
                continue
            require(
                event < len(self.events) and self.events[event][0] == name,
                f"unexpected {name} at event {event}",
            )
            _, *args = self.events[event]
            event += 1
            x = [getattr(st.regs, f"x{i}") for i in range(9)]

            def reg(i, val):
                agree(st, x[i], val, "callee x" + str(i))

            def frame(i, size):
                dest = integer(st, x[i])
                sp = integer(st, st.regs.sp)
                require(
                    sp <= dest <= STACK - size
                    or RESULT <= dest <= self.rw[1][1] - size,
                    "callee result buffer",
                )
                return dest

            ret = None
            if name == "alloc":
                reg(0, self.length)
                reg(1, 1)
                ret = HEAP
                require(not self.heap_live, "duplicate allocation")
                self.heap_live = True
                wrbytes(st, HEAP, c.BVV(0, 8 * self.length))
            elif name == "permute":
                p = frame(0, 400)
                agree(st, load(st, p, 400), args[0], "Keccak input bytes/address/order")
                wrbytes(st, p, args[1])
            elif name == "nodes":
                reg(1, KEY)
                reg(2, SEED)
                reg(3, ADRS)
                reg(4, c.Concat(args[0][1], args[0][0]))
                reg(5, args[1].zero_extend(32))
                if self.kind == "step":
                    agree(
                        st,
                        c.ULT(args[1], self.parent_height),
                        True,
                        "recursive height decreases",
                    )
                for idx in args[0]:
                    agree(
                        st,
                        c.ULE(idx, c.LShR(b32(2**20 - 1), args[1])),
                        True,
                        "recursive child bound",
                    )
                wrbytes(st, frame(0, 2 * self.n), args[2])
            elif name == "single":
                p = frame(0, 200)
                agree(
                    st,
                    load(st, p, 200),
                    args[0],
                    "single-state SHAKE root accumulator and padding",
                )
                wrbytes(st, p, args[1])
            clobber_scratch(st)
            if ret is not None:
                st.regs.x0 = ret
            st.regs.pc = st.regs.lr
        raise ValueError("FORS step bound")


def bind_keccak(image):
    # Match the kernel-checked witness to this exact image, including constants
    # and lane schedule, and verify the single-state wrapper used by absorption.
    from check import certificate, ROOT
    from permute import decode
    from single import verify

    address, lanes, table, instructions, layout = decode(image)
    verify(image, address)
    witness = (ROOT / "lean/Spec/AppleKeccakWitness.lean").read_text().split("\n", 1)[1]
    require(
        witness == certificate(lanes, table, instructions, layout),
        "different linked Keccak witness",
    )
    env = dict(
        os.environ,
        PATH=str(Path.home() / ".elan/bin") + os.pathsep + os.environ["PATH"],
    )
    cwd = ROOT / "lean-hw"
    subprocess.run(
        ["lake", "build", "Shakebatch.LinkedFors"],
        cwd=cwd,
        env=env,
        check=True,
        stdout=subprocess.DEVNULL,
    )
    names = [
        "LinkedArm.Fors.short_hash",
        "LinkedArm.Fors.absorb_word",
        "LinkedArm.Digest.finish_eq",
    ]
    query = "import Shakebatch.LinkedFors\n" + "".join(
        f"#print axioms {name}\n" for name in names
    )
    audit = subprocess.check_output(
        ["lake", "env", "lean", "--stdin"], input=query, text=True, cwd=cwd, env=env
    )
    for name in names:
        (axioms,) = re.findall(
            r"^'" + re.escape(name) + r"' depends on axioms: \[([^\]]*)\]", audit, re.M
        )
        require(
            set(map(str.strip, axioms.split(",")))
            <= {"propext", "Classical.choice", "Quot.sound"},
            "unexpected Lean axioms",
        )


def negative_controls(path, image):
    # Address-domain, sibling offset, child orientation, and serialization differ
    # independently. Each mutant remains an executable AArch64 instruction.
    for routine, kind, offset, word, mask, reason in [
        (b"4sign", "sign", 0x18C, 0x528000CB, 1 << 5, "Keccak input"),
        (b"4sign", "sign", 0x24C, 0x52000108, 1 << 10, "callee x4"),
        (b"7recover", "recover", 0x50, 0x52800088, 1 << 5, "single-state"),
        (b"7recover", "recover", 0x280, 0x9A8D0157, 1 << 12, "Keccak input"),
    ]:
        pc, _ = image.function(
            b"10fors_batch" + routine + b"Kj10_EB6_", b"6slhdsa5shake"
        )
        data = bytearray(image.data)
        index = pc + offset - image.base
        require(
            struct.unpack_from("<I", data, index)[0] == word, "unexpected mutation site"
        )
        struct.pack_into("<I", data, index, word ^ mask)
        path.write_bytes(data)
        try:
            Case(path, Image(data), 16, "f", kind).run()
        except ValueError as e:
            require(reason in str(e), f"unexpected mutant rejection: {e}")
        else:
            raise ValueError("mutated FORS program passed")
    print("Rejected four independent FORS mutations", flush=True)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("image", type=Path)
    ap.add_argument("--width", type=int, choices=(16, 24, 32))
    ap.add_argument("--variant", choices=("s", "f"))
    ap.add_argument("--kind", choices=("sign", "recover", "leaf", "step"))
    ap.add_argument(
        "--mutations",
        action="store_true",
        help="check four instruction mutations instead of the positive matrix",
    )
    args = ap.parse_args()
    data = args.image.read_bytes()
    image = Image(data)
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest(), flush=True)
    bind_keccak(image)
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "consumer"
        path.write_bytes(data)
        if args.mutations:
            negative_controls(path, image)
            return
        for n in [args.width] if args.width else (16, 24, 32):
            for v in [args.variant] if args.variant else ("f", "s"):
                for kind in (
                    [args.kind] if args.kind else ("leaf", "step", "sign", "recover")
                ):
                    if kind in ("leaf", "step") and v == "s" and not args.variant:
                        continue
                    steps, events = Case(path, image, n, v, kind).run()
                    print(n, v, kind, steps, events, flush=True)


if __name__ == "__main__":
    main()
