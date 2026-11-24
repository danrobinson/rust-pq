# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Machine-code correspondence for the SHA-2 signer for messages of at least 1024 bytes.

Run with uv on the linked Apple ACVP executable. For each FIPS profile, VEX checks
all feasible paths with arbitrary key blocks, randomness bytes, valid contexts,
message length and abstract hash/subroutine outputs. The SHA comparators implement
the kstep equations in Hw/Model.lean and Hw512/Rounds.lean, sharing uninterpreted
instruction results between native and reference circuits. The segmented SHA
continuation and digest bodies, FORS, hypertree and runtime allocation/copy routines
are contracts at their checked arguments. ABI, successful allocation and memory
address assumptions follow driver.py.
"""

import argparse
import hashlib
import re
import struct
import sys
import tempfile

sys.dont_write_bytecode = True
from pathlib import Path

from driver import (
    CONTEXT,
    KEY,
    MESSAGE,
    RANDOM,
    RETURN,
    Contract,
    Driver,
    Image,
    angr,
    blob,
    c,
    clobber_scratch,
    equal,
    guard_access,
    integer,
    load,
    objects,
    require,
    unsigned,
    wrbytes,
)
from hypertree import instructions
from sha256_seed import SeedCompression, vector


def lanes(x, bits):
    return [x[i + bits - 1 : i] for i in range(0, x.size(), bits)]


class Compression(SeedCompression):
    """The Lean kstep rounds on symbolic words, sharing instruction applications with VEX."""

    def __init__(self, n, seed):
        self.applications = seed.applications if seed is not None else {}
        self.bits = bits = 32 if n == 16 else 64
        src = (
            Path(__file__).resolve().parents[2] / f"lean/Spec/Sha{bits * 8}.lean"
        ).read_text()

        def words(name):
            t = src.split(f"def {name} : List Word := [", 1)[1].split("]", 1)[0]
            return [c.BVV(int(x, 16), bits) for x in re.findall(rf"0x(\w+)#{bits}", t)]

        self.initial, self.k = words("H0"), words("K")
        require(
            len(self.initial) == 8 and len(self.k) == (64 if bits == 32 else 80),
            "SHA constants",
        )

    def block(self, initial, block):
        bits = self.bits
        step = 128 // bits

        def add(a, b):
            return vector([x + y for x, y in zip(lanes(a, bits), lanes(b, bits))])

        def ext(a, b):
            return vector([lanes(a, 64)[1], lanes(b, 64)[0]])

        state = [vector(initial[j : j + step]) for j in range(0, 8, step)]
        msg = [
            vector(
                [
                    block.get_bytes(off + offset, bits // 8)
                    for offset in range(0, 16, bits // 8)
                ]
            )
            for off in range(0, block.size() // 8, 16)
        ]
        require(len(msg) == (4 if bits == 32 else 8), "one SHA block")
        original = state[:]
        for i in range(len(self.k) // step):
            j = i % len(msg)
            wk = add(msg[j], vector(self.k[i * step : (i + 1) * step]))
            if bits == 32:
                ab, ef = state
                state = [self.op("H", ab, ef, wk), self.op("H2", ef, ab, wk)]
                if i < 12:
                    su = self.op("SU0", msg[j], msg[(j + 1) % 4])
                    msg[j] = self.op("SU1", su, msg[(j + 2) % 4], msg[(j + 3) % 4])
            else:
                ab, cd, ef, gh = state
                t = self.op("H", add(ext(wk, wk), gh), ext(ef, gh), ext(cd, ef))
                state = [self.op("H2", t, cd, ab), ab, add(cd, t), ef]
                if i < 32:
                    su = self.op("SU0", msg[j], msg[(j + 1) % 8])
                    msg[j] = self.op(
                        "SU1",
                        su,
                        msg[(j + 7) % 8],
                        ext(msg[(j + 4) % 8], msg[(j + 5) % 8]),
                    )
        return [
            x for old, new in zip(original, state) for x in lanes(add(old, new), bits)
        ]

    def op(self, opcode, *values):
        key = (opcode, *(c.simplify(v) for v in values))
        if getattr(self, "index", None) is not None and key not in self.applications:
            # Different instruction order can commute lane additions. Reuse an
            # abstract instruction result only after proving all operands equal.
            for previous in self.index.get(
                (opcode, tuple(v.variables for v in key[1:])), ()
            ):
                mismatch = c.Or(*(a != b for a, b in zip(key[1:], previous[1:])))
                if not c.Solver().satisfiable(extra_constraints=[mismatch]):
                    self.applications[key] = self.applications[previous]
                    break
        return super().op(opcode, *values)

    def hooks(self, project, path, pc, words):
        self.index = {}
        for previous in self.applications:
            self.index.setdefault(
                (previous[0], tuple(v.variables for v in previous[1:])), []
            ).append(previous)
        if self.bits == 32:
            self.install(project, pc, words)
            return
        decoded = instructions(path, pc, words)
        for i, w in enumerate(words):
            op, _ = decoded[i]
            if op == "eor.8b":
                require(w & 0xFFE0FC00 == 0x2E201C00, "bad EOR.8B")

                def eor8(s, word=w):
                    x = getattr(s.regs, f"q{word >> 5 & 31}")[63:0]
                    y = getattr(s.regs, f"q{word >> 16 & 31}")[63:0]
                    setattr(s.regs, f"q{word & 31}", (x ^ y).zero_extend(64))

                project.hook(pc + 4 * i, eor8, length=4)
            elif op == "movi.8b":
                imm = ((w >> 16 & 7) << 5) | (w >> 5 & 31)
                require(w & 0xFFF8FC00 == 0x0F00E400, "bad MOVI.8B")

                def mov8(s, word=w, value=imm):
                    setattr(
                        s.regs,
                        f"q{word & 31}",
                        c.BVV(int.from_bytes(bytes([value]) * 8), 128),
                    )

                project.hook(pc + 4 * i, mov8, length=4)
            elif op == "rev64.8b":
                require(w & 0xFFFFFC00 == 0x0E200800, "bad REV64.8B")

                def rev8(s, word=w):
                    x = getattr(s.regs, f"q{word >> 5 & 31}")[63:0]
                    setattr(s.regs, f"q{word & 31}", x.reversed.zero_extend(64))

                project.hook(pc + 4 * i, rev8, length=4)
            elif op == "rev64.16b":
                require(w & 0xFFFFFC00 == 0x4E200800, "bad REV64.16B")

                def rev(s, word=w):
                    x = getattr(s.regs, f"q{word >> 5 & 31}")
                    setattr(
                        s.regs,
                        f"q{word & 31}",
                        vector([v.reversed for v in lanes(x, 64)]),
                    )

                project.hook(pc + 4 * i, rev, length=4)
            elif op.startswith("sha512"):
                name = op.split(".")[0][6:].upper()
                require(
                    name in ("H", "H2", "SU0", "SU1"), "unsupported SHA-512 instruction"
                )

                mask = 0xFFFFFC00 if name == "SU0" else 0xFFE0FC00
                opcode = {
                    "H": 0xCE608000,
                    "H2": 0xCE608400,
                    "SU0": 0xCEC08000,
                    "SU1": 0xCE608800,
                }
                require(w & mask == opcode[name], "bad SHA-512 operand encoding")

                def step(s, word=w, label=name):
                    regs = [
                        getattr(s.regs, f"q{j}")
                        for j in (word & 31, word >> 5 & 31, word >> 16 & 31)
                    ]
                    setattr(
                        s.regs,
                        f"q{word & 31}",
                        self.op(label, *regs[: 2 if label == "SU0" else 3]),
                    )

                project.hook(pc + 4 * i, step, length=4)


class Segmented(Driver):
    def __init__(self, row, param):
        super().__init__(row, param, "slh_sign_internal", "sha2")
        self.sha = Compression(self.n, self.inline_seed)
        block = self.sha.bits * 2
        key = c.Concat(self.sk[1], c.BVV(0, 8 * (block - self.n)))

        def pad(byte):
            return c.BVV(bytes([byte]) * block)

        ipad = self.sha.block(self.sha.initial, key ^ pad(0x36))
        self.ipad = c.Concat(*(x.reversed for x in ipad))
        opad = self.sha.block(self.sha.initial, key ^ pad(0x5C))
        self.inner = blob("segmented_inner_digest", block // 2)
        padding = b"\x80" + bytes(block // 2 - 3) + (12 * block).to_bytes(2, "big")
        outer = self.sha.block(opad, c.Concat(self.inner, c.BVV(padding)))
        self.r = c.Concat(*outer).get_bytes(0, self.n)
        self.schedule = ("continued", "seg_digest") + self.schedule[2:]
        self.context = blob("context", 255)

    def start(self, s):
        super().start(s)
        for i, v in enumerate(
            [
                self.param,
                MESSAGE,
                self.msglen,
                CONTEXT,
                self.ctxlen,
                KEY,
                4 * self.n,
                RANDOM,
            ]
        ):
            setattr(s.regs, f"x{i}", v)
        s.add_constraints(c.UGE(self.msglen, 1024), c.ULE(self.ctxlen, 255))
        wrbytes(s, CONTEXT, self.context)

    def call(self, s, name):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        count = len(s.globals["calls"])
        if name == "copy" and count == 0:
            dst = integer(s, x[0])
            equal(s, x[1], CONTEXT, "HMAC prefix copy source")
            equal(s, x[2], self.ctxlen, "HMAC prefix copy length")
            self.workspace(s, dst, 255)
            for i in range(255):
                val = c.If(
                    c.ULT(i, self.ctxlen), self.context.get_byte(i), load(s, dst + i, 1)
                )
                wrbytes(s, dst + i, val)
        elif name in ("continued", "seg_digest"):
            require(
                count < len(self.schedule) and self.schedule[count] == name,
                "segmented hash call order",
            )
            s.globals["calls"] += (name,)
            if name == "continued":
                block = self.sha.bits * 2
                equal(
                    s,
                    load(s, x[1], block // 2),
                    self.ipad,
                    "HMAC inner key-derived state",
                )
                equal(s, x[2], block, "inner absorbed byte count")
                pre = integer(s, x[3])
                equal(s, load(s, pre, self.n), self.rand, "prefix randomizer")
                equal(
                    s,
                    load(s, pre + self.n, 2),
                    self.ctxlen[15:0],
                    "framing domain and length",
                )
                mismatches = [
                    c.And(
                        c.ULT(i, self.ctxlen),
                        load(s, pre + self.n + 2 + i, 1) != self.context.get_byte(i),
                    )
                    for i in range(255)
                ]
                equal(s, c.Or(*mismatches), False, "all live context bytes")
                equal(s, x[4], self.ctxlen + self.n + 2, "prefix length")
                equal(s, x[5], MESSAGE, "continued message")
                equal(s, x[6], self.msglen, "continued message length")
                wrbytes(s, self.workspace(s, x[0], block // 2), self.inner)
            else:
                equal(s, x[1], self.m, "H_msg output width")
                for reg, value in [(2, self.r), (3, self.sk[2]), (4, self.sk[3])]:
                    equal(s, load(s, x[reg], self.n), value, "H_msg R, seed or root")
                equal(s, x[5], CONTEXT, "H_msg context")
                equal(s, x[6], self.ctxlen, "H_msg context length")
                equal(s, x[7], MESSAGE, "H_msg message")
                equal(s, unsigned(s, s.regs.sp), self.msglen, "H_msg message length")
                self.vec(s, integer(s, x[0]), "digest", self.m, 1, [(0, self.digest)])
        else:
            return super().call(s, name)
        clobber_scratch(s)


def execute(path, image, pc, words, hooks, driver):
    end = pc + 4 * len(words)
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    driver.sha.hooks(project, path, pc, words)
    driver.constants_range = image.sections[b"__const"][:2]
    for addr, label in hooks.items():
        project.hook(addr, Contract(driver=driver, label=label))
    s = project.factory.blank_state(
        addr=pc,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    driver.start(s)

    def guard(s, kind):
        if not s.globals.get("in_driver"):
            return
        ptr = integer(s, getattr(s.inspect, f"mem_{kind}_address"))
        length = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
        if hasattr(driver, "extra_access") and driver.extra_access(
            s, kind, ptr, length
        ):
            return
        if kind == "read" and RANDOM <= ptr and ptr + length <= RANDOM + driver.n:
            return
        return guard_access(s, kind, driver)

    for kind in ("read", "write"):
        s.inspect.b(
            "mem_" + kind, when=angr.BP_BEFORE, action=lambda st, k=kind: guard(st, k)
        )
    todo = [s]
    while todo:
        s = todo.pop()
        visits = s.globals.get("blocks", 0) + 1
        require(visits < 5000, "unbounded execution")
        s.globals["blocks"] = visits
        s.globals["in_driver"] = False
        if s.addr == RETURN:
            driver.finish(s)
            continue
        s.globals["in_driver"] = pc <= s.addr < end
        require(
            s.addr in hooks or s.globals["in_driver"], f"unexpected exit {s.addr:#x}"
        )
        try:
            succ = project.factory.successors(s)
        except Exception as e:
            e.add_note(f"At {s.addr:#x} (word {(s.addr - pc) // 4})")
            raise
        require(
            not succ.unconstrained_successors and succ.flat_successors,
            "unexpected termination",
        )
        todo.extend(succ.flat_successors)


def verify(path, image, n, v):
    row, param, _, _, hooks = objects(path, image, n, v, "sha2")
    driver = Segmented(row, param)
    suffix = f"Kj{n:x}_EB6_".encode()
    pc, words = image.function(b"3slh7message4sign" + suffix, b"6slhdsa")
    bits = driver.sha.bits
    inner = f"9continuedKj{bits * 2:x}_NtB2_6Sha{bits * 8}EB6_".encode()
    hooks[image.function(inner, b"6slhdsa3slh7message")[0]] = "continued"
    hooks[image.function(b"6digest" + suffix, b"6slhdsa3slh7message")[0]] = "seg_digest"
    execute(path, image, pc, words, hooks, driver)
    require(driver.final_paths == 4, "allocation path coverage")
    print(
        f"SHA2-{8 * n}{v}: segmented Algorithm 19, four output allocation paths",
        flush=True,
    )


def mutation_tests(image):
    # Independent defects in the prefix, inner SHA-512 and H_msg message pointer.
    tests = [
        (16, 47, 31 ^ 20, "framing domain and length"),
        (24, 68, 1 << 5, "HMAC inner key-derived state"),
        (32, 271, 1 << 10, "H_msg message"),
    ]
    with tempfile.TemporaryDirectory() as folder:
        for n, i, mask, message in tests:
            pc, words = image.function(
                f"3slh7message4signKj{n:x}_EB6_".encode(), b"6slhdsa"
            )
            data = bytearray(image.data)
            struct.pack_into("<I", data, pc - image.base + 4 * i, words[i] ^ mask)
            candidate = Path(folder) / "altered-signer"
            candidate.write_bytes(data)
            try:
                verify(candidate, Image(data), n, "s")
            except ValueError as err:
                require(message in str(err), f"unexpected mutation failure: {err}")
            else:
                raise AssertionError(f"accepted alteration to {message}")


if __name__ == "__main__":
    args = argparse.ArgumentParser()
    args.add_argument("binary", type=Path)
    args.add_argument("--width", type=int, choices=(16, 24, 32))
    args.add_argument("--variant", choices=("s", "f"))
    args.add_argument("--self-test", action="store_true")
    a = args.parse_args()
    image = Image(a.binary.read_bytes())
    for n in [a.width] if a.width else [16, 24, 32]:
        for v in [a.variant] if a.variant else ["s", "f"]:
            verify(a.binary, image, n, v)

    if a.self_test:
        mutation_tests(image)
        print("Rejected three mutations of the segmented signer")
    print("Mach-O SHA-256", hashlib.sha256(image.data).hexdigest())
