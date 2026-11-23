"""Interpret the normal valid-context paths of the linked Apple SHAKE signing entries.

LLVM decodes instructions from a byte-checked immutable snapshot. Machine words carry
symbolic affine values. Owned byte buffers track their initialized prefix. Allocation
may move that prefix. Normal allocator returns provide enough fresh storage, preserve
initialized bytes and update capacity/pointer. memcpy copies its stated nonoverlapping
slice, deallocation releases the supplied owned buffer, and the signer returns an owned
24-byte Vec descriptor independently of the temporary frame. The valid ABI inputs have
disjoint writable slots, sufficient stack and representable total slice/allocation sizes.
The checker does not assume the framing helper, deterministic seed selection, or signer
argument/return forwarding. Panics, unwinding and allocation failure are outside it.
"""

import copy
import re
import struct
import subprocess
from collections import Counter

from entries import inspect
from hypertree import instructions
from image import require, sign_extend


class Word(tuple):
    """Canonical affine expression. The empty-string coefficient is the constant."""

    def __new__(cls, value=0):
        if isinstance(value, Word):
            return value
        require(isinstance(value, (str, int)), "invalid scalar")
        terms = {value: 1} if isinstance(value, str) else {"": value}
        return tuple.__new__(cls, sorted((k, v) for k, v in terms.items() if v))

    def __deepcopy__(self, memo):
        return self

    def combine(self, other, sign):
        terms = Counter(dict(self))
        for key, count in Word(other):
            terms[key] += sign * count
        return tuple.__new__(Word, sorted((k, v) for k, v in terms.items() if v))

    def __add__(self, other):
        return self.combine(other, 1)

    def __sub__(self, other):
        return self.combine(other, -1)

    def number(self):
        require(all(k == "" for k, _ in self), "expected concrete offset")
        return dict(self).get("", 0)


def at(name, off=0):
    return Word(name) + off


def symbol(image, contains, ends):
    hits = [
        addr for name, addr in image.symbols if contains in name and name.endswith(ends)
    ]
    require(len(hits) == 1 and hits[0] in image.starts, "ambiguous or absent callee")
    return hits[0]


def memcpy_address(image, path):
    listing = subprocess.check_output(
        ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
    )
    imports = {}
    section = None
    for line in listing.splitlines():
        if line.startswith("Indirect symbols for "):
            section = line.split("(", 1)[1].split(")", 1)[0]
        elif re.fullmatch(r"0x[0-9a-f]+\s+\d+\s+_memcpy", line):
            require(section not in imports, "duplicate memcpy import")
            imports[section] = int(line.split()[0], 16)
    stub = imports["__TEXT,__stubs"]
    page, load, branch = struct.unpack("<III", image.read(b"__stubs", stub, 12))
    require(
        page & 0x9F00001F == 0x90000010
        and load & 0xFFC003FF == 0xF9400210
        and branch == 0xD61F0200,
        "unexpected memcpy import stub",
    )
    pages = sign_extend(((page >> 5 & 0x7FFFF) << 2) | (page >> 29 & 3), 21)
    slot = (stub & ~4095) + pages * 4096 + (load >> 10 & 4095) * 8
    require(
        slot == imports["__DATA,__la_symbol_ptr"], "stub does not load bound memcpy"
    )
    return stub


class State:
    def __init__(self, frame, m_empty, c_empty, width, deterministic):
        self.frame, self.width, self.deterministic = frame, width, deterministic
        self.m = Word(0 if m_empty else "m.length")
        self.c = Word(0 if c_empty else "ctx.length")
        self.reg = {f"x{i}": Word(f"entry.x{i}") for i in range(31)}
        self.reg.update(
            sp=Word("sp"),
            x0=Word("m"),
            x1=self.m,
            x2=Word("ctx"),
            x3=self.c,
            x4=Word("sk"),
            x5=Word("rand"),
            x8=Word("out"),
        )
        self.memory = {}
        self.low = 0
        self.flags = None
        self.calls = []
        self.events = []
        self.written = Word(0)
        self.capacity = Word(0)
        self.buf = Word(1)
        self.min_capacity = Word(0)
        self.growth = 0

    def value(self, reg):
        if reg.startswith("#"):
            return Word(int(reg[1:], 0))
        if reg in ("xzr", "wzr"):
            return Word(0)
        if reg.startswith("w"):
            full = self.value("x" + reg[1:])
            if full == self.c:
                return full  # valid contexts fit in one byte
            return Word(full.number() & 0xFFFFFFFF)
        require(reg in self.reg, "reading clobbered register " + reg)
        return self.reg[reg]

    def put(self, reg, val):
        if reg.startswith("w"):
            val = Word(val.number() & 0xFFFFFFFF)
            reg = "x" + reg[1:]
        self.reg[reg] = val

    def cells(self, addr, count, store):
        # All scalar/q spills comprise one or two aligned little-endian 64-bit cells.
        keys = [addr + off for off in range(0, count, 8)]
        for key in keys:
            if dict(key).get("sp"):
                off = (key - Word("sp")).number()
                require(
                    off % 8 == 0 and self.low <= off <= -8, "out-of-frame stack access"
                )
            elif dict(key).get("out"):
                require(
                    store and (key - Word("out")).number() in (0, 8, 16),
                    "bad sret access",
                )
            elif dict(key).get("sk"):
                off = (key - Word("sk")).number()
                require(
                    not store and off % 8 == 0 and 0 <= off <= 4 * self.width - 8,
                    "bad secret-key access",
                )
                self.memory[key] = Word(f"sk.word.{off}")
            else:
                raise ValueError("unmodeled word access")
        return keys

    def store(self, addr, values):
        self.memory.update(zip(self.cells(addr, 8 * len(values), True), values))

    def load(self, addr, count):
        keys = self.cells(addr, count, False)
        require(all(k in self.memory for k in keys), "read of uninitialized word")
        return tuple(self.memory[k] for k in keys)

    def clobber(self):
        for name in [
            *(f"x{i}" for i in range(19)),
            "x30",
            *(f"q{i}" for i in range(32)),
        ]:
            self.reg.pop(name, None)
        self.flags = None

    def append(self, dst, part, length):
        require(
            dst == self.buf + self.written,
            "write does not append at the frame frontier",
        )
        require(
            self.min_capacity == self.written + length,
            "missing capacity proof for frame write",
        )
        if length:
            self.events.append(part)
        self.written += length

    def call(self, kind, extra):
        v = self.value
        if kind in ("grow", "reserve"):
            header = v("x0")
            cap, ptr, length = self.load(header, 24)
            require(
                (cap, ptr, length) == (self.capacity, self.buf, self.written),
                "allocator received incorrect Vec or initialized length",
            )
            if kind == "grow":
                needed = length + 1
                require(length in (Word(0), Word(1)), "unexpected push allocation")
            else:
                require(
                    (v("x1"), v("x3"), v("x4")) == (length, Word(1), Word(1)),
                    "incorrect reserve length, element size or alignment",
                )
                needed = length + v("x2")
            self.growth += 1
            self.buf = Word(f"heap.{self.growth}")
            self.capacity = Word(f"cap.{self.growth}")
            self.min_capacity = needed
            self.store(header, [self.capacity, self.buf])
        elif kind == "memcpy":
            src, length = v("x1"), v("x2")
            require(
                (src, length) in [(Word("ctx"), self.c), (Word("m"), self.m)],
                "memcpy source or length is wrong",
            )
            self.append(v("x0"), "ctx" if src == Word("ctx") else "m", length)
        elif kind == "frame":
            require(
                [v(f"x{i}") for i in range(4)]
                == [Word("m"), self.m, Word("ctx"), self.c],
                "incorrect message/context forwarding",
            )
            self.store(
                v("x8"), [Word("frame.cap"), Word("frame.ptr"), self.c + self.m + 2]
            )
            self.calls.append(kind)
        elif kind == "sign":
            require(
                [v(f"x{i}") for i in range(5)]
                == [
                    Word(extra),
                    Word("frame.ptr"),
                    self.c + self.m + 2,
                    Word("sk"),
                    Word(4 * self.width),
                ],
                "incorrect signer row, framed slice, or secret-key arguments",
            )
            if self.deterministic:
                expected = tuple(
                    Word(f"sk.word.{2 * self.width + i}")
                    for i in range(0, self.width, 8)
                )
                require(
                    self.load(v("x5"), self.width) == expected,
                    "incorrect PK.seed randomizer",
                )
            else:
                require(v("x5") == Word("rand"), "incorrect hedging randomizer")
            self.store(v("x8"), [Word("sig.cap"), Word("sig.ptr"), Word("sig.len")])
            self.calls.append(kind)
        elif kind == "free":
            require(
                [v(f"x{i}") for i in range(3)]
                == [Word("frame.ptr"), Word("frame.cap"), Word(1)],
                "wrong deallocation",
            )
            self.calls.append(kind)
        else:
            raise ValueError("unrecognized reachable call")
        self.clobber()

    def returned(self):
        require(
            self.value("sp") == Word("sp")
            and all(self.value(f"x{i}") == Word(f"entry.x{i}") for i in range(19, 31)),
            "failed to restore stack or callee-saved state",
        )
        descriptor = [self.memory[at("out", off)] for off in (0, 8, 16)]
        if self.frame:
            require(
                descriptor == [self.capacity, self.buf, self.c + self.m + 2]
                and self.written == self.c + self.m + 2,
                "invalid frame result",
            )
            expect = (
                ["zero", "ctxLen"]
                + (["ctx"] if self.c else [])
                + (["m"] if self.m else [])
            )
            require(
                self.events == expect, "frame does not contain FIPS 205 pure message"
            )
        else:
            require(
                descriptor == [Word("sig.cap"), Word("sig.ptr"), Word("sig.len")]
                and self.calls == ["frame", "sign", "free"],
                "incorrect signature result or cleanup",
            )


def paths(
    image, path, pc, words, callees, frame, width=0, deterministic=False, params=0
):
    decoded = instructions(path, pc, words)
    pending = [
        (0, State(frame, m, c, width, deterministic), frozenset())
        for m in (False, True)
        for c in (False, True)
    ]
    returns = []
    while pending:
        i, s, visited = pending.pop()
        while True:
            require(
                i in decoded and i not in visited, "cycle or branch outside function"
            )
            visited = visited | {i}
            op, operands = decoded[i]
            args = operands.split(" <")[0].split(", ") if operands else []
            w = words[i]
            next_i = i + 1
            if op == "mov":
                s.put(args[0], s.value(args[1]))
            elif op in ("add", "sub"):
                a, b = (s.value(r) for r in args[1:])
                result = a + b if op == "add" else a - b
                s.put(args[0], result)
                if args[0] == "sp":
                    offset = (result - Word("sp")).number()
                    require(offset <= 0 and offset % 16 == 0, "misaligned stack")
                    s.low = offset
            elif op == "adrp":
                require(w & 0x9F000000 == 0x90000000, "bad address opcode")
                delta = sign_extend((w >> 5 & 0x7FFFF) << 2 | (w >> 29 & 3), 21)
                s.put(args[0], Word(((pc + 4 * i) & ~4095) + delta * 4096))
            elif op in ("ldp", "stp", "ldr", "ldur", "str", "strb"):
                m = re.fullmatch(r"(.*), \[(\w+)(?:, #(-?0x[0-9a-f]+))?\]", operands)
                require(m is not None, "unsupported addressing mode")
                addr = s.value(m[2]) + int(m[3] or "0", 0)
                registers = m[1].split(", ")
                if op == "strb":
                    val = s.value(registers[0])
                    if s.written == Word(0):
                        require(val == Word(0), "incorrect framing domain")
                        tag = "zero"
                    else:
                        require(
                            s.written == Word(1) and val == s.c,
                            "incorrect context-length byte",
                        )
                        tag = "ctxLen"
                    s.append(addr, tag, Word(1))
                else:
                    require(
                        len(registers) == (2 if op in ("ldp", "stp") else 1),
                        "invalid operands",
                    )
                    for r in registers:
                        require(r.startswith(("x", "q")), "unsupported register width")
                        simd = r.startswith("q")
                        size = 16 if simd else 8
                        if op.startswith("ld"):
                            values = s.load(addr, size)
                            s.put(r, values if simd else values[0])
                        else:
                            value = s.value(r)
                            s.store(addr, value if simd else (value,))
                        addr += size
            elif op == "cmp":
                s.flags = (s.value(args[0]), s.value(args[1]))
            elif op == "bl":
                require(w & 0xFC000000 == 0x94000000, "bad call opcode")
                dst = pc + 4 * (i + sign_extend(w & 0x3FFFFFF, 26))
                s.call(callees.get(dst), params)
            elif op == "b":
                next_i = i + sign_extend(w & 0x3FFFFFF, 26)
            elif op in ("b.ls", "b.ne", "b.hi", "cbz"):
                target = i + sign_extend(w >> 5 & 0x7FFFF, 19)
                if op == "cbz":
                    val = s.value(args[0])
                    if val in (s.c, s.m):
                        take = not val
                    else:
                        require(val == Word("frame.cap"), "unexpected null check")
                        take = False  # frame has at least two initialized bytes
                    if take:
                        next_i = target
                else:
                    require(s.flags is not None, "condition depends on clobbered flags")
                    left, right = s.flags
                    if op == "b.ls":
                        require(
                            not frame and (left, right) == (s.c, Word(255)),
                            "wrong context guard",
                        )
                        next_i = target  # theorem assumes 0 <= ctx.length <= 255
                    elif op == "b.ne":
                        require(
                            frame
                            and (left, right) == (s.capacity, Word(1))
                            and s.min_capacity == Word(1),
                            "invalid grow condition",
                        )
                        taken = copy.deepcopy(s)
                        taken.min_capacity = Word(2)
                        pending.append((target, taken, visited))
                    else:
                        require(
                            frame
                            and left in (s.c, s.m)
                            and right == s.capacity - s.written
                            and s.min_capacity == s.written,
                            "invalid capacity check",
                        )
                        if left:
                            pending.append((target, copy.deepcopy(s), visited))
                        s.min_capacity = s.written + left
            elif op == "ret":
                require(w == 0xD65F03C0, "unsupported return register")
                s.returned()
                returns.append((bool(s.m), bool(s.c), tuple(s.events)))
                break
            else:
                raise ValueError("unmodeled pure-sign instruction " + op)
            i = next_i
    return returns


def verify(image, path):
    frame_pc, words = image.function(b"12with_context", b"6slhdsa5shake3slh")
    callees = {
        memcpy_address(image, path): "memcpy",
        symbol(image, b"5alloc7raw_vec", b"6RawVechE8grow_oneB7_"): "grow",
        symbol(image, b"7reserve21do_reserve_and_handle", b"6slhdsa"): "reserve",
    }
    frame_paths = paths(image, path, frame_pc, words, callees, True)
    free = symbol(image, b"___rustc", b"___rust_dealloc")
    for n in (16, 24, 32):
        mono = f"Kj{n:x}_EB6_".encode()
        core = b"6slhdsa5shake3slh17slh_sign_internal" + mono
        core_pc, _ = image.function(core, b"6slhdsa")
        for variant in ("s", "f"):
            prefix = f"6slhdsa4sets10shake_{n * 8}{variant}".encode()
            internal = prefix + b"17slh_sign_internal"
            verified_row = inspect(
                image, internal, core, [None, "x0", "x1", "x2", 4 * n, "x3"]
            )
            for op in (b"4sign", b"8slh_sign", b"18sign_deterministic"):
                entry, code = image.function(prefix + op, b"6slhdsa4sets")
                # Resolve the constant from the wrapper, then bind its contents to
                # the FIPS row already checked by entries.certificate.
                candidates = []
                for j, w in enumerate(code[:-1]):
                    if w & 0x9F00001F == 0x90000000:
                        add = code[j + 1]
                        require(
                            add & 0xFFC003FF == 0x91000000,
                            "unexpected parameter relocation",
                        )
                        delta = sign_extend((w >> 5 & 0x7FFFF) << 2 | (w >> 29 & 3), 21)
                        candidates.append(
                            ((entry + 4 * j) & ~4095)
                            + delta * 4096
                            + (add >> 10 & 4095)
                        )
                require(len(candidates) == 1, "wrong number of parameter loads")
                params = candidates[0]
                require(
                    struct.unpack("<QQIIIII", image.read(b"__const", params, 36))
                    == verified_row,
                    "incorrect FIPS parameter row",
                )
                paths(
                    image,
                    path,
                    entry,
                    code,
                    {frame_pc: "frame", core_pc: "sign", free: "free"},
                    False,
                    n,
                    op == b"18sign_deterministic",
                    params,
                )
    return frame_certificate(frame_paths)


def frame_certificate(traces):
    # Each reachable symbolic trace supplies its own byte expression to Lean.
    lines = ["import Spec.SlhDsa", "namespace LinkedPureMessage"]
    tags = {
        "zero": "[0]",
        "ctxLen": "[BitVec.ofNat 8 ctx.length]",
        "ctx": "ctx",
        "m": "m",
    }
    for m_nonempty, ctx_nonempty, events in sorted(set(traces)):
        expr = " ++ ".join(tags[x] for x in events)
        hyps = ("" if m_nonempty else "(hm : m = []) ") + (
            "" if ctx_nonempty else "(hc : ctx = []) "
        )
        lines.append(
            f"example (m ctx : Spec.Bytes) {hyps}: {expr} = Spec.withContext m ctx := by"
        )
        if not m_nonempty:
            lines.append("  subst m")
        if not ctx_nonempty:
            lines.append("  subst ctx")
        lines.append("  simp [Spec.withContext, Spec.toByte, List.range_succ]")
    lines.append("end LinkedPureMessage")
    return "\n".join(lines) + "\n"


def mutation_tests(image, scratch):
    from image import Image

    # Mutate the framing domain, context memcpy length, PK.seed source, and
    # returned signature descriptor. Each altered instruction still decodes.
    mutations = [
        (b"12with_context", b"6slhdsa5shake3slh", 17, 31 ^ 22, "framing domain"),
        (
            b"12with_context",
            b"6slhdsa5shake3slh",
            38,
            (22 ^ 20) << 16,
            "memcpy source or length",
        ),
        (b"18sign_deterministic", b"6slhdsa4sets10shake_128s", 6, 1 << 10, "PK.seed"),
        (b"4sign", b"6slhdsa4sets10shake_128s", 26, 1 << 10, "signature result"),
    ]
    for suffix, family, index, mask, expected in mutations:
        start, words = image.function(suffix, family)
        off = start - image.base + 4 * index
        bad = bytearray(image.data)
        struct.pack_into("<I", bad, off, words[index] ^ mask)
        path = scratch / "mutated-signing-consumer"
        path.write_bytes(bad)
        try:
            verify(Image(bad), path)
        except ValueError as err:
            require(expected in str(err), f"unexpected signing mutation result: {err}")
        else:
            raise AssertionError(f"accepted mutation of {expected}")
