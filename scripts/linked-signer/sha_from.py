# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Prove the Apple arm64 SHA-from-state callers implement Merkle–Damgård finalization.

Each residue class uses arbitrary tail bytes, chaining state, complete-block
count and aligned prefix length within the representable FIPS byte domain.
The bulk slice is an abstract valid input disjoint from the stack, output and
allocator. The copy contract supplies its arbitrary suffix and the compressor
contract supplies the state for its exact pointer and block count. The exact
linked compressor bodies are separately bound to the Lean-proved register
programs. Allocation, resize, deallocation and memcpy assume successful Rust/
C ABI semantics. RawVec growth decisions run as linked instructions.
"""

import argparse
import hashlib
import struct
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

sys.dont_write_bytecode = True

from angr.engines.vex.claripy import irop
from driver import (
    HEAP,
    KEY,
    MESSAGE,
    RESULT,
    RETURN,
    STACK,
    STRIDE,
    Contract,
    Driver,
    Image,
    angr,
    blob,
    c,
    clobber_scratch,
    equal,
    integer,
    load,
    objects,
    put,
    require,
    wrbytes,
)
from hypertree import instructions
from pure_sign import memcpy_address
from sha2 import verify as verify_compressor


# libvex_ir.h specifies a signed low-byte count per lane. For negative
# counts the unsigned variant shifts right and fills with zero.
def vector_shift(op, args):
    data, counts = args
    width = op._vector_size
    lanes = []
    for i in range(128 // width):
        word = data.get_bytes(i * width // 8, width // 8)
        count = counts.get_bytes((i + 1) * width // 8 - 1, 1)
        right = c.ZeroExt(width - 8, -count)
        left = c.ZeroExt(width - 8, count)
        lanes.append(c.If(count[7] == 1, c.LShR(word, right), word << left))
    return c.Concat(*lanes)


for op in ("Iop_Sh32Ux4", "Iop_Sh64Ux2"):
    setattr(irop.SimIROp, "_op_" + op, vector_shift)


class Padding(Driver):
    def __init__(self, path, image, bits):
        n = 16 if bits == 256 else 32
        row, param, *_ = objects(path, image, n, "s", "sha2")
        super().__init__(row, param, "slh_sign_internal", "sha2")
        self.bits = bits
        self.block = bits // 4
        self.word = bits // 64
        self.digestlen = bits // 8
        self.initial = blob("input_chaining_state", self.digestlen)
        self.full = blob("state_after_complete_message_blocks", self.digestlen)
        self.final = blob("state_after_padding_blocks", self.digestlen)
        self.pre = c.BVS("aligned_prefix", 64)
        self.count = c.BVS("complete_blocks", 64)
        self.constants_range = image.sections[b"__const"][:2]

    def start_case(self, s, r):
        super().start(s)
        self.rsize = r
        self.tail = blob("final_message_bytes", r) if r else None
        length = self.count * self.block + r
        # Valid slice, aligned and nonwrapping prior byte count. SHA-256's
        # 64-bit length field further requires fewer than 2^64 input bits.
        limit = (1 << 61) - 1 if self.bits == 256 else (1 << 64) - 1
        s.add_constraints(
            c.ULE(self.count, ((1 << 63) - 1 - r) // self.block),
            c.ULE(self.pre, limit - length),
            c.ULE(length, limit),
            self.pre % self.block == 0,
        )
        wrbytes(s, KEY, self.initial)
        s.regs.x0, s.regs.x1, s.regs.x2, s.regs.x3 = KEY, self.pre, MESSAGE, length
        s.regs.x8 = RESULT
        total = (self.pre + length).zero_extend(self.bits // 4 - 64) * 8
        zeros = (-r - 1 - self.bits // 32) % self.block
        pieces = ([self.tail] if r else []) + [c.BVV(b"\x80" + bytes(zeros)), total]
        self.padding = c.Concat(*pieces)

    def call(self, s, kind):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        alloc = dict(s.globals["allocations"])
        if kind == "compress":
            count = len(s.globals["calls"])
            p = self.workspace(s, x[0], self.digestlen)
            if count == 0:
                equal(s, load(s, p, self.digestlen), self.initial, "initial SHA state")
                equal(s, x[1], MESSAGE, "bulk SHA input")
                equal(s, x[2], self.count, "number of complete blocks")
                result = c.If(self.count == 0, self.initial, self.full)
                s.globals["bulk_state"] = result
            else:
                require(count == 1, "extra compression call")
                equal(
                    s,
                    load(s, p, self.digestlen),
                    s.globals["bulk_state"],
                    "padding chains from bulk state",
                )
                ptr = integer(s, x[1])
                require(str(ptr) in alloc, "live padding array")
                size = self.padding.size() // 8
                require(alloc[str(ptr)][0] >= size, "initialized padding fits capacity")
                equal(s, x[2], size // self.block, "one or two padding blocks")
                equal(
                    s,
                    load(s, ptr, size),
                    self.padding,
                    "complete FIPS padding and bit length",
                )
                result = self.final
            wrbytes(s, p, result)
            s.globals["calls"] += (kind,)
        elif kind == "copy":
            require(self.rsize > 0, "copy for empty suffix")
            dst = integer(s, x[0])
            require(
                str(dst) in alloc and alloc[str(dst)][0] >= self.rsize,
                "tail destination",
            )
            equal(s, x[1], MESSAGE + self.count * self.block, "tail start")
            equal(s, x[2], self.rsize, "tail length")
            wrbytes(s, dst, self.tail)
            clobber_scratch(s)
            s.regs.x0 = dst
            return
        elif kind == "finish_grow":
            dest = self.workspace(s, x[0], 24)
            old = integer(s, x[2])
            oldcap = integer(s, x[1])
            newcap = integer(s, x[3])
            require(
                0 < newcap <= 4 * self.block and oldcap < newcap, "valid growth request"
            )
            if oldcap:
                require(
                    str(old) in alloc and alloc.pop(str(old))[0] == oldcap,
                    "resize owned allocation",
                )
            else:
                require(old == 1, "empty sentinel")
            addr = HEAP + s.globals["serial"] * STRIDE
            s.globals["serial"] += 1
            if oldcap:
                wrbytes(s, addr, load(s, old, oldcap))
            alloc[str(addr)] = (newcap, 1, "padding")
            s.globals["allocations"] = alloc
            put(s, dest, 0, 8)
            put(s, dest + 8, addr, 8)
        elif kind == "free":
            self.release(s, integer(s, x[0]), x[1], integer(s, x[2]))
        else:
            raise ValueError("unexpected SHA-from callee " + kind)
        clobber_scratch(s)

    def finish(self, s):
        require(
            s.globals["calls"] == ("compress", "compress")
            and not s.globals["allocations"],
            "SHA calls or ownership",
        )
        digest = c.Concat(
            *(
                self.final.get_bytes(i, self.word).reversed
                for i in range(0, self.digestlen, self.word)
            )
        )
        equal(s, load(s, RESULT, self.digestlen), digest, "big-endian SHA digest")
        self.check_abi(s)


def make_project(path, image, bits, driver):
    def function(suffix, family):
        return image.function(suffix, family)

    pc, words = function(f"6sha{bits}11sha{bits}_from".encode(), b"6slhdsa")
    native = [(pc, pc + len(words) * 4)]
    grow, gwords = function(b"6RawVechE8grow_oneB7_", b"5alloc7raw_vec")
    reserve, rwords = function(b"6slhdsa", b"7reserve21do_reserve_and_handle")
    hooks = {
        memcpy_address(image, path): "copy",
        function(b"___rust_dealloc", b"___rustc")[0]: "free",
    }
    for a, ww in [(grow, gwords), (reserve, rwords)]:
        native.append((a, a + len(ww) * 4))
        targets = {
            a + 4 * (i + ((w & 0x03FFFFFF) ^ 0x02000000) - 0x02000000)
            for i, w in enumerate(ww)
            if w & 0xFC000000 == 0x94000000
        }
        callee = [
            p
            for p in targets
            if any(q == p and b"finish_grow" in name for name, q in image.symbols)
        ]
        require(len(callee) == 1, "unique allocation backend")
        hooks[callee[0]] = "finish_grow"
    # Same unique hardware body selected in apple-binary/sha2.py's byte-to-Lean code binding.
    suffix = f"4sha26sha{bits}11compress{bits}".encode()
    matched = []
    for name, a in image.symbols:
        if name.endswith(suffix):
            _, ww = function(name, suffix)
            if ww[0] & 0xFFC003E0 == 0xAD400000 and any(
                op.startswith(f"sha{bits}h.")
                for op, arg in instructions(path, a, ww).values()
            ):
                matched.append(a)
    require(len(matched) == 1, "unique linked hardware compressor")
    hooks[matched[0]] = "compress"
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    for addr, label in hooks.items():
        project.hook(addr, Contract(driver=driver, label=label))
    return project, pc, native, hooks


def check_case(project, pc, native, hooks, d, r):
    s = project.factory.blank_state(
        addr=pc,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    d.start_case(s, r)

    def guard(st, kind):
        if not st.globals.get("in_driver"):
            return
        addr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        length = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        if kind == "read" and KEY <= addr and addr + length <= KEY + d.digestlen:
            return
        if kind == "write" and RESULT <= addr and addr + length <= RESULT + d.digestlen:
            return
        for key, (cap, _, _) in st.globals["allocations"].items():
            if int(key) <= addr and addr + length <= int(key) + cap:
                return
        # Runtime uses only the native stack and linked constants elsewhere.
        require(
            STACK - 2048 <= addr
            and addr + length <= STACK
            or kind == "read"
            and d.constants_range[0] <= addr
            and addr + length <= sum(d.constants_range),
            "native SHA padding memory access",
        )

    for kind in ("read", "write"):
        s.inspect.b(
            "mem_" + kind, when=angr.BP_BEFORE, action=lambda st, k=kind: guard(st, k)
        )
    todo = [s]
    returns = 0
    while todo:
        s = todo.pop()
        s.globals["in_driver"] = False
        if s.addr == RETURN:
            d.finish(s)
            returns += 1
            continue
        s.globals["in_driver"] = any(a <= s.addr < b for a, b in native)
        require(
            s.globals["in_driver"] or s.addr in hooks,
            f"SHA padding unknown exit {s.addr:#x}",
        )
        visits = s.globals.get("visits", 0) + 1
        require(visits < 4000, "padding did not terminate")
        s.globals["visits"] = visits
        succ = project.factory.successors(s)
        require(
            not succ.unconstrained_successors and succ.flat_successors,
            "unexpected termination",
        )
        todo.extend(succ.flat_successors)
    require(returns == 1, "missing or duplicate successful padding path")


def check_group(task):
    path, bits, residues = task
    image = Image(path.read_bytes())
    d = Padding(path, image, bits)
    proj, pc, ranges, hooks = make_project(path, image, bits, d)
    for r in residues:
        check_case(proj, pc, ranges, hooks, d, r)


def mutation(image, bits):
    pc, words = image.function(f"6sha{bits}11sha{bits}_from".encode(), b"6slhdsa")
    idx = [i for i, w in enumerate(words) if w & 0xFFFFFFE0 == 0x52801000]
    require(len(idx) == 1, "unique padding delimiter")
    data = bytearray(image.data)
    struct.pack_into("<I", data, pc - image.base + 4 * idx[0], words[idx[0]] ^ 32)
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "wrong-delimiter"
        path.write_bytes(data)
        try:
            check_group((path, bits, [bits // 4 - 1]))
        except ValueError as err:
            require(
                "complete FIPS padding and bit length" in str(err),
                f"unexpected mutation result: {err}",
            )
        else:
            raise AssertionError("accepted changed delimiter")
    print(f"Rejected changed SHA-{bits} padding byte", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("--bits", type=int, choices=(256, 512))
    parser.add_argument("--residue", type=int)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    image = Image(args.binary.read_bytes())
    require(args.jobs >= 1, "jobs must be positive")
    for bits in [args.bits] if args.bits else (256, 512):
        verify_compressor(image, args.binary, bits)
        residues = (
            [args.residue] if args.residue is not None else list(range(bits // 4))
        )
        require(all(0 <= r < bits // 4 for r in residues), "invalid residue")
        jobs = min(len(residues), args.jobs)
        tasks = [(args.binary, bits, residues[i::jobs]) for i in range(jobs)]
        if jobs == 1:
            check_group(tasks[0])
        else:
            with ProcessPoolExecutor(jobs) as pool:
                list(pool.map(check_group, tasks))
        print(
            f"SHA-{bits} streaming/padding: {len(residues)} residue classes, arbitrary complete-block count",
            flush=True,
        )
        if args.self_test:
            mutation(image, bits)
    print("Mach-O SHA-256", hashlib.sha256(image.data).hexdigest())
