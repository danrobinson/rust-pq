# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["unicorn==2.1.4", "pyelftools==0.32"]
# ///
"""Compare all observed effects of the compiled original and row-snapshot FORS trees."""

from hashlib import shake_256
from pathlib import Path
import os
import struct
import tempfile

from elftools.elf.elffile import ELFFile
from unicorn import (
    Uc,
    UC_ARCH_X86,
    UC_MODE_64,
    UC_HOOK_CODE,
    UC_PROT_EXEC,
    UC_PROT_READ,
    UC_PROT_WRITE,
)
from unicorn import x86_const as x86
from buffered_lift import lift_rows
from build import SRC, function
from fors_buffered_image import image

ARGS = [
    getattr(x86, "UC_X86_REG_" + n) for n in ("RDI", "RSI", "RDX", "RCX", "R8", "R9")
]
PAGE, BASE, STACK, INPUT, OUTPUT, IMPORTS = (
    4096,
    0x400000,
    0x600000,
    0x710000,
    0x720000,
    0x730000,
)
STACK_LEN = 0x40000
RET = IMPORTS + PAGE - 8


class Machine:
    def __init__(self, path):
        self.uc = Uc(UC_ARCH_X86, UC_MODE_64)
        self.symbols, self.imports = {}, {}
        with path.open("rb") as file:
            elf = ELFFile(file)
            if elf["e_machine"] != "EM_X86_64":
                raise ValueError("expected an x86-64 shared image")
            segments = [s for s in elf.iter_segments() if s["p_type"] == "PT_LOAD"]
            last = max(s["p_vaddr"] + s["p_memsz"] for s in segments)
            self.uc.mem_map(BASE, (last + PAGE - 1) // PAGE * PAGE)
            for s in segments:
                self.uc.mem_write(BASE + s["p_vaddr"], s.data())
            self.symbols = {
                s.name: BASE + s["st_value"]
                for s in elf.get_section_by_name(".dynsym").iter_symbols()
                if s["st_shndx"] != "SHN_UNDEF"
            }
            self.uc.mem_map(IMPORTS, PAGE)
            for sec in elf.iter_sections():
                if sec["sh_type"] != "SHT_RELA":
                    continue
                syms = elf.get_section(sec["sh_link"])
                for reloc in sec.iter_relocations():
                    kind, addend = reloc["r_info_type"], reloc["r_addend"]
                    if kind == 8:  # R_X86_64_RELATIVE
                        ptr = BASE + addend
                    elif kind in (6, 7):  # GLOB_DAT / JUMP_SLOT
                        sym = syms.get_symbol(reloc["r_info_sym"])
                        if sym["st_shndx"] != "SHN_UNDEF":
                            ptr = BASE + sym["st_value"] + addend
                        else:
                            ptr = self.imports.setdefault(
                                sym.name, IMPORTS + 8 * len(self.imports)
                            )
                            self.uc.mem_write(ptr, b"\xc3")
                    else:
                        raise ValueError(f"unexpected x86 relocation {kind}")
                    self.uc.mem_write(BASE + reloc["r_offset"], struct.pack("<Q", ptr))
            self.uc.mem_protect(
                BASE, (last + PAGE - 1) // PAGE * PAGE, UC_PROT_READ | UC_PROT_EXEC
            )
        self.names = {ptr: name for name, ptr in self.imports.items()}
        self.uc.mem_protect(IMPORTS, PAGE, UC_PROT_READ | UC_PROT_EXEC)
        self.uc.mem_map(STACK, STACK_LEN, UC_PROT_READ | UC_PROT_WRITE)
        self.uc.mem_map(INPUT, PAGE, UC_PROT_READ)
        self.uc.mem_map(OUTPUT, PAGE, UC_PROT_READ | UC_PROT_WRITE)
        self.uc.hook_add(UC_HOOK_CODE, self.call, begin=IMPORTS, end=IMPORTS + PAGE - 1)

    def args(self):
        return [self.uc.reg_read(r) for r in ARGS]

    def store(self, ptr, data):
        if not STACK <= ptr <= STACK + STACK_LEN - len(data):
            if not self.out <= ptr <= self.out + self.n - len(data):
                raise ValueError("observable write outside the stack or output")
        self.uc.mem_write(ptr, bytes(data))

    def call(self, cpu, address, size, _):
        name = self.names[address]
        out, a, b, c, d, e = self.args()
        if name in ("memcpy", "memmove", "memset"):
            data = bytes([a & 255]) * b if name == "memset" else cpu.mem_read(a, b)
            self.store(out, data)
            cpu.reg_write(x86.UC_X86_REG_RAX, out)
            return
        expected, fields, result = next(self.stream)
        if name != expected:
            raise ValueError(f"unexpected {name}, expected {expected}")
        for actual, value in zip((a, b, c, d, e)[: len(fields)], fields, strict=True):
            got = (
                actual
                if isinstance(value, int)
                else bytes(cpu.mem_read(actual, len(value)))
            )
            if got != value:
                raise ValueError(
                    f"{name} observable input differs at operation {self.count}"
                )
        self.store(out, result)
        self.count += 1

    def run(self, n, height, idx):
        self.n = n
        self.out = OUTPUT + PAGE - n
        self.count = 0
        source = shake_256(struct.pack("<III", n, height, idx)).digest(2 * n + 28)
        sk, seed, addr = source[:n], source[n : 2 * n], source[2 * n :]
        self.stream = iter(oracle(n, height, idx, sk, seed, addr))
        self.uc.mem_write(INPUT, source)
        guard = bytes([0xA5]) * (PAGE - n)
        self.uc.mem_write(OUTPUT, guard + bytes([0x6C]) * n)
        stack_top = STACK + STACK_LEN - 8
        self.uc.mem_write(stack_top, struct.pack("<Q", RET))
        self.uc.reg_write(x86.UC_X86_REG_RSP, stack_top)
        for r, v in zip(
            ARGS, (self.out, INPUT, INPUT + n, idx, height, INPUT + 2 * n), strict=True
        ):
            self.uc.reg_write(r, v)
        self.uc.emu_start(self.symbols[f"tree{n}"], RET, count=100000 * (1 << height))
        if self.uc.reg_read(x86.UC_X86_REG_RIP) != RET:
            raise ValueError("subtree did not return")
        op, _, value = next(self.stream)
        if op != "return" or next(self.stream, None) is not None:
            raise ValueError("missing primitive calls")
        if bytes(self.uc.mem_read(OUTPUT, PAGE)) != guard + value:
            raise ValueError("root or output frame differs")
        if bytes(self.uc.mem_read(INPUT, len(source))) != source:
            raise ValueError("shared input was modified")
        return self.count


def oracle(n, h, idx, sk, seed, words):
    layer, hi, lo, typ, pair, w2, w3 = struct.unpack("<7I", words)

    def address(t, x, y, z):
        return struct.pack(">8I", layer, 0, hi, lo, t, x, y, z)

    # Each requested node is keyed by its absolute location and height. Both probes
    # see the same opaque lane bytes; the oracle separately checks all call inputs.
    def node(level, i):
        return shake_256(
            sk + seed + struct.pack("<II", level, (idx << (h - level)) + i)
        ).digest(n)

    def parents(level, first, count):
        ids = range(first, first + count)
        addrs = b"".join(address(3, pair, level, (idx << (h - level)) + i) for i in ids)
        left = b"".join(node(level - 1, 2 * i) for i in ids)
        right = b"".join(node(level - 1, 2 * i + 1) for i in ids)
        values = b"".join(node(level, i) for i in ids)
        if count == 1:
            return "proof_parent", (seed, addrs, left, right), values
        inactive = shake_256(seed + values + b"inactive").digest((8 - count) * n)
        return "proof_pairs", (seed, addrs, left, right, count), values + inactive

    for b in range(1 << (h - 3)):
        first = 8 * b
        ids = struct.pack("<8I", *((idx << h) + first + j for j in range(8)))
        yield (
            "proof_fors_leaves",
            (sk, seed, address(typ, pair, w2, w3), ids, 8),
            b"".join(node(0, first + j) for j in range(8)),
        )
        level = 1
        while (b + 1) % (1 << level) == 0:
            yield parents(level, 8 * ((b + 1) // (1 << level) - 1), 8)
            level += 1
    for level in range(h - 2, h + 1):
        yield parents(level, 0, 1 << (h - level))
    yield "return", (), node(h, 0)


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    original = (SRC / "shake/fors_batch.rs").read_text()
    with tempfile.TemporaryDirectory() as d:
        folder = Path(d)
        for name, s in (
            ("original", original),
            ("row snapshots", lift_rows(original, "fors_subtree_horiz")),
        ):
            m = Machine(image(folder, s))
            ops = 0
            for n in (16, 24, 32):
                for h in range(3, 15):
                    for i in (0, 1, (1 << (20 - h)) - 1):
                        ops += m.run(n, h, i)
            print(
                f"{name}: 108 FORS subtrees, {ops} primitive calls and complete root/output frames matched",
                flush=True,
            )
        target = "left[k] = buf[h][2 * k];"
        for occurrence, h in [(0, 4), (1, 3)]:
            parts = function(original, "fors_subtree_horiz").split(target)
            if len(parts) != 3:
                raise ValueError("review the two FORS sibling reads")
            reads = [target, target]
            reads[occurrence] = target.replace("2 * k", "2 * k + 1")
            body = parts[0] + reads[0] + parts[1] + reads[1] + parts[2]
            m = Machine(image(folder, body))
            try:
                m.run(24, h, 7)
            except ValueError as error:
                if "observable input differs" not in str(error):
                    raise
            else:
                raise ValueError("accepted a duplicated FORS sibling")
        print(
            "Rejected a wrong child in both the full carry and the partial flush.",
            flush=True,
        )


if __name__ == "__main__":
    main()
