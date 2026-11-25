# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the inlined 16-byte SHA-2 seed compression and register/memory frame in parallel Arm keygen."""

import argparse
import hashlib
import struct
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from driver import Image, angr, c, equal, integer, require
from current_keygen import page, sha256_seed
from sha256_seed import SeedCompression

PC = 0x1000CC908
STACK_BACKING = 0x70000000


def locate(image):
    (pc, words), _ = sha256_seed(image, b"Kj10_EB4_")
    require(pc == PC and len(words) == 43, "parallel keygen seed block moved")
    iv = page(pc + 16, words[4]) + 16 * ((words[5] >> 10) & 4095)
    k = page(pc + 36, words[9]) + ((words[10] >> 10) & 4095)
    return words, iv, k


def check(image):
    words, iv, k = locate(image)
    seed = c.BVS("pk_seed_bytes", 128)
    ref = SeedCompression(seed)
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    ref.install(project, PC, words)
    state = project.factory.blank_state(
        addr=PC,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    # Quantify over every input/dead-register value and the stack location. Map
    # each proved SP-relative access into a disjoint concrete backing range.
    regs = [c.BVS(f"input_x{r}", 64) for r in range(31)]
    vecs = [c.BVS(f"input_q{r}", 128) for r in range(32)]
    stack = c.BVS("input_stack", 64)
    regs[9] = c.BVV(0, 64)
    vecs[0] = seed.reversed
    for r, v in enumerate(regs):
        setattr(state.regs, f"x{r}", v)
    for r, v in enumerate(vecs):
        setattr(state.regs, f"q{r}", v)
    state.regs.sp = stack
    written = set()
    literal_bytes = set()

    def access(s, kind):
        key = f"mem_{kind}_address"
        address = getattr(s.inspect, key)
        size = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
        if not address.symbolic:
            addr = integer(s, address)
            require(
                kind == "read"
                and any(
                    lo <= addr and addr + size <= hi
                    for lo, hi in [(iv, iv + 32), (k, k + 256)]
                ),
                "unexpected literal or non-stack memory write",
            )
            literal_bytes.update(range(addr, addr + size))
            return
        offset = c.simplify(address - stack)
        require(not offset.symbolic, "memory address is not SP plus a constant")
        start = integer(s, offset)
        require(start + size <= 64, "memory outside 64-byte stack ring")
        cells = set(range(start, start + size))
        if kind == "read":
            require(cells <= written, "read of uninitialized stack")
        else:
            written.update(cells)
        setattr(s.inspect, key, c.BVV(STACK_BACKING + start, 64))

    for kind in ("read", "write"):
        state.inspect.b(
            f"mem_{kind}",
            when=angr.BP_BEFORE,
            action=lambda s, kind=kind: access(s, kind),
        )
    end = PC + 4 * len(words)
    for _ in range(700):
        if state.addr == end:
            break
        require(PC <= state.addr < end, "branch leaves seed program")
        nxt = project.factory.successors(state, num_inst=1)
        require(
            len(nxt.flat_successors) == 1 and not nxt.unconstrained_successors,
            "seed has non-unique path",
        )
        state = nxt.flat_successors[0]
    require(state.addr == end, "compression did not finish")
    require(
        all(c.is_true(c.simplify(clause)) for clause in state.solver.constraints),
        "execution constrained symbolic inputs",
    )
    equal(
        state, state.regs.q1, ref.seed.get_bytes(64, 16).reversed, "first digest half"
    )
    equal(
        state, state.regs.q0, ref.seed.get_bytes(80, 16).reversed, "second digest half"
    )
    equal(state, state.regs.x28, (regs[8][31:0] - 1).zero_extend(32), "W28 result")
    equal(state, state.regs.sp, stack, "SP preserved")
    for r in set(range(31)) - set(range(9, 18)) - {28}:
        equal(state, getattr(state.regs, f"x{r}"), regs[r], f"preserved X{r}")
    for r in range(6, 32):
        equal(state, getattr(state.regs, f"q{r}"), vecs[r], f"preserved Q{r}")
    require(written == set(range(64)), "incomplete scratch ring")
    require(
        literal_bytes == set(range(iv, iv + 32)) | set(range(k, k + 256)),
        "unexpected literal footprint",
    )
    for i, w in enumerate(ref.final_ring):
        final = state.memory.load(
            STACK_BACKING + 16 * i, 16, endness="Iend_LE", inspect=False
        )
        equal(state, final, w, f"schedule ring row {i}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    args = parser.parse_args()
    image = Image(args.binary.read_bytes())
    check(image)
    _, iv, k = locate(image)
    for label, section, addr, mask, expected in [
        ("wrong round", b"__text", PC + 15 * 4, 0x1000, "digest half"),
        ("wrong d subtraction", b"__text", PC + 38 * 4, 0x400, "W28 result"),
        ("stack displacement", b"__text", PC + 3 * 4, 0x8000, "outside 64-byte"),
        ("wrong IV", b"__const", iv, 1, "digest half"),
        ("wrong K", b"__const", k + 63 * 4, 1, "digest half"),
    ]:
        bad = bytearray(image.data)
        base, _, offset = image.sections[section]
        pos = offset + addr - base
        struct.pack_into("<I", bad, pos, struct.unpack_from("<I", bad, pos)[0] ^ mask)
        try:
            check(Image(bad))
        except ValueError as err:
            require(expected in str(err), f"{label}: unexpected rejection: {err}")
        else:
            raise ValueError(f"{label} was accepted")
    print(
        f"Verified symbolic parallel SHA2-128 seed digest, W28, preserved state and memory frame; five negative controls; Mach-O sha256 {hashlib.sha256(image.data).hexdigest()}."
    )


if __name__ == "__main__":
    main()
