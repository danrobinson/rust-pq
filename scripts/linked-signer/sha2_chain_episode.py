# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Symbolic round-window and compaction certificates for the Apple SHA-256 scheduler."""

import argparse
from pathlib import Path
import sys

sys.dont_write_bytecode = True
from driver import (
    Image,
    STACK,
    KEY,
    angr,
    c,
    blob,
    put,
    wrbytes,
    load,
    integer,
    require,
    unsigned,
)
from signer_inventory import import_stubs
from wots_chains import ImageEnv, agrees, return_call
from segmented import Compression
from sha2_chain import BLOCKS, START, END
from sha256_seed import vector, add4
import arm_vector_ir

# Dispatch before testing the number of lanes, post-compaction before refilling.
from sha2_chain_context import (
    CUTS,
    ENTRY,
    persistent,
    set_context,
    activate,
    check_context,
)


def by_word(value):
    return c.Concat(*(w.reversed for w in value.chop(32)))


def pack(hash, h, block, n, lane, now, end):
    fixed = c.Concat(
        block.get_bytes(0, 18), c.BVV(0, 8 * (4 + n)), block.get_bytes(22 + n, 42 - n)
    )
    # Array layout from the linked Slot stores and the independently defined
    # split into fixed message words, variable chaining value and cached SHA rounds.
    val = block.get_bytes(22, n)
    xb = (
        by_word(c.Concat(val.get_bytes(16, n - 16), c.BVV(0, 64)))
        if n == 24
        else (by_word(val.get_bytes(16, 16)) if n == 32 else c.BVV(0, 128))
    )
    tail = (
        by_word(c.Concat(c.BVV(0, 64), block.get_bytes(46, 8)))
        if n == 24
        else c.BVV(0, 128)
    )
    ab, ef = vector(h[:4]), vector(h[4:])
    wk = add4(vector(block.get_bytes(0, 16).chop(32)), vector(hash.k[:4]))
    a1, e1 = hash.op("H", ab, ef, wk), hash.op("H2", ef, ab, wk)
    return c.Concat(
        by_word(fixed),
        by_word(val.get_bytes(0, 16)),
        xb,
        tail,
        a1.reversed,
        e1.reversed,
        lane.reversed,
        now.reversed,
        end.reversed,
    )


def verify(path, image, n, num, rounds):
    env = ImageEnv(path, image, n)
    pc, words = image.function(
        b"4hash12chain_blocks" + f"Kj{n:x}_EB4_".encode(), b"6slhdsa"
    )
    dispatch, refill = [pc + o for o in CUTS[n]]
    (zero,) = [a for a, name in import_stubs(image, path).items() if name == "_bzero"]
    s = env.blank(pc)
    for i, v in enumerate([KEY, BLOCKS, num, START, num, END, num]):
        setattr(s.regs, f"x{i}", v)
    hash = Compression(16, None)
    h = [c.BVS("initial_word", 32) for _ in range(8)]
    for i, v in enumerate(h):
        put(s, KEY + 4 * i, v, 4)
    h0 = blob("shared_first_16_bytes", 16)
    starts = [c.BVS("start", 4).zero_extend(28) for _ in range(num)]
    residual = [c.BVS("remaining_after_batch", 4).zero_extend(28) for _ in range(num)]
    # For a fifteen-round minimum every four-bit interval must be [0,15).
    # Prove the reduction locally before using constants to hash the long chain.
    if rounds == 15:
        for t, left in zip(starts, residual):
            q = c.Solver()
            q.add(c.ULE(t + rounds + left, 15))
            require(
                not q.satisfiable(extra_constraints=[c.Or(t != 0, left != 0)]),
                "full interval reduction",
            )
        starts = [c.BVV(0, 32) for _ in starts]
        residual = [c.BVV(0, 32) for _ in residual]
    s.add_constraints(c.Or(*(r == 0 for r in residual)))
    blocks, results, completed = [], [], []
    for i, (a, r) in enumerate(zip(starts, residual)):
        finish = a + rounds + r
        s.add_constraints(c.ULE(finish, 15))
        put(s, START + 4 * i, a, 4)
        put(s, END + 4 * i, finish, 4)
        b = c.Concat(
            h0,
            blob("address_suffix", 2),
            blob("old_round", 4),
            blob("value", n),
            blob("tail", 42 - n),
        )
        wrbytes(s, BLOCKS + 64 * i, b)
        blocks.append(b)
        for j in range(rounds):
            msg = c.Concat(b.get_bytes(0, 18), a + j, b.get_bytes(22, 42))
            result = c.Concat(*hash.block(h, msg)).get_bytes(0, n)
            b = c.Concat(msg.get_bytes(0, 22), result, msg.get_bytes(22 + n, 42 - n))
        completed.append(b)
        results.append(result)
    hash.hooks(env.project, path, pc, words)
    # Canonicalize an inferred minimum run length after any CSEL Wd,Wa,Wb,LO.
    # A replacement is made only when SMT proves that the actual result equals rounds.
    sync = {
        pc + 4 * (i + 1): w & 31
        for i, w in enumerate(words)
        if (w & 0xFFE0FC00) == 0x1A803000
    }
    entry = pc + ENTRY[n]
    stops = {entry, dispatch, refill, *sync}
    stored = None
    cold = None
    lanes = [c.BVS("id", 64) for _ in range(num)]
    next_id, total = c.BVS("scanned", 64), c.BVS("array_length", 64)

    def guarded(st, kind):
        if not st.globals.get("native", False):
            return
        expression = getattr(st.inspect, f"mem_{kind}_address")
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        sp = integer(st, st.regs.sp)
        if not isinstance(expression, int) and expression.symbolic:
            require(kind == "write", "unexpected indexed read during batch")
            for i, lane in enumerate(lanes):
                for off in [18, 19, 20, 21, 22, 38]:
                    if not st.solver.satisfiable(
                        extra_constraints=[expression != BLOCKS + 64 * lane + off]
                    ):
                        require(
                            18 <= off
                            and off + size <= 22 + max(n, 32 if n == 24 else n),
                            "indexed write extent",
                        )
                        st.inspect.mem_write_address = BLOCKS + 64 * i + off
                        return
            raise ValueError("unmatched symbolic block write")
        ptr = integer(st, expression)
        allowed = [(sp, STACK - 0x90 - sp)]
        if kind == "read":
            allowed.extend([env.const, (KEY, 32)])
        require(
            any(a <= ptr and ptr + size <= a + l for a, l in allowed),
            f"episode {kind} extent {ptr:#x}",
        )

    steps_max = 0
    todo = [(s, None, 0)]
    leaves = 0
    while todo:
        st, initial, steps = todo.pop()
        st.globals["native"] = False
        require(steps < 16000, "unbounded SHA chain episode")
        if st.addr == zero:
            ptr, size = integer(st, st.regs.x0), integer(st, st.regs.x1)
            require(
                integer(st, st.regs.sp) <= ptr <= STACK - size and size == 640,
                "zero slot buffer",
            )
            wrbytes(st, ptr, c.BVV(0, 8 * size))
            return_call(st)
            todo.append((st, initial, steps + 1))
            continue
        if st.addr == entry and cold is None:
            cold = persistent(st, n)
        if st.addr == dispatch:
            require(initial is None, "second dispatch without compaction")
            base = integer(st, st.regs.x24)
            new = env.blank(dispatch)
            new.add_constraints(*st.solver.constraints)
            new.add_constraints(
                c.ULE(next_id, total), c.ULE(total, 67), c.ULT(lanes[-1], next_id)
            )
            for i in range(num - 1):
                new.add_constraints(c.ULT(lanes[i], lanes[i + 1]))
            new.regs.sp = st.regs.sp
            scalar, vec, stack = persistent(st, n)
            set_context(new, scalar, vec, stack)
            new.regs.x8 = next_id
            new.regs.x19 = total
            new.regs.x13 = num
            for i, word in enumerate(h):
                put(new, KEY + 4 * i, word, 4)
            initial = []
            for i in range(num):

                def slot(lane):
                    return pack(
                        hash,
                        h,
                        blocks[i],
                        n,
                        lane,
                        starts[i],
                        starts[i] + rounds + residual[i],
                    )

                agrees(
                    st,
                    load(st, base + 160 * i, 160),
                    slot(c.BVV(i, 64)),
                    "incoming packed slot",
                )
                wrbytes(new, base + 160 * i, slot(lanes[i]))
                wrbytes(new, BLOCKS + 64 * i, blocks[i])
                initial.append(slot(lanes[i]))
            # Use the same cold-to-cached formula that the separate refill proof checks.
            active = activate(
                cold,
                n,
                h0,
                initial[0].get_bytes(112, 16).reversed,
                initial[0].get_bytes(128, 16).reversed,
            )
            active = (
                [(j, c.BVV(num, 64) if j == 8 else v) for j, v in active[0]],
                active[1],
                active[2],
            )
            check_context(st, persistent(st, n), active, "canonical live-in context")
            stored = persistent(new, n)
            frame_sp = integer(new, new.regs.sp)
            for kind in ("read", "write"):
                new.inspect.b(
                    f"mem_{kind}",
                    when=angr.BP_BEFORE,
                    action=lambda st, k=kind: guarded(st, k),
                )
            st = new
        if st.addr in sync:
            reg = f"w{sync[st.addr]}"
            value = getattr(st.regs, reg)
            if not st.solver.satisfiable(extra_constraints=[value != rounds]):
                setattr(st.regs, reg, rounds)
        if st.addr == refill and initial is not None:
            agrees(st, st.regs.sp, frame_sp, "unchanged scheduler stack")
            alive = [
                i
                for i in range(num)
                if st.solver.satisfiable(extra_constraints=[residual[i] != 0])
            ]
            require(len(alive) < num, "scheduler did not retire a lane")
            agrees(st, st.regs.x14, len(alive), "number of surviving chains")
            base = integer(st, st.regs.x24)
            for i in range(num):
                running = i in alive
                agrees(
                    st, residual[i] != 0, running, "compacted exactly unfinished lanes"
                )
                agrees(
                    st,
                    load(st, BLOCKS + 64 * i, 64),
                    blocks[i] if running else completed[i],
                    "SHA chain writeback",
                )
                if running:
                    raw = initial[i]
                    target = base + 160 * alive.index(i)
                    expected = c.Concat(
                        raw.get_bytes(0, 64),
                        by_word(results[i]),
                        raw.get_bytes(64 + n, 88 - n),
                        (starts[i] + rounds).reversed,
                        raw.get_bytes(156, 4),
                    )
                    agrees(
                        st, load(st, target, 160), expected, "packed survivor record"
                    )
            check_context(st, persistent(st, n), stored, "preserve scheduler context")
            steps_max = max(steps, steps_max)
            leaves += 1
            continue
        require(
            pc <= st.addr < pc + 4 * len(words), f"unexpected episode exit {st.addr:#x}"
        )
        st.globals["native"] = initial is not None
        nx = env.project.factory.successors(st, extra_stop_points=stops)
        require(
            nx.flat_successors and not nx.unconstrained_successors,
            f"unresolved episode exit {st.addr:#x}",
        )
        todo.extend((nxst, initial, steps + 1) for nxst in nx.flat_successors)
    require(
        leaves == (1 if rounds == 15 else 2**num - 1),
        "missing feasible retirement subset",
    )
    print(n, num, rounds, leaves, steps_max, flush=True)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("binary", type=Path)
    p.add_argument("--width", type=int, default=16)
    p.add_argument("--slots", type=int, default=2)
    p.add_argument("--rounds", type=int)
    a = p.parse_args()
    for r in [a.rounds] if a.rounds else range(1, 16):
        verify(a.binary, Image(a.binary.read_bytes()), a.width, a.slots, r)
