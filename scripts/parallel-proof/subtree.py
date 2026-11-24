# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check every permutation input and parent input of the compiled eight-leaf routine."""

import argparse
import logging
import tempfile
from pathlib import Path

logging.getLogger("angr.state_plugins.unicorn_engine").setLevel(logging.CRITICAL)
import angr
import claripy as bv
from build import build


def zeros(n):
    return bv.BVV(0, 8 * n)


def byte_range(x, start, size):
    return x.get_bytes(start, size)


def word_row(msgs, word):
    return bv.Concat(*(byte_range(m, word * 8, 8) for m in msgs))


def inputs(n, height, secret, seed, index, layer, tree):
    """FIPS byte strings, with the permutation result fresh at every invocation."""

    def address(typ, first, second, third):
        def u32(v):
            return bv.BVV(v, 32) if isinstance(v, int) else v

        return bv.Concat(
            layer, zeros(4), tree, *(u32(x) for x in (typ, first, second, third))
        )

    def rows(msgs):
        return [word_row(msgs, i) for i in range(25)]

    def block(msg):
        used = msg.size() // 8
        return bv.Concat(
            msg, bv.BVV(31, 8), zeros(134 - used), bv.BVV(128, 8), zeros(64)
        )

    def fresh():
        return [bv.BVS("permuted", 512) for _ in range(25)]

    def digests(output):
        return [
            bv.Concat(*(byte_range(r, lane * 8, 8) for r in output[: n // 8]))
            for lane in range(8)
        ]

    key_count = 1 << height
    keys = [index * key_count + i for i in range(key_count)]
    pending = [bv.Concat(seed, address(1, k, 0, 0)) for k in keys]
    sponge = [zeros(key_count * 8)] * 25

    def absorb(blocks):
        return [old ^ new for old, new in zip(sponge, rows(blocks))]

    chains = 2 * n + 3
    chains_per_batch = 8 // key_count
    for first in range(0, chains, chains_per_batch):
        lanes = [
            (chain, k)
            for chain in range(first, min(first + chains_per_batch, chains))
            for k in keys
        ]
        active = len(lanes)
        state = fresh()
        messages = [
            block(bv.Concat(seed, address(5, k, chain, 0), secret))
            for chain, k in lanes
        ]
        yield "active", (active, rows(messages)), state
        for step in range(15):
            messages = [
                block(bv.Concat(seed, address(0, k, chain, step), digest))
                for (chain, k), digest in zip(lanes, digests(state))
            ]
            state = fresh()
            yield "active", (active, rows(messages)), state
        endpoints = digests(state)
        for group in range(0, active, key_count):
            pending = [
                bv.Concat(m, d) if m is not None else d
                for m, d in zip(pending, endpoints[group : group + key_count])
            ]
            size = pending[0].size() // 8
            if size >= 136:
                blocks = [bv.Concat(byte_range(m, 0, 136), zeros(64)) for m in pending]
                updated = fresh()
                yield "active", (key_count, absorb(blocks)), updated
                sponge = [byte_range(r, 0, key_count * 8) for r in updated]
                pending = [
                    byte_range(m, 136, size - 136) if size > 136 else None
                    for m in pending
                ]
    final = fresh()
    yield "active", (key_count, absorb([block(m) for m in pending])), final
    nodes = digests(final)[:key_count]
    for h in range(1, height):
        count = key_count >> h
        blocks = [
            block(
                bv.Concat(
                    seed,
                    address(2, 0, h, index * count + j),
                    nodes[2 * j],
                    nodes[2 * j + 1],
                )
            )
            for j in range(count)
        ]
        updated = fresh()
        yield "active", (count, rows(blocks)), updated
        nodes = digests(updated)[:count]
    value = bv.BVS("root", 8 * n)
    yield "parent", (seed, address(2, 0, height, index), *nodes), value
    nodes = [value]
    yield "return", (), nodes[0]


class Copy(angr.SimProcedure):
    def run(self, dst, src, length):
        if any(v.symbolic for v in (dst, src, length)):
            raise ValueError("symbolic copy range")
        n = length.concrete_value
        words = [
            (i, self.state.memory.load(src.concrete_value + i, min(32, n - i)))
            for i in range(0, n, 32)
        ]
        for i, word in words:
            self.state.memory.store(dst.concrete_value + i, word)
        return dst


def check(image, n, height):
    project = angr.Project(str(image), auto_load_libs=False)
    addr = lambda name: project.loader.find_symbol(name).rebased_addr
    for name in ("memset", "memcpy", "memmove"):
        if project.loader.find_symbol(name) is not None:
            project.hook_symbol(
                name,
                (angr.SIM_PROCEDURES["libc"][name]() if name == "memset" else Copy()),
                replace=True,
            )
    out, sk, pk, stop = 0x710000, 0x720000, 0x730000, 0x750000
    secret, seed = (bv.BVS(k, n * 8) for k in ("secret", "seed"))
    # Every index for which all leaf indices fit u32.
    idx = bv.ZeroExt(height, bv.BVS("index", 32 - height))
    layer, tree = bv.BVS("layer", 32), bv.BVS("tree", 64)
    st = project.factory.call_state(
        addr(f"proof{n}_{height}"),
        out,
        sk,
        pk,
        idx,
        layer,
        tree,
        0x740000,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
        ret_addr=stop,
        prototype="void f(void*,void*,void*,unsigned,unsigned,unsigned long long,void*)",
    )
    st.memory.store(sk, secret)
    st.memory.store(pk, seed)
    st.memory.store(0x740000, bv.BVS("address_tail", 128))

    def fixed_address(state, kind):
        addr_expr = getattr(state.inspect, kind + "_address")
        if getattr(addr_expr, "symbolic", False):
            raise ValueError("symbolic memory address")

    for event in ("mem_read", "mem_write"):
        st.inspect.b(
            event, when=angr.BP_BEFORE, action=lambda s, k=event: fixed_address(s, k)
        )

    stream = iter(inputs(n, height, secret, seed, idx, layer, tree))
    permitted = {addr("proof_permute"), addr("proof_parent"), stop}
    count = 0

    def concrete(v):
        if v.symbolic:
            raise ValueError("symbolic pointer")
        return v.concrete_value

    def same(x, y):
        if x is not y and st.solver.satisfiable(extra_constraints=[x != y]):
            raise ValueError(
                f"SHAKE-{n * 8} mismatch at call {count}: {str(x)[:900]} vs {str(y)[:900]}"
            )

    while True:
        if st.addr in permitted:
            kind, args, result = next(stream)
            if st.addr == stop:
                if kind != "return" or next(stream, None) is not None:
                    raise ValueError("early return")
                same(st.memory.load(out, n), result)
                print(
                    f"{n} bytes, height {height}: checked {count} calls and root",
                    flush=True,
                )
                return
            if st.addr == addr("proof_permute"):
                if kind not in ("permute", "active"):
                    raise ValueError("unexpected permutation")
                active, args = args if kind == "active" else (8, args)
                same(st.regs.rsi, bv.BVV(active, 64))
                ptr = concrete(st.regs.rdi)
                for j, row in enumerate(args):
                    same(st.memory.load(ptr + 64 * j, active * 8), row)
                    st.memory.store(ptr + 64 * j, result[j])
            else:
                if kind != "parent":
                    raise ValueError("unexpected parent")
                for ptr, expected in zip(
                    (st.regs.rsi, st.regs.rdx, st.regs.rcx, st.regs.r8), args
                ):
                    same(st.memory.load(concrete(ptr), expected.size() // 8), expected)
                st.memory.store(concrete(st.regs.rdi), result)
            count += 1
            # The compiled caller can rely only on SysV callee-saved registers.
            for reg in ("rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"):
                setattr(st.regs, reg, bv.BVS(reg, 64))
            for i in range(16):
                setattr(st.regs, f"xmm{i}", bv.BVS("scratch", 128))
            st.regs.cc_op = 0
            st.regs.cc_dep1 = bv.BVS("flags", 64)
            st.regs.cc_dep2 = st.regs.cc_ndep = 0
            sp = concrete(st.regs.rsp)
            st.regs.rip = st.memory.load(sp, 8, endness="Iend_LE")
            st.regs.rsp = sp + 8
        else:
            if project.is_hooked(st.addr) and project.hooked_by(
                st.addr
            ).display_name not in ("Copy", "memset"):
                raise ValueError(f"unexpected call {project.hooked_by(st.addr)}")
            succ = project.factory.successors(st)
            if succ.unconstrained_successors or len(succ.flat_successors) != 1:
                raise ValueError("nonunique symbolic control flow")
            st = succ.flat_successors[0]
            # No path restrictions may silently narrow the input theorem.
            if any(cond.symbolic for cond in st.solver.constraints):
                raise ValueError("symbolic branch or address concretization")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--width", nargs="+", type=int, choices=(16, 24, 32), default=(16, 24, 32)
    )
    options = parser.parse_args()
    with tempfile.TemporaryDirectory() as tmp:
        binary = build(Path(tmp))
        for width in options.width:
            for height in (1, 2, 3):
                check(binary, width, height)
