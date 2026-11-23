# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the linked Apple SHA-2 FORS subtree recurrence and public-key recovery.

The trace oracle specifies each PRF/F/H input, compressed address, padded
compression block, step counter, and result used by the next level. Batched
SHA-256 chains, the paired SHA-512 compression kernel, scalar thash_pair,
and the final hash on the roots are contract boundaries. The paired parents
and authentication-path builders themselves execute as linked instructions.

All eight base heights run for each width. The recursive step assumes the
specification only for the two children at strictly smaller height; arbitrary
32-bit indices satisfy (index << height) < 2^20 mathematically. This includes
every global FORS leaf index in the six published rows. Recovery uses arbitrary
digest and exact-length signature bytes, with symbolic left/right decisions at
every authentication level. The base_2b routine is separately checked by
sha2_fors_sign.py. The runtime contracts model successful allocation, clearing,
growth preserving initialized bytes, and release on the modeled ABI. The proof
does not address allocation failure, alternate artifacts or side channels.
"""

import argparse
import hashlib
import logging
import struct
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor
from pathlib import Path

logging.getLogger("angr.state_plugins.unicorn_engine").setLevel(logging.CRITICAL)
sys.dont_write_bytecode = True
from angr.concretization_strategies import SimConcretizationStrategySolutions
from angr.state_plugins.sim_action_object import SimActionObject
from driver import (
    HEAP,
    KEY,
    RESULT,
    RETURN,
    STACK,
    STRIDE,
    Driver,
    Image,
    angr,
    blob,
    c,
    clobber_scratch,
    integer,
    load,
    objects,
    put,
    require,
    unsigned,
    wrbytes,
)
from fors import agree, b32
from hypertree import instructions
from signer_inventory import import_stubs

SEED, ADRS, MD, SIG = KEY + 512, KEY + 1024, KEY + 1280, KEY + 2048


class Case:
    def __init__(self, path, image, n, v, mode, height=None):
        row, param, *_, self.hooks = objects(path, image, n, v, "sha2")
        self.model = m = Driver(row, param, "slh_sign_internal", "sha2")
        self.n = n
        self.a = m.a
        self.k = m.k
        self.mode = mode
        self.events = []
        self.allowed = []
        suf = f"Kj{n:x}_EB4_".encode()

        def func(fam, name, suffix=suf):
            return image.function(name + suffix, fam)

        def native(fam, name, suffix=suf):
            address, words = func(fam, name, suffix)
            self.allowed.append((address, address + 4 * len(words)))
            return address, words

        f = b"6slhdsa4fors"
        h = b"6slhdsa4hash"
        p = b"6slhdsa6sha512"
        self.node, _ = native(f, b"9fors_node")
        native(f, b"10fors_batch")
        recover, recoverwords = native(f, b"16fors_pk_from_sig")
        self.start = recover if mode == "recover" else self.node
        self.hooks = {
            a: name for a, name in self.hooks.items() if name in ("free", "reserve")
        }
        self.hooks.update(
            {
                func(h, b"12chain_blocks")[0]: "chain",
                func(h, b"10thash_pair")[0]: "pair",
                func(h, b"5thash")[0]: "roots",
                image.function(b"6slhdsa4util7base_2b", b"6slhdsa")[0]: "digits",
            }
        )
        self.hooks.update(
            {
                a: "zero"
                for a, name in import_stubs(image, path).items()
                if name == "_bzero"
            }
        )
        if n > 16:
            suf2 = f"Kj{n:x}_EB6_".encode()
            native(p, b"7parents7parents", suf2)
            native(p, b"7parents12path_parents", suf2)
            self.hooks[func(p, b"6paired16compress_parents", suf2)[0]] = "paired"
        self.project = angr.load_shellcode(
            bytes(image.data), arch="aarch64", load_address=image.base
        )
        s = self.project.factory.blank_state(
            addr=self.start,
            add_options={
                angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
                angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            },
        )
        self.s = s
        m.start(s)
        self.tree = blob("address_tree", 8)
        self.layer = b32(c.BVS("address_layer", 32))
        self.kp = blob("address_keypair", 4)
        self.sk = blob("secret_seed", n)
        wrbytes(s, KEY, self.sk)
        wrbytes(s, SEED, blob("seed_record", 96 + n))
        for off, sz, value in [
            (0, 8, self.tree),
            (8, 4, self.layer),
            (12, 4, 3),
            (16, 4, self.kp),
            (20, 4, 0),
            (24, 4, 0),
        ]:
            put(s, ADRS + off, value, sz)
        if mode == "recover":
            self.sig = [
                [blob("sig_block", n) for _ in range(m.a + 1)] for _ in range(m.k)
            ]
            for t, row in enumerate(self.sig):
                for j, val in enumerate(row):
                    for off in range(0, n, 8):
                        wrbytes(
                            s,
                            SIG + n * (t * (m.a + 1) + j) + off,
                            val.get_bytes(off, 8),
                        )
            wrbytes(s, MD, m.digest.get_bytes(0, m.md))
            args = (param, SIG, m.forslen, MD, m.md, SEED, ADRS)
            self.events.append(("digits",))
            ids = [(i << m.a) + m.idx.get_bytes(4 * i, 4).reversed for i in range(m.k)]
            vals = self.level(3, 0, ids, [ss[0] for ss in self.sig])
            for level in range(1, m.a + 1):
                pairs = []
                for i, (idx, x) in enumerate(zip(ids, vals)):
                    y = self.sig[i][level]
                    even = idx[0] == 0
                    pairs.append(c.Concat(c.If(even, x, y), c.If(even, y, x)))
                ids = [c.LShR(i, 1) for i in ids]
                vals = self.level(3, level, ids, pairs)
            self.output = blob("forest_pk", n)
            self.events.append(("roots", c.Concat(*vals), self.output))
            # One scalar remainder lane can take two short branch arms around
            # the same thash_pair for N=24/32. Rejoin only after validating both.
            if n > 16:
                decoded = instructions(path, recover, recoverwords)
                joins = [
                    int(decoded[j + 1][1].split()[0], 16)
                    for j, (op, arg) in decoded.items()
                    if op == "bl" and "thash_pair" in arg and decoded[j + 1][0] == "b"
                ]
                require(len(joins) <= 1, "ambiguous recovery join")
                self.join = joins[0] if joins else None
        else:
            idx = blob("subtree_index", 4)
            z = blob("recursive_height", 4) if mode == "inductive" else b32(height)
            s.add_constraints(c.ULE(idx, c.LShR(b32(2**20 - 1), z)))
            args = (RESULT, KEY, idx.zero_extend(32), z.zero_extend(32), SEED, ADRS)
            if mode == "inductive":
                s.add_constraints(c.UGE(z, 8), c.ULE(z, 14))
                kids = [blob("recursive_child", n) for _ in range(2)]
                for side in range(2):
                    self.events.append(("child", idx * 2 + side, z - 1, kids[side]))
                self.output = blob("subtree_parent", n)
                self.events.append(("pair", idx, z, c.Concat(*kids), self.output))
            else:
                ids = [(idx << height) + i for i in range(1 << height)]
                vals = self.level(6, 0, ids, [self.sk] * len(ids))
                vals = self.level(3, 0, ids, vals)
                for level in range(1, height + 1):
                    ids = [(idx << (height - level)) + i for i in range(len(vals) // 2)]
                    vals = self.level(
                        3,
                        level,
                        ids,
                        [c.Concat(a, b) for a, b in zip(vals[::2], vals[1::2])],
                    )
                self.output = vals[0]
        for i, value in enumerate(args):
            setattr(s.regs, f"x{i}", value)
        s.regs.x8 = RESULT
        self.ro = [
            (KEY, n),
            (ADRS, 28),
            (SEED, 96 + n),
            (param, 36),
            image.sections[b"__const"][:2],
        ]
        if mode == "recover":
            self.ro.extend([(MD, m.md), (SIG, m.forslen)])
        self.domain = list(s.solver.constraints)
        self.guard()

    def block(self, typ, level, idx, value, b):
        adr = c.Concat(
            self.layer[7:0], self.tree, c.BVV(typ, 8), self.kp, b32(level), b32(idx)
        )
        used = 22 + value.size() // 8
        return c.Concat(
            adr,
            value,
            c.BVV(b"\x80" + bytes(b - used - 9) + ((b + used) * 8).to_bytes(8, "big")),
        )

    def level(self, typ, h, ids, inputs):
        results = [blob("tweakable_hash", self.n) for _ in ids]
        if self.n == 16 or h == 0:
            rows = [
                (i, self.block(typ, h, i, x, 64), y)
                for i, x, y in zip(ids, inputs, results)
            ]
            self.events.append(("chain", rows))
        else:
            for j in range(0, len(ids) - 1, 2):
                blocks = c.Concat(
                    *(self.block(typ, h, ids[t], inputs[t], 128) for t in (j, j + 1))
                )
                self.events.append(("paired", blocks, c.Concat(*results[j : j + 2])))
            if len(ids) % 2:
                self.events.append(("pair", ids[-1], h, inputs[-1], results[-1]))
        return results

    def regions(self, s, kind):
        areas = [(STACK - 32768, 32768), (RESULT, self.n)]
        areas += [
            (int(p), int(cap) * al)
            for p, (cap, al, _) in s.globals["allocations"].items()
        ]
        return areas + self.ro if kind == "read" else areas

    def guard(self):
        self.s.memory.read_strategies = [SimConcretizationStrategySolutions(2)]

        def watch(s, kind):
            if not s.globals.get("native"):
                return
            ptr = getattr(s.inspect, f"mem_{kind}_address")
            size = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
            if not isinstance(ptr, int) and ptr.symbolic:
                ps = s.solver.eval_upto(ptr, 3)
                require(
                    kind == "read" and 0 < len(ps) <= 2, "unbounded symbolic address"
                )
            else:
                ps = [integer(s, ptr)]
            for p in ps:
                require(
                    any(a <= p and p + size <= a + l for a, l in self.regions(s, kind)),
                    f"unexpected {kind} at {p:#x} ({size})",
                )

        for k in ("read", "write"):
            self.s.inspect.b(
                "mem_" + k, when=angr.BP_BEFORE, action=lambda s, kind=k: watch(s, kind)
            )

    def check_address(self, s, p, typ, level, idx):
        for off, sz, v in [
            (0, 8, self.tree),
            (8, 4, self.layer),
            (12, 4, typ),
            (16, 4, self.kp),
            (20, 4, level),
            (24, 4, idx),
        ]:
            agree(s, unsigned(s, p + off, sz), v, f"FORS address word {off}")

    def call(self, s, name):
        n = self.n
        m = self.model
        x = [getattr(s.regs, f"x{i}") for i in range(9)]

        def reg(i, v):
            agree(s, x[i], v, f"{name} x{i}")

        def ptr(i, size):
            addr = integer(s, x[i])
            require(
                any(
                    a <= addr and addr + size <= a + l
                    for a, l in self.regions(s, "write")
                ),
                f"{name} output range",
            )
            return addr

        def stack(i, size):
            addr = integer(s, x[i])
            require(
                integer(s, s.regs.sp) <= addr and addr + size <= STACK,
                f"{name} workspace",
            )
            return addr

        ev = s.globals.get("event", 0)
        if name in ("chain", "child", "roots", "paired", "pair", "digits"):
            require(
                ev < len(self.events) and self.events[ev][0] == name,
                f"event {ev}: unexpected {name}",
            )
            _, *args = self.events[ev]
            s.globals["event"] = ev + 1
        if name == "zero":
            size = integer(s, x[1])
            dest = stack(0, size)
            wrbytes(s, dest, c.BVV(0, 8 * size))
        elif name == "digits":
            reg(0, MD)
            reg(1, m.md)
            reg(2, m.a)
            reg(3, m.k)
            # base_2b on this image is checked independently by sha2_fors_sign.py.
            cap = max(4, 1 << (m.k - 1).bit_length())
            desc = stack(8, 24)
            put(s, desc, cap, 8)
            put(s, desc + 8, HEAP, 8)
            put(s, desc + 16, m.k, 8)
            s.globals["allocations"] = {str(HEAP): (cap, 4, "digits")}
            wrbytes(s, HEAP, m.idx)
        elif name == "reserve":
            desc = stack(0, 24)
            used = integer(s, x[1])
            reg(2, n)
            reg(3, 1)
            reg(4, 1)
            oldcap = integer(s, unsigned(s, desc))
            old = integer(s, unsigned(s, desc + 8))
            agree(s, unsigned(s, desc + 16), used, "roots Vec initialized length")
            require(used <= oldcap < used + n, "growth boundary")
            cap = max(8, used + n, 2 * oldcap)
            addr = HEAP + (s.globals["serial"] + 1) * STRIDE
            s.globals["serial"] += 1
            alloc = dict(s.globals["allocations"])
            if oldcap:
                require(
                    alloc.pop(str(old)) == (oldcap, 1, "roots"),
                    "owned roots allocation",
                )
                wrbytes(s, addr, load(s, old, used))
            else:
                require(old == 1, "empty roots sentinel")
            alloc[str(addr)] = (cap, 1, "roots")
            s.globals["allocations"] = alloc
            put(s, desc, cap, 8)
            put(s, desc + 8, addr, 8)
        elif name == "free":
            m.release(s, integer(s, x[0]), x[1], integer(s, x[2]))
        elif name == "chain":
            rows = args[0]
            count = len(rows)
            reg(0, SEED + (96 if n == 32 else 64))
            reg(2, count)
            for i in [4, 6]:
                capacity = 35 if self.mode == "recover" else 128
                reg(i, capacity)
                stack(i - 1, 4 * capacity)
            blocks = stack(1, 64 * count)
            starts = stack(3, 4 * count)
            ends = stack(5, 4 * count)
            for j, (idx, expected, out) in enumerate(rows):
                agree(s, unsigned(s, starts + 4 * j, 4), idx, "chain first step")
                agree(s, unsigned(s, ends + 4 * j, 4), idx + 1, "chain last step")
                agree(
                    s,
                    load(s, blocks + 64 * j, 64),
                    expected,
                    "complete SHA-256 node block",
                )
                wrbytes(s, blocks + 64 * j + 22, out)
        elif name == "paired":
            expected, out = args
            reg(0, SEED)
            agree(
                s, load(s, stack(1, 256), 256), expected, "both SHA-512 parent blocks"
            )
            wrbytes(s, stack(2, 2 * n), out)
        elif name == "pair":
            idx, h, inputs, out = args
            reg(0, SEED)
            self.check_address(s, stack(1, 28), 3, h, idx)
            agree(
                s,
                c.Concat(load(s, x[2], n), load(s, x[3], n)),
                inputs,
                "ordered scalar parent children",
            )
            wrbytes(s, ptr(8, n), out)
        elif name == "child":
            idx, h, out = args
            reg(1, KEY)
            reg(2, idx.zero_extend(32))
            reg(3, h.zero_extend(32))
            reg(4, SEED)
            reg(5, ADRS)
            wrbytes(s, stack(0, n), out)
        elif name == "roots":
            value, out = args
            reg(0, SEED)
            self.check_address(s, stack(1, 28), 4, 0, 0)
            reg(3, m.k * n)
            a = integer(s, x[2])
            require(
                str(a) in s.globals["allocations"]
                and s.globals["allocations"][str(a)][0] >= m.k * n,
                "owned roots array",
            )
            agree(s, load(s, a, m.k * n), value, "ordered FORS roots")
            wrbytes(s, ptr(8, n), out)
        else:
            raise ValueError(name)
        clobber_scratch(s)
        s.regs.pc = s.regs.lr

    def successors(self, s, one=False):
        require(
            any(a <= s.addr < b for a, b in self.allowed),
            f"unexpected FORS exit {s.addr:#x}",
        )
        s.globals["native"] = True
        succ = self.project.factory.successors(s, **({"num_inst": 1} if one else {}))
        require(
            succ.flat_successors and not succ.unconstrained_successors,
            "incomplete successors",
        )
        for t in succ.flat_successors:
            t.globals["native"] = False
        return succ.flat_successors

    def run(self):
        s = self.s
        for steps in range(50000):
            if s.addr == RETURN:
                require(
                    s.globals["event"] == len(self.events)
                    and not s.globals["allocations"],
                    "incomplete trace",
                )
                agree(s, load(s, RESULT, self.n), self.output, "returned FORS value")
                self.model.check_abi(s)
                require(s.solver.satisfiable(), "infeasible return")
                orig = c.Solver()
                orig.add(c.And(*self.domain))
                require(
                    not orig.satisfiable(
                        extra_constraints=[c.Not(c.And(*s.solver.constraints))]
                    ),
                    "excluded valid inputs",
                )
                return
            name = (
                "child"
                if self.mode == "inductive" and steps and s.addr == self.node
                else self.hooks.get(s.addr)
            )
            if name:
                self.call(s, name)
                continue
            children = self.successors(s)
            if len(children) == 1:
                s = children[0]
                continue
            require(
                len(children) == 2 and self.mode == "recover" and self.join,
                "unexpected symbolic branch",
            )
            conditions = [[SimActionObject(t.history.jump_guard)] for t in children]
            arms = []
            for t in children:
                for _ in range(25):
                    if t.addr == self.join:
                        break
                    if self.hooks.get(t.addr) == "pair":
                        self.call(t, "pair")
                    else:
                        (t,) = self.successors(t, True)
                require(t.addr == self.join, "failed to rejoin parity branches")
                arms.append(t)
            require(
                arms[0].globals["event"] == arms[1].globals["event"],
                "branch trace mismatch",
            )
            s = arms[0].merge(arms[1], merge_conditions=conditions, common_ancestor=s)[
                0
            ]
        raise ValueError("FORS execution bound")


def check(task):
    path, n, v, mode, height = task
    Case(path, Image(path.read_bytes()), n, v, mode, height).run()
    if mode == "recover":
        return f"SHA2-{8 * n}{v}: all FORS digits, authentication paths and roots"
    if mode == "inductive":
        return f"n={n}: recursive subtree step at every height 8 through 14"
    return f"n={n}: subtree from all {1 << height} leaves at height {height}"


def mutations(path):
    image = Image(path.read_bytes())
    # Flip one linked instruction in each independently checked component.
    tests = [
        (
            b"4fors9fors_nodeKj10_EB4_",
            20,
            "w2, #0x1",
            16,
            "inductive",
            None,
            "child x2",
        ),
        (
            b"4fors10fors_batchKj18_EB4_",
            120,
            "w12, #0x6",
            24,
            "batch",
            3,
            "complete SHA-256 node block",
        ),
        (
            b"7parents7parentsKj18_EB6_",
            102,
            "w15, #0x80",
            24,
            "batch",
            3,
            "both SHA-512 parent blocks",
        ),
        (
            b"4fors16fors_pk_from_sigKj10_EB4_",
            298,
            "w9, #0x4",
            16,
            "recover",
            None,
            "FORS address word 12",
        ),
    ]
    with tempfile.TemporaryDirectory() as directory:
        bad = Path(directory) / "altered-fors"
        for name, i, operands, n, mode, height, msg in tests:
            pc, words = image.function(name, b"6slhdsa")
            require(
                instructions(path, pc, words)[i] == ("mov", operands),
                "unexpected mutation site",
            )
            data = bytearray(image.data)
            struct.pack_into("<I", data, pc - image.base + 4 * i, words[i] ^ (1 << 5))
            bad.write_bytes(data)
            try:
                check((bad, n, "s", mode, height))
            except ValueError as err:
                require(msg in str(err), f"unexpected mutation result: {err}")
            else:
                raise AssertionError(f"accepted alteration to {msg}")
    print(
        "Rejected altered recursive child, PRF domain, SHA-512 parent padding and roots domain",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("binary", type=Path)
    parser.add_argument("--width", type=int, choices=(16, 24, 32))
    parser.add_argument("--height", type=int, choices=range(8))
    parser.add_argument("--mode", choices=("recover", "batch", "inductive"))
    parser.add_argument("--variant", choices=("s", "f"))
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--self-test", action="store_true")
    a = parser.parse_args()
    tasks = []
    require(a.jobs >= 1, "jobs must be positive")
    for n in [a.width] if a.width else [16, 24, 32]:
        if a.mode in (None, "inductive"):
            tasks.append((a.binary, n, "s", "inductive", None))
        if a.mode in (None, "batch"):
            for z in [a.height] if a.height is not None else range(8):
                tasks.append((a.binary, n, "s", "batch", z))
        if a.mode in (None, "recover"):
            for v in [a.variant] if a.variant else "sf":
                tasks.append((a.binary, n, v, "recover", None))
    if a.jobs == 1:
        for task in tasks:
            print(check(task), flush=True)
    else:
        with ProcessPoolExecutor(a.jobs) as pool:
            for result in pool.map(check, tasks):
                print(result, flush=True)
    if a.self_test:
        mutations(a.binary)
    print("Mach-O SHA-256", hashlib.sha256(a.binary.read_bytes()).hexdigest())
