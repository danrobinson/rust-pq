# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Verify linked SHAKE WOTS batches. Indices may be any permutation of the legal chain IDs.
Each indexed store must produce the expected chain fragment at the exact byte address.
Because each ID occurs exactly once, these stores materialize the checked endpoint array.
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys
import hashlib
import struct
import tempfile

sys.dont_write_bytecode = True
from wots_chains import (
    Chain,
    ImageEnv,
    c,
    angr,
    Image,
    blob,
    load,
    unsigned,
    put,
    wrbytes,
    agrees,
    integer,
    require,
    return_call,
    matrix,
    b32,
    packed,
    padded,
    STACK,
    KEY,
    RESULT,
    RETURN,
    SEED,
    ADDRESS,
)

from wots_order import prove as prove_order

HEAP, DIGITS, SIG, READBUF, WRITEBUF = (
    0x400000,
    KEY + 1024,
    KEY + 4096,
    0x900000,
    0x910000,
)


class Batch:
    def __init__(self, env, kind, path):
        self.e, self.n, self.kind = env, env.n, kind
        self.chain_count = 2 * env.n + 3
        self.body = env.fun(f"5batch{len(kind)}{kind}".encode() + env.suffix)
        self.allowed = [self.body, env.fun(b"5batch6header" + env.suffix)]
        self.calls = {
            env.permute: "permute",
            env.fun(b"5batch6chains" + env.suffix)[0]: "chains",
            env.fun(b"5batch11chain_order")[0]: "order",
            env.fun(b"4hash5start" + env.suffix)[0]: "start",
            env.fun(b"6Sponge6absorb", b"8shake256")[0]: "absorb",
            env.fun(b"6Sponge6finish", b"8shake256")[0]: "finish",
            env.fun(b"19___rust_alloc_zeroed", b"___rustc")[0]: "alloc",
            env.fun(b"35___rust_no_alloc_shim_is_unstable_v2", b"___rustc")[0]: "shim",
        }
        lo, sz, _ = env.image.sections[b"__stubs"]
        stubs = subprocess.check_output(
            ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
        )
        (zero,) = [
            int(x, 16)
            for x in re.findall(r"^(0x[0-9a-f]+)\s+\d+\s+_bzero$", stubs, re.M)
            if lo <= int(x, 16) < lo + sz
        ]
        self.calls[zero] = "bzero"
        self.calls[env.fun(b"parallel6single", b"8shake256")[0]] = "single"
        self.native = {
            env.fun(b"4hash5start" + env.suffix)[0]: "start",
            env.fun(b"6Sponge6absorb", b"8shake256")[0]: "absorb",
            env.fun(b"6Sponge6finish", b"8shake256")[0]: "finish",
        }
        for pc in self.native:
            del self.calls[pc]
        self.allowed.extend(
            [
                env.fun(b"4hash5start" + env.suffix),
                env.fun(b"6Sponge6absorb", b"8shake256"),
                env.fun(b"6Sponge6finish", b"8shake256"),
            ]
        )
        self.seed, self.sk = blob("pk_seed", self.n), blob("sk_seed", self.n)
        self.layer, self.tree, self.kp = (
            blob("layer", 4),
            blob("tree", 8),
            blob("keypair", 4),
        )
        self.state = env.blank(self.body[0])
        s = self.state
        self.abi = {i: getattr(s.regs, f"x{i}") for i in range(18, 31)}
        self.simd = {i: getattr(s.regs, f"q{i}")[63:0] for i in range(8, 16)}
        self.end = [blob("endpoint", self.n) for _ in range(self.chain_count + 1)]
        self.ids = [
            c.BVS(f"chainID{j}", 7).zero_extend(57) for j in range(self.chain_count)
        ]
        self.ds = [c.BVS("digit", 4).zero_extend(28) for _ in range(self.chain_count)]
        self.sig = [blob("signatureWord", self.n) for _ in range(self.chain_count)]
        for j in self.ids:
            s.add_constraints(c.ULT(j, self.chain_count))
        self.endpoint_base = HEAP if kind == "sign" else None
        self.at = 0
        self.pending = []
        self.allocated = False
        self.expected_prf = None
        self.root = blob("final_key", self.n)
        self.special_write = False
        self.materialized = False
        self.order_seen = False
        self.finished = False
        self.started = False
        self.read_log = set()
        self.single = []
        self.single_at = 0
        if kind != "sign":
            addr = c.Concat(
                self.layer, b32(0), self.tree, b32(1), self.kp, b32(0), b32(0)
            )
            fields = [self.seed, addr] + self.end[: self.chain_count]
            state = [c.BVV(0, 64)] * 25
            pos = 0

            def permute():
                next = blob("T_permuted_state", 200)
                self.single.append((c.Concat(*state), next))
                return next.chop(64)

            for field in fields:
                for w in field.chop(64):
                    state[pos] = state[pos] ^ w
                    pos += 1
                    if pos == 17:
                        state = permute()
                        pos = 0
            state[pos] = state[pos] ^ c.BVV(b"\x1f" + bytes(7))
            state[16] = state[16] ^ c.BVV(bytes(7) + b"\x80")
            self.root = permute()[0 : self.n // 8]
            self.root = c.Concat(*self.root)
        wrbytes(s, SEED, self.seed)
        wrbytes(s, KEY, self.sk)
        for off, size, v in [
            (0, 8, self.tree),
            (8, 4, self.layer),
            (12, 4, 0),
            (16, 4, self.kp),
            (20, 4, blob("previous_word2", 4)),
            (24, 4, blob("previous_word3", 4)),
        ]:
            put(s, ADDRESS + off, v, size)
        siglen = c.BVS("full_input_signature_slice_length", 63).zero_extend(1)
        s.add_constraints(c.UGE(siglen, self.n * self.chain_count))
        args = {
            "keygen": [KEY, SEED, ADDRESS],
            "sign": [KEY, SEED, ADDRESS, DIGITS, self.chain_count],
            "recover": [SIG, siglen, SEED, ADDRESS, DIGITS, self.chain_count],
        }
        for i, v in enumerate(args[kind]):
            setattr(s.regs, f"x{i}", v)
        s.regs.x8 = RESULT
        for k in ("read", "write"):
            s.inspect.b(
                "mem_" + k,
                when=angr.BP_BEFORE,
                action=lambda st, k=k: self.memory(st, k),
            )

    def memory(self, s, kind):
        expr = getattr(s.inspect, "mem_" + kind + "_address")
        le = getattr(s.inspect, "mem_" + kind + "_length")
        size = (
            integer(s, le)
            if le is not None
            else getattr(s.inspect, "mem_" + kind + "_expr").size() // 8
        )
        if isinstance(expr, int) or not expr.symbolic:
            addr = integer(s, expr)
            if self.endpoint_base is not None and (
                self.allocated or self.kind == "recover"
            ):
                hi = self.endpoint_base + self.n * (
                    self.chain_count if self.kind == "sign" else 67
                )
                if (
                    addr < hi
                    and self.endpoint_base < addr + size
                    and not self.special_write
                ):
                    require(
                        kind == "read" and self.materialized,
                        "unlogged direct endpoint access",
                    )
            lo, length = self.e.const
            ranges = [
                (STACK - 16384, STACK),
                (RESULT, RESULT + (24 if self.kind == "sign" else self.n)),
                (READBUF, READBUF + 64),
                (WRITEBUF, WRITEBUF + 64),
            ]
            if self.allocated:
                ranges.append((HEAP, HEAP + self.chain_count * self.n))
            if kind == "read":
                ranges += [
                    (KEY, KEY + self.n),
                    (SEED, SEED + self.n),
                    (ADDRESS, ADDRESS + 28),
                    (lo, lo + length),
                ]
            require(
                any(a <= addr and addr + size <= b for a, b in ranges),
                f"out-of-region {kind} at {s.addr:x}: {addr:x}/{size}",
            )
            return
        # Indices come from a valid permutation; every symbolic access is checked before it
        # is redirected. The scratch materializes exactly the bytes named by the proven address.
        if kind == "read":
            for k in range(self.at, min(self.chain_count, self.at + 2)):
                idx = self.ids[k]
                if expr.variables != idx.variables:
                    continue
                for base, scale, data, delta in [
                    (DIGITS, 4, self.ds[k].reversed, 0)
                ] + [(SIG, self.n, self.sig[k], j) for j in range(0, self.n, 8)]:
                    if delta + size > data.size() // 8 or (
                        base == SIG and self.kind != "recover"
                    ):
                        continue
                    if not c.is_true(c.simplify(expr == base + scale * idx + delta)):
                        if s.solver.satisfiable(
                            extra_constraints=[expr != base + scale * idx + delta]
                        ):
                            continue
                    self.read_log.update(
                        (base, k, j) for j in range(delta, delta + size)
                    )
                    wrbytes(s, READBUF, data.get_bytes(delta, size))
                    s.inspect.mem_read_address = READBUF
                    return
        if kind == "write" and self.endpoint_base is not None:
            value = s.inspect.mem_write_expr
            data = value.reversed if s.inspect.mem_write_endness == "Iend_LE" else value
            for k, idx, output, covered in self.pending:
                if expr.variables != idx.variables:
                    continue
                for delta in range(0, self.n - size + 1, 8):
                    if s.solver.satisfiable(
                        extra_constraints=[
                            expr != self.endpoint_base + self.n * idx + delta
                        ]
                    ):
                        continue
                    agrees(
                        s,
                        data,
                        output.get_bytes(delta, size),
                        "scattered endpoint bytes",
                    )
                    fragment = set(range(delta, delta + size))
                    require(not (covered & fragment), "duplicate output store")
                    covered.update(fragment)
                    s.inspect.mem_write_address = WRITEBUF
                    return
        raise ValueError(
            f"unmodeled indexed {kind} at {s.addr:x}, {expr}, {size}, {self.at}"
        )

    def flush(self):
        for _, _, _, covered in self.pending:
            require(covered == set(range(self.n)), "incomplete selected lane")
        self.pending = []

    def materialize(self, s):
        self.flush()
        require(
            self.at == self.chain_count and self.endpoint_base is not None,
            "early endpoint materialization",
        )
        self.special_write = True
        for j in range(self.chain_count):
            wrbytes(s, self.endpoint_base + self.n * j, self.end[j])
        self.special_write = False
        self.materialized = True

    def choose(self, k):
        # The value of the (arbitrary) endpoint family at the requested ID.
        return c.ite_dict(
            self.ids[k],
            {j: v for j, v in enumerate(self.end[: self.chain_count])},
            self.end[-1],
        )

    def handle(self, s, name):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        reg = lambda i, v: agrees(s, x[i], v, name + " argument " + str(i))

        def buf(i, count):
            addr = integer(s, x[i])
            require(
                integer(s, s.regs.sp) <= addr <= STACK - count, "callee stack buffer"
            )
            return addr

        if name == "order":
            require(self.kind != "keygen" and not self.order_seen, "extra chain order")
            reg(0, DIGITS)
            reg(1, self.chain_count)
            p = buf(8, 67 * 8)
            for i, v in enumerate(self.ids):
                put(s, p + 8 * i, v, 8)
            self.order_seen = True
        elif name == "bzero":
            require(
                self.kind == "recover" and self.endpoint_base is None,
                "unexpected endpoint bzero",
            )
            reg(1, self.n * 67)
            self.endpoint_base = buf(0, self.n * 67)
            self.special_write = True
            wrbytes(s, self.endpoint_base, c.BVV(0, 8 * self.n * 67))
            self.special_write = False
        elif name == "shim":
            require(
                self.kind == "sign" and not self.allocated, "unexpected allocator shim"
            )
        elif name == "alloc":
            require(self.kind == "sign" and not self.allocated, "unexpected allocation")
            reg(0, self.chain_count * self.n)
            reg(1, 1)
            self.allocated = True
            self.special_write = True
            wrbytes(s, HEAP, c.BVV(0, 8 * self.n * self.chain_count))
            self.special_write = False
            return_call(s, HEAP)
            return
        elif name == "permute":
            self.flush()
            require(
                self.kind != "recover"
                and self.at < self.chain_count
                and self.expected_prf is None,
                "unexpected leaf permutation",
            )
            ks = [
                self.at,
                self.at + 1
                if self.kind == "keygen"
                else min(self.at + 1, self.chain_count - 1),
            ]
            ids = [b32(k) if self.kind == "keygen" else self.ids[k][31:0] for k in ks]
            expected = matrix(
                [
                    padded(
                        c.Concat(
                            self.seed,
                            self.layer,
                            b32(0),
                            self.tree,
                            b32(5),
                            self.kp,
                            i,
                            b32(0),
                            self.sk,
                        )
                    )
                    for i in ids
                ]
            )
            ptr = buf(0, 400)
            agrees(
                s, load(s, ptr, 400), expected, "WOTS_PRF two complete padded messages"
            )
            outs = [blob("prfKeccak", 200) for _ in range(2)]
            wrbytes(s, ptr, matrix(outs))
            self.expected_prf = [v.get_bytes(0, self.n) for v in outs]
        elif name == "chains":
            self.flush()
            require(
                self.at < self.chain_count
                and (self.kind == "keygen" or self.order_seen),
                "extra chain pair",
            )
            ks = [
                self.at,
                self.at + 1
                if self.kind == "keygen"
                else min(self.at + 1, self.chain_count - 1),
            ]
            ids = [c.BVV(k, 64) if self.kind == "keygen" else self.ids[k] for k in ks]
            reg(1, SEED)
            reg(2, ADDRESS)
            reg(3, ids[0])
            reg(4, ids[1])
            inp = (
                self.expected_prf
                if self.kind != "recover"
                else [self.sig[k] for k in ks]
            )
            require(inp is not None, "missing WOTS_PRF")
            agrees(
                s,
                load(s, buf(5, 2 * self.n), 2 * self.n),
                c.Concat(*inp),
                "selected chain input",
            )
            self.expected_prf = None
            digits = [self.ds[k] for k in ks] if self.kind != "keygen" else []
            reg(6, packed(digits) if self.kind == "recover" else 0)
            reg(7, packed(digits) if self.kind == "sign" else (15 << 32) | 15)
            if self.kind != "keygen":
                for k in ks:
                    for j in range(4):
                        require((DIGITS, k, j) in self.read_log, "missing WOTS digit")
                    if self.kind == "recover":
                        for j in range(self.n):
                            require(
                                (SIG, k, j) in self.read_log,
                                "missing signature input byte",
                            )
            outs = [
                self.end[k] if self.kind == "keygen" else self.choose(k) for k in ks
            ]
            wrbytes(s, buf(0, 2 * self.n), c.Concat(*outs))
            if self.kind != "keygen":
                self.pending = [
                    (k, idx, out, set()) for k, idx, out in zip(ks, ids, outs)
                ][: min(2, self.chain_count - self.at)]
            self.at = min(self.chain_count, self.at + 2)
        elif name == "single":
            require(
                self.started and self.single_at < len(self.single),
                "unexpected public-key permutation",
            )
            before, after = self.single[self.single_at]
            p = buf(0, 200)
            agrees(
                s,
                load(s, p, 200),
                before,
                "T absorbs seed, WOTS_PK address, ordered endpoints and SHAKE padding",
            )
            wrbytes(s, p, after)
            self.single_at += 1
        return_call(s)

    def run(self):
        s = self.state
        initial = tuple(s.solver.constraints)
        for step in range(5000):
            if s.addr == RETURN:
                if self.kind == "sign":
                    self.flush()
                    require(self.at == self.chain_count, "incomplete signature")
                    require(self.allocated, "signature allocation")
                    for j, v in enumerate(
                        [self.n * self.chain_count, HEAP, self.n * self.chain_count]
                    ):
                        agrees(s, unsigned(s, RESULT + j * 8), v, "signature Vec")
                else:
                    require(
                        self.finished and self.single_at == len(self.single),
                        "missing public key permutation",
                    )
                    agrees(s, load(s, RESULT, self.n), self.root, "returned key")
                agrees(s, s.regs.sp, STACK, "return SP")
                for j, v in self.abi.items():
                    agrees(s, getattr(s.regs, f"x{j}"), v, "preserved register")
                for j, v in self.simd.items():
                    agrees(s, getattr(s.regs, f"q{j}")[63:0], v, "preserved SIMD")
                # No symbolic input may have been lost by VEX branch/address choices.
                proof = c.Solver()
                proof.add(initial)
                require(
                    not proof.satisfiable(
                        extra_constraints=[c.Not(c.And(*s.solver.constraints))]
                    ),
                    "narrowed WOTS input domain",
                )
                return step
            if s.addr in self.native and self.native[s.addr] == "start":
                require(
                    self.kind != "sign" and not self.started,
                    "unexpected public key initialization",
                )
                self.started = True
                if self.kind == "recover":
                    self.materialize(s)
            if s.addr in self.native and self.native[s.addr] == "finish":
                require(
                    self.started and self.at == self.chain_count and not self.finished,
                    "unexpected public key finalization",
                )
                self.finished = True
            if s.addr in self.e.stubs:
                self.e.library(s)
            elif s.addr in self.calls:
                self.handle(s, self.calls[s.addr])
            else:
                require(
                    any(a <= s.addr < b for a, b in self.allowed),
                    f"unknown WOTS exit {s.addr:x}",
                )
                state = self.e.project.factory.successors(s)
                require(
                    len(state.flat_successors) == 1
                    and not state.unconstrained_successors,
                    f"unresolved WOTS branch {s.addr:x}",
                )
                s = state.flat_successors[0]
        raise ValueError("WOTS execution bound")


def mutation_tests(path, image):
    """Change the actual width-16 bytes and require the corresponding proof to fail."""
    base, _, file_offset = image.sections[b"__text"]
    controls = [
        (b"5batch6chainsKj10_EB6_", 0x120, 0x110006B5, 1 << 10, "round"),
        (b"5batch11chain_order", 0x14C, 0xF8287A89, 1, "order"),
        (b"5batch6keygenKj10_EB6_", 0x80, 0x528000B7, 1 << 5, "keygen"),
        (b"5batch4signKj10_EB6_", 0x214, 0x3CA06900, 1, "sign"),
    ]
    for suffix, off, expected, flip, kind in controls:
        pc, words = image.function(suffix, b"6slhdsa5shake")
        require(words[off // 4] == expected, "missing WOTS negative control")
        raw = bytearray(image.data)
        struct.pack_into("<I", raw, file_offset + pc - base + off, expected ^ flip)
        changed = Image(raw)
        with tempfile.TemporaryDirectory() as folder:
            binary = Path(folder) / "changed"
            binary.write_bytes(raw)
            env = ImageEnv(binary, changed, 16)
            try:
                if kind == "round":
                    Chain(env).run(True)
                elif kind == "order":
                    prove_order(env, binary)
                else:
                    Batch(env, kind, binary).run()
            except ValueError as error:
                require(
                    "counterexample" in str(error),
                    f"unexpected WOTS mutation failure: {error}",
                )
            else:
                raise AssertionError(f"WOTS mutation passed: {kind}")


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("image", type=Path)
    p.add_argument("--width", type=int, choices=(16, 24, 32))
    p.add_argument("--kind", choices=("keygen", "sign", "recover"))
    p.add_argument("--self-test", action="store_true")
    args = p.parse_args()
    image = Image(args.image.read_bytes())
    print("Mach-O SHA-256", hashlib.sha256(image.data).hexdigest(), flush=True)
    if args.kind is None:
        print(
            "order",
            prove_order(ImageEnv(args.image, image, 16), args.image),
            flush=True,
        )
    for n in [args.width] if args.width else (16, 24, 32):
        env = ImageEnv(args.image, image, n)
        if args.kind is None:
            chain = Chain(env)
            print(n, "chains", chain.run(False), chain.run(True), flush=True)
        for k in [args.kind] if args.kind else ("keygen", "sign", "recover"):
            print(n, k, Batch(env, k, args.image).run(), flush=True)
    if args.self_test:
        mutation_tests(args.image, image)
        print("Rejected four WOTS binary mutations")
