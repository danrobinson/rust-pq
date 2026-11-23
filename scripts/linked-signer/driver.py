# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Symbolically execute linked Apple arm64 SLH-DSA Algorithm 19 drivers with explicit callee contracts."""

import argparse
import hashlib
import logging
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

logging.getLogger("angr.state_plugins.unicorn_engine").setLevel(logging.CRITICAL)
import angr
import claripy as c

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "apple-binary"))
from entries import inspect
from image import Image, require, sign_extend
from sha256_seed import SeedCompression

BE, LE = "Iend_BE", "Iend_LE"
# Fixed, disjoint modeled ABI address layout. The code and parameter row retain their
# actual linked addresses. None of the addresses below are image-relative.
STACK, KEY, RANDOM, MESSAGE, RESULT = 0x70000000, 0x100000, 0x110000, 0x120000, 0x130000
CONTEXT, FRAMED = 0x140000, 0x50000000
RETURN = 0x200000
HEAP = 0x300000
STRIDE = 0x100000


def integer(state, value):
    if isinstance(value, int):
        return value
    return state.solver.eval_one(value)


def equal(state, x, y, detail):
    if isinstance(x, int) and isinstance(y, int):
        require(x == y, detail)
    elif state.solver.satisfiable(extra_constraints=[x != y]):
        raise ValueError("counterexample: " + detail)


def load(state, ptr, size):
    return state.memory.load(integer(state, ptr), size, endness=BE)


def unsigned(state, ptr, size=8):
    return state.memory.load(integer(state, ptr), size, endness=LE)


def put(state, ptr, value, size):
    state.memory.store(integer(state, ptr), value, size=size, endness=LE)


def blob(name, size):
    return c.BVS(name, 8 * size)


def wrbytes(state, addr, data):
    state.memory.store(integer(state, addr), data, endness=BE)


def chunks(name, size):
    return [(i, blob(name, min(size - i, 128))) for i in range(0, size, 128)]


def objects(path, image, n, variant, hash_family):
    shake = hash_family == "shake"
    family = b"6slhdsa5shake" if shake else b"6slhdsa"
    suffix = f"Kj{n:x}_EB{6 if shake else 4}_".encode()
    label = f"{hash_family}_{8 * n}{variant}"
    nm = f"6slhdsa4sets{len(label)}{label}17slh_sign_internal".encode()
    target = family + b"3slh17slh_sign_internal" + suffix
    row = inspect(image, nm, target, [None, "x0", "x1", "x2", 4 * n, "x3"])
    wrappers, w = image.function(nm, b"6slhdsa4sets")
    # The entry checker validates ADRP/ADD; recover the runtime parameter pointer from
    # that pair to run the driver against bytes in the measured image.
    (index,) = [j for j, v in enumerate(w) if v & 0x9F00001F == 0x90000000]
    v = w[index]
    param = (
        ((wrappers + 4 * index) & ~4095)
        + 4096 * sign_extend(((v >> 5 & 0x7FFFF) << 2) | (v >> 29 & 3), 21)
        + (w[index + 1] >> 10 & 4095)
    )
    fips = {
        (16, "s"): (16, 30, 63, 7, 9, 12, 14),
        (16, "f"): (16, 34, 66, 22, 3, 6, 33),
        (24, "s"): (24, 39, 63, 7, 9, 14, 17),
        (24, "f"): (24, 42, 66, 22, 3, 8, 33),
        (32, "s"): (32, 47, 64, 8, 8, 14, 22),
        (32, "f"): (32, 49, 68, 17, 4, 9, 35),
    }
    require(row == fips[n, variant], "standard FIPS parameter row")
    require(
        row == struct.unpack("<QQIIIII", image.read(b"__const", param, 36)),
        "entry parameter pointer",
    )

    def addr(ending):
        addresses = {a for name, a in image.symbols if name.endswith(ending)}
        require(len(addresses) == 1, f"ambiguous or missing callee {ending!r}")
        return addresses.pop()

    hooks = {
        addr(family + b"3slh12with_context"): "frame",
        addr(family + b"4hash5h_msg" + suffix): "hmsg",
        addr(b"___rust_dealloc"): "free",
    }
    if shake:
        hooks.update(
            {
                addr(b"6Sponge6absorb"): "absorb",
                addr(b"6Sponge6finish"): "finish",
                addr(b"6slhdsa4util7base_2b"): "indices",
                addr(family + b"10fors_batch4sign" + suffix): "fors",
                addr(family + b"10fors_batch7recover" + suffix): "recover",
                addr(family + b"2ht7ht_sign" + suffix): "ht",
                addr(family + b"4xmss9xmss_sign" + suffix): "xmss",
                addr(family + b"4xmss16xmss_pk_from_sig" + suffix): "xmss_root",
            }
        )
    else:
        hooks.update(
            {
                addr(family + b"4hash7prf_msg" + suffix): "prf",
                addr(family + b"4fors9fors_sign" + suffix): "sha_fors",
                addr(family + b"4fors16fors_pk_from_sig" + suffix): "sha_recover",
                addr(family + b"2ht7ht_sign" + suffix): "sha_ht",
            }
        )
        if n > 16:
            hooks[addr(family + b"4hash8seed_ctx" + suffix)] = "seed"
    (reserve,) = {
        a
        for name, a in image.symbols
        if b"do_reserve_and_handle" in name
        and b"11RawVecInnerp" in name
        and name.endswith(b"6slhdsa")
    }
    hooks[reserve] = "reserve"
    (grow,) = {
        a
        for name, a in image.symbols
        if b"6RawVecmE8grow_one" in name and name.endswith(b"6slhdsa")
    }
    hooks[grow] = "grow"
    stubs = subprocess.check_output(
        ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
    )
    start, size, _ = image.sections[b"__stubs"]
    (memcpy,) = [
        int(a, 16)
        for a in re.findall(r"^(0x[0-9a-f]+)\s+\d+\s+_memcpy$", stubs, re.M)
        if start <= int(a, 16) < start + size
    ]
    hooks[memcpy] = "copy"
    entry, words = image.function(target, family)
    return row, param, entry, entry + 4 * len(words), hooks


def clobber_scratch(s):
    # A normal AAPCS64 call can clobber caller-saved values. Scramble them
    # except x30, used by the hooked return, and the preserved halves of v8-v15.
    for i in range(18):
        setattr(s.regs, f"x{i}", c.BVS("scratch", 64))
    for i in range(32):
        old = getattr(s.regs, f"q{i}")
        setattr(
            s.regs,
            f"q{i}",
            c.Concat(c.BVS("scratch_high", 64), old[63:0])
            if 8 <= i < 16
            else c.BVS("scratch_simd", 128),
        )
    s.regs.cc_op = 0
    s.regs.cc_dep1 = c.BVS("NZCV", 64)
    s.regs.cc_dep2 = 0
    s.regs.cc_ndep = 0


class Driver:
    def __init__(self, row, param, api, hash_family):
        self.family = hash_family
        self.api = api
        self.n, m, h, d, hp, a, k = row
        self.m, self.h, self.hp, self.a, self.k = m, h, hp, a, k
        self.param = param
        self.md = (k * a + 7) // 8
        self.forslen = k * (a + 1) * self.n
        self.htlen = d * (2 * self.n + 3 + hp) * self.n
        self.total = self.n + self.forslen + self.htlen
        self.sk = [blob("key_block", self.n) for _ in range(4)]
        self.rand = blob("randomizer", self.n)
        self.msglen = c.BVS("message_length", 64)
        self.ctxlen = c.BVS("context_length", 64)
        self.framed = self.msglen + self.ctxlen + 2
        self.r = blob("R", self.n)
        self.digest = blob("digest", m)
        self.pkfors = blob("fors_root", self.n)
        self.fors = chunks("fors_signature", self.forslen)
        self.d = d
        self.layerlen = self.htlen // d
        self.layers = [chunks("xmss_signature", self.layerlen) for _ in range(d)]
        self.roots = [self.pkfors] + [blob("xmss_root", self.n) for _ in range(d - 1)]
        self.ht = [
            (i * self.layerlen + off, val)
            for i, layer in enumerate(self.layers)
            for off, val in layer
        ]
        # The native index vector stores k big-endian base-2^a digits as LE u32s.
        digits = [
            self.digest[m * 8 - 1 - i * a : m * 8 - (i + 1) * a]
            .zero_extend(32 - a)
            .reversed
            for i in range(k)
        ]
        self.idx = c.Concat(*digits)
        b = h - hp
        treebytes = (b + 7) // 8
        self.tree = self.digest.get_bytes(self.md, treebytes)[b - 1 : 0].zero_extend(
            64 - b
        )
        self.leaf = self.digest.get_bytes(self.md + treebytes, (hp + 7) // 8)[
            hp - 1 : 0
        ].zero_extend(64 - hp)
        self.sponge = [blob("opaque_sponge", 208) for _ in range(3)]
        self.schedule = (
            (
                "absorb",
                "absorb",
                "absorb",
                "finish",
                "hmsg",
                "indices",
                "fors",
                "indices",
                "recover",
                "ht",
            )
            if hash_family == "shake"
            else ("prf", "hmsg")
            + (("seed",) if self.n > 16 else ())
            + ("sha_fors", "sha_recover", "sha_ht")
        )
        self.inline_seed = (
            SeedCompression(self.sk[2])
            if hash_family == "sha2" and self.n == 16
            else None
        )
        self.seed = (
            self.inline_seed.seed
            if self.inline_seed
            else blob("seed_context", 96 + self.n)
        )
        self.final_paths = 0
        self.rejections = 0

    @staticmethod
    def workspace(s, pointer, width):
        address = integer(s, pointer)
        require(
            STACK - 2048 <= address <= STACK - width,
            "callee output outside stack frame",
        )
        return address

    def vec(self, s, desc, name, length, alignment, data, capacity=None):
        # Opaque Rust Vec result layout for this linked ABI (capacity, pointer, length).
        self.workspace(s, desc, 24)
        require(0 <= length <= STRIDE // alignment, "vector exceeds modeled allocation")
        ordinal = s.globals["serial"] + 1
        s.globals["serial"] = ordinal
        address = HEAP + ordinal * STRIDE
        cap = c.BVS(name + "_capacity", 64) if capacity is None else c.BVV(capacity, 64)
        s.add_constraints(c.UGE(cap, length), c.ULE(cap, STRIDE // alignment))
        put(s, desc, cap, 8)
        put(s, desc + 8, address, 8)
        put(s, desc + 16, length, 8)
        for off, value in data:
            wrbytes(s, address + off, value)
        s.globals["allocations"] = dict(
            s.globals["allocations"], **{str(address): (cap, alignment, name)}
        )
        s.globals[name] = address
        return address

    def start(self, state):
        for i, b in enumerate(self.sk):
            wrbytes(state, KEY + i * self.n, b)
        wrbytes(state, RANDOM, self.rand)
        regs = (
            [MESSAGE, self.msglen, KEY, RANDOM]
            if self.api == "slh_sign_internal"
            else [MESSAGE, self.msglen, CONTEXT, self.ctxlen, KEY, RANDOM]
        )
        if self.api == "sign_deterministic":
            self.rand = self.sk[2]
        for i, val in enumerate(regs):
            setattr(state.regs, "x" + str(i), val)
        state.regs.x8 = RESULT
        state.regs.sp = STACK
        state.regs.lr = RETURN
        state.globals["serial"] = 0
        state.globals["calls"] = ()
        state.globals["allocations"] = {}
        state.globals["vector_saved"] = tuple(
            getattr(state.regs, f"q{i}")[63:0] for i in range(8, 16)
        )
        state.globals["platform"] = state.regs.x18
        state.globals["saved"] = tuple(
            getattr(state.regs, f"x{i}") for i in range(19, 30)
        )
        state.add_constraints(
            c.ULE(self.msglen, 2**63 - 1), c.ULE(self.ctxlen, 2**63 - 1)
        )
        if self.api != "slh_sign_internal":
            state.add_constraints(
                c.Or(
                    c.UGT(self.ctxlen, 255), c.ULE(self.msglen, 2**63 - 3 - self.ctxlen)
                )
            )

    def check_address(self, s, p):
        for offset, width, val in [
            (0, 8, self.tree),
            (8, 4, 0),
            (12, 4, 3),
            (16, 4, self.leaf[31:0]),
            (20, 4, 0),
            (24, 4, 0),
        ]:
            equal(
                s,
                unsigned(s, p + offset, width),
                val,
                "FORS address field " + str(offset),
            )

    def call(self, s, name):
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        dest = lambda i: integer(s, x[i])
        check = lambda i, y: equal(s, x[i], y, f"{name}: x{i}")
        buf = lambda i, v: equal(
            s, load(s, x[i], v.size() // 8), v, f"{name}: buffer {i}"
        )
        calls = s.globals["calls"]
        if name not in (
            "free",
            "reserve",
            "copy",
            "grow",
            "frame",
            "xmss",
            "xmss_root",
        ):
            schedule = self.schedule
            require(
                len(calls) < len(schedule) and schedule[len(calls)] == name,
                "unexpected cryptographic call order",
            )
            s.globals["calls"] = (*calls, name)
        n = self.n
        public = self.api != "slh_sign_internal"
        msg = FRAMED if public else MESSAGE
        msglen = self.framed if public else self.msglen
        if name == "frame":
            require(
                public and not s.globals.get("framed", False), "unexpected framing call"
            )
            check(0, MESSAGE)
            check(1, self.msglen)
            check(2, CONTEXT)
            check(3, self.ctxlen)
            equal(
                s, c.ULE(self.ctxlen, 255), True, "oversized context passed to framing"
            )
            # Byte contents of FRAMED are the Alg.22 prefix, context and message.
            # This driver forwards this opaque slice verbatim to both hash consumers.
            cap = c.BVS("frame_capacity", 64)
            s.add_constraints(c.UGE(cap, self.framed), c.ULE(cap, 2**63 - 1))
            self.workspace(s, x[8], 24)
            put(s, dest(8), cap, 8)
            put(s, dest(8) + 8, FRAMED, 8)
            put(s, dest(8) + 16, self.framed, 8)
            s.globals["framed"] = True
            s.globals["allocations"] = dict(
                s.globals["allocations"], **{str(FRAMED): (cap, 1, "framed")}
            )
        elif name == "prf":
            buf(0, self.sk[1])
            buf(1, self.rand)
            check(2, msg)
            check(3, msglen)
            wrbytes(s, self.workspace(s, x[8], n), self.r)
        elif name == "seed":
            buf(0, self.sk[2])
            wrbytes(s, self.workspace(s, x[8], self.seed.size() // 8), self.seed)
        elif name == "sha_fors":
            check(0, self.param)
            buf(1, self.digest.get_bytes(0, self.md))
            check(2, self.md)
            buf(3, self.sk[0])
            buf(4, self.seed)
            self.check_address(s, dest(5))
            self.vec(s, dest(8), "fors", self.forslen, 1, self.fors)
        elif name == "sha_recover":
            check(0, self.param)
            check(1, s.globals["fors"])
            check(2, self.forslen)
            self.check_chunks(s, dest(1), self.fors)
            buf(3, self.digest.get_bytes(0, self.md))
            check(4, self.md)
            buf(5, self.seed)
            self.check_address(s, dest(6))
            wrbytes(s, self.workspace(s, x[8], n), self.pkfors)
        elif name == "sha_ht":
            check(0, self.param)
            buf(1, self.pkfors)
            buf(2, self.sk[0])
            buf(3, self.seed)
            check(4, self.tree)
            check(5, self.leaf)
            self.vec(s, dest(8), "ht", self.htlen, 1, self.ht)
        elif name == "absorb":
            i = len(calls)
            buf(0, c.BVV(0, 208 * 8) if i == 0 else self.sponge[i - 1])
            if i == 0:
                buf(1, self.sk[1])
                check(2, n)
            elif i == 1:
                buf(1, self.rand)
                check(2, n)
            else:
                check(1, msg)
                check(2, msglen)
            wrbytes(s, self.workspace(s, x[0], 208), self.sponge[i])
        elif name == "finish":
            buf(0, self.sponge[-1])
            check(2, n)
            wrbytes(s, self.workspace(s, x[0], 208), blob("consumed_sponge", 208))
            wrbytes(s, self.workspace(s, x[1], n), self.r)
        elif name == "hmsg":
            check(0, self.param)
            buf(1, self.r)
            buf(2, self.sk[2])
            buf(3, self.sk[3])
            check(4, msg)
            check(5, msglen)
            self.vec(s, dest(8), "digest", self.m, 1, [(0, self.digest)])
        elif name == "indices":
            buf(0, self.digest.get_bytes(0, self.md))
            check(1, self.md)
            check(2, self.a)
            check(3, self.k)
            s.globals["base_ret"] = integer(s, s.regs.lr)
            s.globals["base_out"] = dest(8)
            return  # The machine executes the actual callee from here.
        elif name == "grow":
            desc = dest(0)
            old = integer(s, unsigned(s, desc + 8))
            length = integer(s, unsigned(s, desc + 16))
            equal(s, unsigned(s, desc), length, "grow_one invoked on a full vector")
            if length:
                require(old == s.globals["indices"], "grown index vector pointer")
                self.release(s, old, 4 * length, 4)
            else:
                require(old == 4, "u32 vector dangling sentinel")
            contents = [] if not length else [(0, load(s, old, 4 * length))]
            self.vec(
                s, desc, "indices", length, 4, contents, capacity=max(4, length * 2)
            )
        elif name in ("fors", "recover"):
            check(0, self.param)
            check(1, s.globals["indices"])
            buf(1, self.idx)
            check(2, self.k)
            if name == "fors":
                buf(3, self.sk[0])
                buf(4, self.sk[2])
                self.check_address(s, dest(5))
                self.vec(s, dest(8), "fors", self.forslen, 1, self.fors)
            else:
                check(3, s.globals["fors"])
                check(4, self.forslen)
                buf(5, self.sk[2])
                self.check_address(s, dest(6))
                self.check_chunks(s, dest(3), self.fors)
                wrbytes(s, self.workspace(s, x[8], n), self.pkfors)
        elif name == "ht":
            check(0, self.param)
            buf(1, self.pkfors)
            buf(2, self.sk[0])
            buf(3, self.sk[2])
            check(4, self.tree)
            check(5, self.leaf)
            s.globals["ht_ret"] = integer(s, s.regs.lr)
            s.globals["ht_out"] = dest(8)
            s.globals["layer_event"] = 0
            return
        elif name in ("xmss", "xmss_root"):
            require(
                s.globals.get("ht_ret") is not None, "XMSS invocation outside hypertree"
            )
            event = s.globals["layer_event"]
            j = event // 2
            require(
                event < 2 * self.d - 1 and (name == "xmss") == (event % 2 == 0),
                "XMSS call order",
            )
            tree = c.LShR(self.tree, j * self.hp)
            leaf = (
                self.leaf
                if j == 0
                else c.LShR(self.tree, (j - 1) * self.hp) & ((1 << self.hp) - 1)
            )
            check(0, self.param)
            ap = dest(5 if name == "xmss" else 6)
            equal(s, unsigned(s, ap), tree, "XMSS tree coordinate")
            equal(s, unsigned(s, ap + 8, 4), j, "XMSS layer")
            equal(s, load(s, ap + 12, 16), 0, "XMSS remaining address fields")
            if name == "xmss":
                buf(1, self.roots[j])
                buf(2, self.sk[0])
                check(3, leaf)
                buf(4, self.sk[2])
                self.vec(s, dest(8), "layer", self.layerlen, 1, self.layers[j])
            else:
                check(1, leaf)
                check(2, s.globals["layer"])
                check(3, self.layerlen)
                self.check_chunks(s, dest(2), self.layers[j])
                buf(4, self.roots[j])
                buf(5, self.sk[2])
                wrbytes(s, self.workspace(s, x[8], n), self.roots[j + 1])
            s.globals["layer_event"] = event + 1
        elif name == "reserve":
            desc = dest(0)
            used, additional = dest(1), dest(2)
            require(
                additional > 0 and used + additional <= STRIDE,
                "reserve size outside modeled heap",
            )
            check(3, 1)
            check(4, 1)
            equal(s, unsigned(s, desc + 16), used, "reserve live length")
            old = integer(s, unsigned(s, desc + 8))
            upper = s.globals.get("ht_ret") is not None
            region = "ht" if upper else "signature"
            previous = integer(s, unsigned(s, desc)) if upper else None
            if used:
                require(old == s.globals[region], "reserve old pointer")
                self.release(s, old, unsigned(s, desc), 1)
            else:
                equal(s, unsigned(s, desc), 0, "empty vector")
                require(old == 1, "initial dangling sentinel")
            # RawVec reserve preserves all live bytes. Model arbitrary sufficient new capacity.
            data = [
                (i, load(s, old + i, min(used - i, 128))) for i in range(0, used, 128)
            ]
            new = self.vec(
                s,
                desc,
                region,
                used,
                1,
                data,
                capacity=max(2 * previous, used + additional, 8) if upper else None,
            )
            cap = s.globals["allocations"][str(new)][0]
            s.add_constraints(c.UGE(cap, used + additional))
        elif name == "copy":
            dst, src, count = map(dest, range(3))
            upper = s.globals.get("ht_ret") is not None
            out = s.globals["ht" if upper else "signature"]
            allowed = (
                [s.globals["layer"]] if upper else [s.globals["fors"], s.globals["ht"]]
            )
            require(src in allowed and dst >= out, "copy regions")
            expected = (
                self.layerlen
                if upper
                else self.forslen
                if src == s.globals["fors"]
                else self.htlen
            )
            require(count == expected, "copy source length")
            cap = s.globals["allocations"][str(out)][0]
            equal(s, c.ULE(dst - out + count, cap), True, "copy destination capacity")
            for i in range(0, count, 128):
                wrbytes(s, dst + i, load(s, src + i, min(count - i, 128)))
        elif name == "free":
            self.release(s, dest(0), x[1], dest(2))
        else:
            raise ValueError(name)
        clobber_scratch(s)

    def ht_return(self, s):
        require(s.globals["layer_event"] == 2 * self.d - 1, "incomplete hypertree")
        desc = s.globals["ht_out"]
        addr = s.globals["ht"]
        equal(s, unsigned(s, desc + 8), addr, "hypertree result pointer")
        equal(s, unsigned(s, desc + 16), self.htlen, "hypertree result length")
        equal(
            s,
            unsigned(s, desc),
            s.globals["allocations"][str(addr)][0],
            "hypertree result capacity",
        )
        self.check_chunks(s, addr, self.ht)
        s.globals["ht_ret"] = None

    def indices_return(self, s):
        desc = s.globals["base_out"]
        addr = s.globals["indices"]
        equal(s, unsigned(s, desc + 8), addr, "base conversion result pointer")
        equal(s, unsigned(s, desc + 16), self.k, "base conversion result length")
        cap = s.globals["allocations"][str(addr)][0]
        equal(s, unsigned(s, desc), cap, "base conversion result capacity")
        equal(s, load(s, addr, self.k * 4), self.idx, "all big-endian FORS digits")
        s.globals["base_ret"] = None

    def release(self, s, addr, cap, align):
        alloc = dict(s.globals["allocations"])
        expected, a, _ = alloc.pop(str(addr))
        equal(s, expected * a, cap, "deallocated capacity in bytes")
        require(align == a, "deallocated alignment")
        s.globals["allocations"] = alloc

    @staticmethod
    def check_chunks(s, addr, chunks):
        for off, val in chunks:
            equal(s, load(s, addr + off, val.size() // 8), val, "signature bytes")

    def finish(self, s):
        require(s.solver.satisfiable(), "infeasible terminal state")
        if self.api != "slh_sign_internal":
            rejected = not s.globals.get("framed", False)
            equal(s, c.UGT(self.ctxlen, 255), rejected, "wrong rejection branch")
            if rejected:
                equal(s, unsigned(s, RESULT), 2**64 - 1, "None discriminator")
                require(
                    not s.globals["calls"] and not s.globals["allocations"],
                    "work after rejection",
                )
                self.check_abi(s)
                self.rejections += 1
                return
        require(len(s.globals["calls"]) == len(self.schedule), "missing calls")
        out = s.globals["signature"]
        require(
            set(s.globals["allocations"]) == {str(out)},
            "incorrect final live allocations",
        )
        cap = s.globals["allocations"][str(out)][0]
        equal(s, unsigned(s, RESULT), cap, "returned capacity")
        equal(s, unsigned(s, RESULT + 8), out, "returned data pointer")
        equal(s, unsigned(s, RESULT + 16), self.total, "returned byte count")
        equal(s, load(s, out, self.n), self.r, "signature R")
        self.check_chunks(s, out + self.n, self.fors)
        self.check_chunks(s, out + self.n + self.forslen, self.ht)
        self.check_abi(s)
        self.final_paths += 1

    def check_abi(self, s):
        equal(s, s.regs.sp, STACK, "returned stack")
        for i, old in enumerate(s.globals["saved"], 19):
            equal(s, getattr(s.regs, f"x{i}"), old, "callee-saved register")
        equal(s, s.regs.x18, s.globals["platform"], "platform register")
        for i, old in enumerate(s.globals["vector_saved"], 8):
            equal(
                s, getattr(s.regs, f"q{i}")[63:0], old, "callee-saved vector register"
            )


def guard_access(s, kind, driver):
    if not s.globals.get("in_driver", False):
        return
    ptr = integer(s, getattr(s.inspect, f"mem_{kind}_address"))
    size = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
    ranges = [(STACK - 2048, 2048), (RESULT, 24)]
    if kind == "read":
        ranges += [(driver.param, 36), (KEY, 4 * driver.n), driver.constants_range]
    for start, length in ranges:
        if start <= ptr and ptr + size <= start + length:
            return
    for start, (capacity, alignment, _) in s.globals["allocations"].items():
        off = ptr - int(start)
        if int(start) != FRAMED and 0 <= off and off + size <= STRIDE:
            equal(
                s,
                c.ULE(off + size, capacity * alignment),
                True,
                "heap access within live allocation",
            )
            return
    raise ValueError(f"out-of-contract native {kind} at {ptr:#x} ({size} bytes)")


class Contract(angr.SimProcedure):
    def run(self, driver=None, label=None):
        driver.call(self.state, label)


def verify(path, image, n, v, api, hash_family="shake"):
    row, param, pc, end, hooks = objects(path, image, n, v, hash_family)
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    profile = f"{hash_family}_{8 * n}{v}"
    public, public_words = image.function(
        f"{len(profile)}{profile}{len(api)}{api}".encode(), b"6slhdsa4sets"
    )
    public_end = public + 4 * len(public_words)
    driver = Driver(row, param, api, hash_family)
    driver.constants_range = image.sections[b"__const"][:2]
    if driver.inline_seed:
        driver.inline_seed.install(
            project,
            pc,
            list(
                struct.unpack(
                    f"<{(end - pc) // 4}I", image.read(b"__text", pc, end - pc)
                )
            ),
        )
    base_pc, base_words = image.function(b"6slhdsa4util7base_2b", b"6slhdsa")
    base_end = base_pc + 4 * len(base_words)
    ht_pc, ht_words = image.function(
        f"2ht7ht_signKj{n:x}_EB6_".encode(), b"6slhdsa5shake"
    )
    ht_end = ht_pc + 4 * len(ht_words)
    for a, label in hooks.items():
        if label not in ("indices", "ht"):
            project.hook(a, Contract(driver=driver, label=label))
    s = project.factory.blank_state(
        addr=public,
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    driver.start(s)
    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}",
            when=angr.BP_BEFORE,
            action=lambda st, k=kind: guard_access(st, k, driver),
        )
    todo = [s]
    # Explore all satisfiable branches; no state merging or pruning by testcase.
    while todo:
        s = todo.pop()
        visits = s.globals.get("block_count", 0) + 1
        require(visits < 20000, "path did not terminate within block limit")
        s.globals["block_count"] = visits
        s.globals["in_driver"] = False
        if s.addr == s.globals.get("base_ret"):
            driver.indices_return(s)
        if s.addr == s.globals.get("ht_ret"):
            driver.ht_return(s)
        if hash_family == "shake" and s.addr == ht_pc:
            driver.call(s, "ht")
        if hash_family == "shake" and s.addr == base_pc:
            driver.call(s, "indices")
        native = (
            pc <= s.addr < end
            or public <= s.addr < public_end
            or (
                hash_family == "shake"
                and (base_pc <= s.addr < base_end or ht_pc <= s.addr < ht_end)
            )
        )
        s.globals["in_driver"] = native
        if s.addr == RETURN:
            driver.finish(s)
            continue
        require(s.addr in hooks or native, f"unmodeled exit {s.addr:#x}")
        # Include tails emitted by the linker only when explicitly modeled, and fail
        # on undecoded instructions, timeouts, unexpected jumps, and symbolic addresses.
        successors = project.factory.successors(s)
        require(not successors.unconstrained_successors, "unconstrained control flow")
        require(successors.flat_successors, "execution stopped before returning")
        todo.extend(successors.flat_successors)
    require(driver.final_paths == 4, "missing signature allocation case")
    require(
        driver.rejections == int(api != "slh_sign_internal"),
        "missing or duplicate rejection path",
    )
    print(
        f"{hash_family.upper()}-{n * 8}{v} {api}: {driver.final_paths} successful paths, {driver.rejections} rejection",
        flush=True,
    )


def mutation_tests(data, folder):
    # Change valid machine instructions, keeping the rest of the image unchanged.
    tests = [
        (
            b"3slh17slh_sign_internalKj10_EB6_",
            0x910043E1,
            0x910003E1,
            "absorb: buffer 1",
        ),
        (
            b"3slh17slh_sign_internalKj10_EB6_",
            0xAA0B21CB,
            0xAA0B1DCB,
            "FORS address field 0",
        ),
        (b"4util7base_2b", 0x2A1A217A, 0x2A1A1D7A, "all big-endian FORS digits"),
        (b"2ht7ht_signKj10_EB6_", 0x9AC826F7, 0x9AC822F7, "XMSS tree coordinate"),
        (
            b"3slh17slh_sign_internalKj10_EB6_",
            0xF9000A88,
            0xF9000A97,
            "returned byte count",
        ),
    ]
    original = Image(data)
    for suffix, old, new, expected in tests:
        family = b"6slhdsa4util" if b"4util" in suffix else b"6slhdsa5shake"
        pc, words = original.function(suffix, family)
        (i,) = [j for j, w in enumerate(words) if w == old]
        altered = bytearray(data)
        struct.pack_into("<I", altered, pc - original.base + 4 * i, new)
        path = folder / "altered"
        path.write_bytes(altered)
        try:
            verify(path, Image(altered), 16, "s", "sign")
        except ValueError as exc:
            require(expected in str(exc), f"wrong failure on mutation {old:#x}: {exc}")
        else:
            raise AssertionError(f"accepted modified instruction {old:#x}")
        print(f"Rejected {old:#010x} → {new:#010x} ({expected})", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument(
        "--set", choices=[f"{n}{v}" for n in (128, 192, 256) for v in "sf"]
    )
    apis = ("slh_sign_internal", "sign", "sign_deterministic", "slh_sign")
    parser.add_argument("--api", choices=apis)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--family", choices=["shake", "sha2"])
    args = parser.parse_args()
    if args.family == "sha2" and args.api not in (None, "slh_sign_internal"):
        parser.error("the SHA-2 driver gate covers slh_sign_internal")
    logging.getLogger("angr").setLevel(logging.ERROR)
    data = args.binary.read_bytes()
    with tempfile.TemporaryDirectory() as folder:
        snapshot = Path(folder) / "linked"
        snapshot.write_bytes(data)
        for n in (16, 24, 32):
            for v in "sf":
                if args.set is None or args.set == f"{8 * n}{v}":
                    for family in (args.family,) if args.family else ("shake", "sha2"):
                        supported = (
                            apis if family == "shake" else ("slh_sign_internal",)
                        )
                        for api in supported:
                            if args.api is None or args.api == api:
                                verify(snapshot, Image(data), n, v, api, family)
        if args.self_test:
            mutation_tests(data, Path(folder))
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
