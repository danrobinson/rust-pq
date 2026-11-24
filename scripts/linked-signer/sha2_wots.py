# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Prove the linked Apple SHA2 WOTS drivers against the batched SHA256 chain contract."""

import argparse
import hashlib
import struct
import tempfile
import sys
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    Image,
    STACK,
    RETURN,
    KEY,
    RESULT,
    Driver,
    angr,
    c,
    blob,
    integer,
    load,
    unsigned,
    put,
    wrbytes,
    require,
    objects,
)
from wots_chains import ImageEnv, agrees, return_call
from signer_inventory import import_stubs
import arm_vector_ir

SEED, ADDRESS, MESSAGE, SIG, DIGITS, OUT = (
    KEY + 0x10000 * i for i in (4, 5, 6, 7, 8, 9)
)


def verify(path, image, n, mode, *, move_allocations=True):
    env = ImageEnv(path, image, n)
    row, param, _, _, hooks = objects(path, image, n, "s", "sha2")
    model = Driver(row, param, "slh_sign_internal", "sha2")
    suffix = f"Kj{n:x}_EB4_".encode()

    def fn(stem):
        return env.fun(stem + suffix, b"6slhdsa")

    pc, end = fn(
        {
            "sign": b"4wots9wots_sign",
            "keygen": b"4wots11wots_pk_gen",
            "recover": b"4wots16wots_pk_from_sig",
        }[mode]
    )
    secret = fn(b"4wots9sk_blocks")
    chain, _ = fn(b"4hash12chain_blocks")
    digits, _ = fn(b"4wots11wots_digits")
    final, _ = fn(b"4hash12thash_values")
    (zero,) = [a for a, name in import_stubs(image, path).items() if name == "_bzero"]
    s = env.blank(pc)
    model.start(s)
    count = 2 * n + 3
    tree, layer, keypair, old2, old3 = [
        c.BVS(name, bits)
        for name, bits in [
            ("tree", 64),
            ("layer", 32),
            ("keypair", 32),
            ("old_address_word2", 32),
            ("old_address_word3", 32),
        ]
    ]
    # The XMSS caller supplies WOTS_HASH. Both remaining words are arbitrary here.
    for off, val, size in [
        (0, tree, 8),
        (8, layer, 4),
        (12, 0, 4),
        (16, keypair, 4),
        (20, old2, 4),
        (24, old3, 4),
    ]:
        put(s, ADDRESS + off, val, size)
    sk, msg, seed = blob("secret", n), blob("message", n), blob("seed_context", 96 + n)
    wrbytes(s, KEY, sk)
    wrbytes(s, SEED, seed)
    wrbytes(s, MESSAGE, msg)
    sig = [blob("input_signature_block", n) for _ in range(count)]
    for i, v in enumerate(sig):
        wrbytes(s, SIG + i * n, v)
    length = c.BVS("full_signature_slice_length", 64)
    s.add_constraints(c.UGE(length, count * n), c.ULE(length, (1 << 63) - 1))
    args = {
        "sign": [MESSAGE, KEY, SEED, ADDRESS],
        "keygen": [KEY, SEED, ADDRESS],
        "recover": [SIG, length, MESSAGE, SEED, ADDRESS],
    }[mode]
    for i, val in enumerate(args):
        setattr(s.regs, f"x{i}", val)
    ds = [c.BVS("digit", 4).zero_extend(28) for _ in range(count)]
    cap = c.BVS("digit_capacity", 64)
    s.add_constraints(c.UGE(cap, count), c.ULE(cap, ((1 << 63) - 1) // 4))
    secrets = [blob("chain_secret", n) for _ in range(count)]
    ends = [blob("chain_result", n) for _ in range(count)]
    root = blob("public_key", n)
    prefix = c.Concat(layer[7:0], tree)

    def block(i, domain, roundnum, val):
        return c.Concat(
            prefix,
            c.BVV(domain, 8),
            keypair,
            c.BVV(i, 32),
            roundnum,
            val,
            c.BVV(b"\x80" + bytes(39 - n) + ((86 + n) * 8).to_bytes(2, "big")),
        )

    def access(st, kind):
        if not st.globals.get("native", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        ranges = [(STACK - 12288, 12288), (RESULT, 24 if mode == "sign" else n)]
        if st.globals.get("out_capacity", 0):
            ranges.append((st.globals["out_pointer"], st.globals["out_capacity"]))
        if kind == "read":
            ranges.extend([(SEED, 96 + n), (ADDRESS, 32), env.const])
            if mode != "recover":
                ranges.append((KEY, n))
            if mode != "keygen":
                ranges.append((MESSAGE, n))
            if mode == "recover":
                ranges.append((SIG, count * n))
            if st.globals.get("digits_live"):
                ranges.append((DIGITS, count * 4))
        require(
            any(a <= ptr and ptr + size <= a + l for a, l in ranges),
            f"WOTS {kind} extent {ptr:#x}+{size}",
        )

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )
    schedule = {
        "keygen": ["prf", "chains", "root"],
        "sign": ["digits", "prf", "chains", "free"],
        "recover": ["digits", "chains", "root", "free"],
    }[mode]
    event = 0
    steps = 0
    while s.addr != RETURN:
        steps += 1
        require(steps < 4000, "WOTS execution bound")
        s.globals["native"] = False
        x = [getattr(s.regs, f"x{i}") for i in range(9)]

        def reg(i, val):
            agrees(s, x[i], val, f"WOTS x{i} argument")

        def frame(ptr, width):
            a = integer(s, ptr)
            require(integer(s, s.regs.sp) <= a <= STACK - width, "WOTS stack extent")
            return a

        def consume(name):
            nonlocal event
            require(
                event < len(schedule) and schedule[event] == name,
                "WOTS " + name + " order",
            )
            event += 1

        if s.addr == digits:
            consume("digits")
            reg(0, MESSAGE)
            desc = frame(x[8], 24)
            for off, val in [(0, cap), (8, DIGITS), (16, count)]:
                put(s, desc + off, val, 8)
            for i, v in enumerate(ds):
                put(s, DIGITS + 4 * i, v, 4)
            s.globals["digits_live"] = True
        elif s.addr == chain:
            prf = schedule[event] == "prf"
            consume("prf" if prf else "chains")
            reg(0, SEED + (96 if n == 32 else 64))
            reg(2, count)
            buf = frame(x[1], count * 64)
            for side, ptr_i in [("start", 3), ("end", 5)]:
                variable = not prf and (
                    (side == "start" and mode == "recover")
                    or (side == "end" and mode == "sign")
                )
                reg(ptr_i + 1, count if variable else 67)
                p = integer(s, x[ptr_i])
                if variable:
                    reg(ptr_i, DIGITS)
                else:
                    start, size = env.const
                    require(
                        start <= p <= start + size - 67 * 4,
                        "constant chain bounds array",
                    )
                for i in range(count):
                    wanted = (
                        ds[i]
                        if variable
                        else (0 if side == "start" else (1 if prf else 15))
                    )
                    agrees(s, unsigned(s, p + 4 * i, 4), wanted, "WOTS chain bound")
            for i in range(count):
                # Each round overwrites the hash address before compressing. Empty
                # chains retain their incoming round and their incoming value.
                ri = old3 if mode == "recover" else c.BVV(0, 32)
                val = sk if prf else (sig[i] if mode == "recover" else secrets[i])
                want = block(i, 5 if prf else 0, ri, val)
                agrees(
                    s,
                    load(s, buf + 64 * i, 64),
                    want,
                    "WOTS complete padded chain input",
                )
                if prf:
                    result = secrets[i]
                elif mode == "sign":
                    result = c.If(ds[i] == 0, secrets[i], ends[i])
                elif mode == "recover":
                    result = c.If(ds[i] == 15, sig[i], ends[i])
                else:
                    result = ends[i]
                wrbytes(s, buf + 64 * i + 22, result)
                if not prf:
                    last = ds[i] - 1 if mode == "sign" else c.BVV(14, 32)
                    empty = (
                        (ds[i] == 0 if mode == "sign" else ds[i] == 15)
                        if mode != "keygen"
                        else c.BoolV(False)
                    )
                    wrbytes(s, buf + 64 * i + 18, c.If(empty, ri, last))
        elif s.addr == final:
            consume("root")
            reg(0, SEED)
            reg(3, count)
            reg(8, RESULT)
            ad = frame(x[1], 28)
            for off, val, size in [
                (0, tree, 8),
                (8, layer, 4),
                (12, 1, 4),
                (16, keypair, 4),
                (20, 0, 8),
            ]:
                agrees(s, unsigned(s, ad + off, size), val, "WOTS public-key address")
            buf = frame(x[2], count * 64)
            for i in range(count):
                v = ends[i] if mode == "keygen" else c.If(ds[i] == 15, sig[i], ends[i])
                agrees(
                    s, load(s, buf + 64 * i + 22, n), v, "WOTS ordered key hash input"
                )
            wrbytes(s, RESULT, root)
        elif s.addr == zero:
            reg(1, 67 * 64)
            wrbytes(s, frame(x[0], 67 * 64), c.BVV(0, 67 * 64 * 8))
        elif hooks.get(s.addr) == "copy":
            reg(2, 67 * 64)
            dst, src = [frame(p, 67 * 64) for p in x[:2]]
            require(
                dst + 67 * 64 <= src or src + 67 * 64 <= dst, "overlapping WOTS blocks"
            )
            for i in range(67):
                wrbytes(s, dst + 64 * i, load(s, src + 64 * i, 64))
            return_call(s, dst)
            continue
        elif hooks.get(s.addr) == "free":
            consume("free")
            reg(0, DIGITS)
            reg(1, cap * 4)
            reg(2, 4)
            s.globals["digits_live"] = False
        elif hooks.get(s.addr) == "reserve":
            desc = frame(x[0], 24)
            used = integer(s, x[1])
            reg(2, n)
            reg(3, 1)
            reg(4, 1)
            old = s.globals.get("out_capacity", 0)
            agrees(s, unsigned(s, desc), old, "old signature capacity")
            agrees(
                s,
                unsigned(s, desc + 8),
                s.globals.get("out_pointer", 1),
                "signature allocation identity",
            )
            agrees(s, unsigned(s, desc + 16), used, "reserve live bytes")
            require(0 <= used <= old < used + n <= count * n, "reserve size")
            new = max(2 * old, used + n, 8)
            put(s, desc, new, 8)
            previous = s.globals.get("out_pointer", OUT)
            dest = previous + 8192 if old and move_allocations else previous
            if old and dest != previous:
                wrbytes(s, dest, load(s, previous, used))
            put(s, desc + 8, dest, 8)
            s.globals["out_pointer"] = dest
            s.globals["out_capacity"] = new
        else:
            require(
                pc <= s.addr < end or secret[0] <= s.addr < secret[1],
                f"unexpected native WOTS exit {s.addr:#x}",
            )
            s.globals["native"] = True
            nx = env.project.factory.successors(s)
            require(
                not nx.unconstrained_successors and len(nx.flat_successors) == 1,
                "unresolved native WOTS branch",
            )
            s = nx.flat_successors[0]
            continue
        return_call(s)
    s.globals["native"] = False
    require(
        event == len(schedule)
        and s.solver.satisfiable()
        and not s.globals.get("digits_live"),
        "WOTS return",
    )
    if mode == "sign":
        pointer = s.globals["out_pointer"]
        for off, val in [(0, s.globals["out_capacity"]), (8, pointer), (16, n * count)]:
            agrees(s, unsigned(s, RESULT + off), val, "returned signature Vec")
        for i in range(count):
            agrees(
                s,
                load(s, pointer + i * n, n),
                c.If(ds[i] == 0, secrets[i], ends[i]),
                "signature chain bytes",
            )
    else:
        agrees(s, load(s, RESULT, n), root, "returned WOTS public key")
    model.check_abi(s)
    print(f"SHA2-{8 * n} WOTS {mode}: {steps} linked basic blocks", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--width", type=int, choices=(16, 24, 32))
    parser.add_argument("--mode", choices=("sign", "keygen", "recover"))
    args = parser.parse_args()
    data = args.executable.read_bytes()
    image = Image(data)
    for n in [args.width] if args.width else (16, 24, 32):
        for mode in [args.mode] if args.mode else ("keygen", "sign", "recover"):
            verify(args.executable, image, n, mode)
            if mode == "sign":
                verify(args.executable, image, n, mode, move_allocations=False)

    if args.self_test:
        tests = [
            (
                b"4wots9sk_blocks",
                0x528000AA,
                0x5280008A,
                "keygen",
                "complete padded chain input",
            ),
            (
                b"4wots11wots_pk_gen",
                0x52800029,
                0x52800049,
                "keygen",
                "public-key address",
            ),
            (
                b"4wots9wots_sign",
                0x3CF56AC0,
                0x3CF56AC1,
                "sign",
                "signature chain bytes",
            ),
            (
                b"4wots16wots_pk_from_sig",
                0x39004588,
                0x3900459F,
                "recover",
                "complete padded chain input",
            ),
        ]
        with tempfile.TemporaryDirectory() as folder:
            altered_path = Path(folder) / "consumer"
            for fn, old, new, mode, witness in tests:
                pc, words = image.function(fn + b"Kj10_EB4_", b"6slhdsa")
                (index,) = [i for i, w in enumerate(words) if w == old]
                altered = bytearray(data)
                struct.pack_into("<I", altered, pc - image.base + 4 * index, new)
                altered_path.write_bytes(altered)
                try:
                    verify(altered_path, Image(altered), 16, mode)
                except ValueError as exc:
                    require(witness in str(exc), f"unexpected mutation failure: {exc}")
                else:
                    raise AssertionError("accepted altered WOTS driver")
        print("Rejected four SHA2 WOTS driver mutations")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
