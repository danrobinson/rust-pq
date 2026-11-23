# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Verify linked fixed-size keygen from the consumer's entry to finished key buffers."""

import argparse
import hashlib
import struct
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
from driver import (
    Image,
    Driver,
    STACK,
    KEY,
    RESULT,
    RETURN,
    angr,
    c,
    objects,
    clobber_scratch,
    blob,
    equal,
    integer,
    load,
    require,
    unsigned,
    wrbytes,
)

PK = RESULT + 256


def verify(path, image, n, variant, family):
    row, param, *_ = objects(path, image, n, variant, family)
    shake = family == "shake"
    mono = f"Kj{n:x}_EB{6 if shake else 4}_".encode()
    crate = b"6slhdsa5shake" if shake else b"6slhdsa"
    label = f"{family}_{n * 8}{variant}"
    public = image.function(f"{len(label)}{label}6keygen".encode(), b"6slhdsa4sets")

    def body(name):
        return image.function(crate + name + mono, crate)

    api = body(b"3api6keygen")
    inner = body(b"3slh19slh_keygen_internal")
    root, _ = body(b"4xmss9xmss_node")
    seedpc = body(b"4hash8seed_ctx")[0] if not shake and n > 16 else None
    model = Driver(row, param, "slh_sign_internal", family)
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    if model.inline_seed:
        model.inline_seed.install(project, *inner)
    st = project.factory.blank_state(
        addr=public[0],
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    model.start(st)
    st.regs.x0, st.regs.x1, st.regs.x2 = KEY, RESULT, PK
    value = blob("XMSS_root", n)

    def access(s, kind):
        if not s.globals.get("native", False):
            return
        ptr = integer(s, getattr(s.inspect, f"mem_{kind}_address"))
        size = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
        regions = [(STACK - 2048, 2048), (RESULT, 4 * n), (PK, 2 * n)]
        if kind == "read":
            regions.extend([(KEY, 3 * n), (param, 36), image.sections[b"__const"][:2]])
        require(
            any(a <= ptr and ptr + size <= a + length for a, length in regions),
            "out-of-bounds keygen " + kind,
        )

    for kind in ("read", "write"):
        st.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda s, k=kind: access(s, k)
        )
    todo = [(st, (), 0)]
    completed = 0
    while todo:
        s, trace, steps = todo.pop()
        require(steps < 500, "keygen execution bound")
        s.globals["native"] = False
        if s.addr == RETURN:
            require(
                trace == (("seed", "root") if seedpc else ("root",)),
                "missing keygen call",
            )
            equal(
                s,
                load(s, RESULT, 4 * n),
                c.Concat(*model.sk[:3], value),
                "serialized secret key",
            )
            equal(
                s,
                load(s, PK, 2 * n),
                c.Concat(model.sk[2], value),
                "serialized public key",
            )
            require(s.solver.satisfiable(), "infeasible keygen return")
            model.check_abi(s)
            completed += 1
            continue
        x = [getattr(s.regs, f"x{i}") for i in range(9)]
        if s.addr in (root, seedpc):
            if s.addr == root:
                equal(s, load(s, x[0], n), model.sk[0], "XMSS keygen secret seed")
                equal(s, x[1], 0, "XMSS top index")
                equal(s, x[2], model.hp, "XMSS tree height")
                seed = model.sk[2] if shake else model.seed
                equal(
                    s,
                    load(s, x[3], seed.size() // 8),
                    seed,
                    "XMSS keygen public seed context",
                )
                adrs = integer(s, x[4])
                equal(s, unsigned(s, adrs), 0, "XMSS keygen tree")
                equal(s, unsigned(s, adrs + 8, 4), model.d - 1, "XMSS top layer")
                equal(
                    s, load(s, adrs + 12, 16), 0, "remaining XMSS keygen address fields"
                )
                out, event = value, "root"
            else:
                equal(s, load(s, x[0], n), model.sk[2], "keygen seed context input")
                out, event = model.seed, "seed"
            wrbytes(s, model.workspace(s, x[8], out.size() // 8), out)
            clobber_scratch(s)
            s.regs.pc = s.regs.lr
            todo.append((s, (*trace, event), steps + 1))
            continue
        require(
            any(
                start <= s.addr < start + 4 * len(words)
                for start, words in [public, api, inner]
            ),
            "unexpected keygen control flow",
        )
        s.globals["native"] = True
        nxt = project.factory.successors(s)
        require(
            nxt.flat_successors and not nxt.unconstrained_successors,
            "unresolved keygen control flow",
        )
        todo.extend((child, trace, steps + 1) for child in nxt.flat_successors)
    require(completed == 1, "missing or duplicate keygen return")
    print(f"{label} keygen: both complete output keys and ABI checked", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    image = Image(data)
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "consumer"
        path.write_bytes(data)
        for family in ("sha2", "shake"):
            for n in (16, 24, 32):
                for variant in "sf":
                    verify(path, image, n, variant, family)
        if args.self_test:
            pc, words = image.function(
                b"3slh19slh_keygen_internalKj10_EB6_", b"6slhdsa5shake"
            )
            for old, new, expected in [
                (0x51000508, 0x51000108, "XMSS top layer"),
                (0x3D8006A0, 0x3D8002A0, "serialized public key"),
            ]:
                (i,) = [j for j, word in enumerate(words) if word == old]
                altered = bytearray(data)
                struct.pack_into("<I", altered, pc - image.base + 4 * i, new)
                path.write_bytes(altered)
                try:
                    verify(path, Image(altered), 16, "s", "shake")
                except ValueError as ex:
                    require(expected in str(ex), f"unexpected failure: {ex}")
                else:
                    raise AssertionError("accepted modified keygen")
                print(f"Rejected keygen mutation {old:#010x} ({expected})")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
