# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Verify linked internal signature verification, including length rejection and root comparison."""

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
    KEY,
    MESSAGE,
    CONTEXT,
    RETURN,
    RESULT,
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
    guard_access,
)

SIGNATURE = 0x21000000


def verify(path, image, n, variant, family, entry="slh_verify_internal"):
    row, param, _, _, hooks = objects(path, image, n, variant, family)
    shake = family == "shake"
    mono = f"Kj{n:x}_EB{6 if shake else 4}_".encode()
    crate = b"6slhdsa5shake" if shake else b"6slhdsa"
    label = f"{family}_{n * 8}{variant}"
    public = image.function(
        f"{len(label)}{label}{len(entry)}{entry}".encode(), b"6slhdsa4sets"
    )

    def body(name):
        return image.function(crate + name + mono, crate)

    inner = body(b"3slh19slh_verify_internal")
    extents = [public, inner]
    contextual = entry != "slh_verify_internal"
    segmented = None
    if contextual and not shake:
        extents.append(body(b"3slh10slh_verify"))
        prefix = b"6slhdsa3slh7message"
        suffix = f"Kj{n:x}_EB6_".encode()
        segmented = image.function(prefix + b"6verify" + suffix, prefix)
        extents.append(segmented)
        hooks[image.function(prefix + b"6digest" + suffix, prefix)[0]] = (
            "segmented_digest"
        )
    if n != 16:
        extents.append(body(b"2ht9ht_verify"))
    base = image.function(b"6slhdsa4util7base_2b", b"6slhdsa")
    if shake:
        extents.append(base)
    xmss, _ = body(b"4xmss16xmss_pk_from_sig")
    hooks[xmss] = "verify_layer"
    model = Driver(row, param, entry if contextual else "slh_sign_internal", family)
    model.constants_range = image.sections[b"__const"][:2]
    project = angr.load_shellcode(
        bytes(image.data), arch="aarch64", load_address=image.base
    )
    if model.inline_seed:
        model.inline_seed.install(project, *inner)
        if segmented:
            model.inline_seed.install(project, *segmented)
    s = project.factory.blank_state(
        addr=public[0],
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
        },
    )
    model.start(s)
    siglen = c.BVS("signature_length", 64)
    s.add_constraints(c.ULE(siglen, 2**63 - 1))
    s.regs.x0, s.regs.x1, s.regs.x2, s.regs.x3, s.regs.x4 = (
        MESSAGE,
        model.msglen,
        SIGNATURE,
        siglen,
        KEY,
    )
    if contextual:
        s.regs.x4, s.regs.x5, s.regs.x6 = CONTEXT, model.ctxlen, KEY
    wrbytes(s, KEY, c.Concat(model.sk[2], model.sk[3]))
    wrbytes(s, SIGNATURE, model.r)
    roots = [model.pkfors] + [blob("recovered_layer", n) for j in range(model.d)]
    model.schedule = ("hmsg",) + (
        ("indices",) if shake else ("seed",) if n > 16 else ()
    )

    def access(st, kind):
        if not st.globals.get("in_driver", False):
            return
        ptr = integer(st, getattr(st.inspect, f"mem_{kind}_address"))
        size = integer(st, getattr(st.inspect, f"mem_{kind}_length"))
        if SIGNATURE <= ptr < SIGNATURE + model.total:
            require(kind == "read", "modified input signature")
            equal(
                st,
                c.ULE(ptr - SIGNATURE + size, siglen),
                True,
                "signature read out of bounds",
            )
            return
        if KEY <= ptr < KEY + 4 * n:
            require(kind == "read" and ptr + size <= KEY + 2 * n, "public key access")
            return
        require(
            not (RESULT <= ptr < RESULT + 24),
            "unexpected verifier result-buffer access",
        )
        guard_access(st, kind, model)

    for kind in ("read", "write"):
        s.inspect.b(
            f"mem_{kind}", when=angr.BP_BEFORE, action=lambda st, k=kind: access(st, k)
        )
    todo = [(s, 0, False, 0)]
    terminals = []
    while todo:
        st, layer, recovered, steps = todo.pop()
        require(steps < 2000, "verification execution bound")
        pc = st.addr
        st.globals["in_driver"] = False
        if pc == st.globals.get("base_ret"):
            model.indices_return(st)
        if segmented and pc == segmented[0]:
            st.globals["segmented"] = True
        if pc == RETURN:
            valid = c.ULE(model.ctxlen, 255) if contextual else c.BoolV(True)
            long = (
                c.And(valid, c.UGE(model.msglen, 1024)) if segmented else c.BoolV(False)
            )
            equal(st, long, st.globals.get("segmented", False), "segmented dispatch")
            if contextual:
                equal(
                    st,
                    c.And(valid, c.Not(long)),
                    st.globals.get("framed", False),
                    "verification context framing",
                )
            equal(
                st,
                c.And(valid, siglen == model.total),
                recovered,
                "signature length branch",
            )
            require(
                layer == (model.d if recovered else 0)
                and not st.globals["allocations"],
                "incomplete verification",
            )
            require(
                st.globals["calls"] == (model.schedule if recovered else ()),
                "incorrect verification call trace",
            )
            verdict = (
                c.If(roots[-1] == model.sk[3], c.BVV(1, 32), c.BVV(0, 32))
                if recovered
                else 0
            )
            equal(st, st.regs.w0, verdict, "verification verdict")
            model.check_abi(st)
            require(st.solver.satisfiable(), "infeasible verification return")
            terminals.append(recovered)
            continue
        name = hooks.get(pc)
        x = [getattr(st.regs, f"x{i}") for i in range(9)]

        def reg(i, val):
            equal(st, x[i], val, f"{name}: x{i}")

        def buf(i, val):
            equal(st, load(st, x[i], val.size() // 8), val, f"{name}: buffer {i}")

        if name == "segmented_digest":
            require(
                not st.globals["calls"] and st.globals.get("segmented"),
                "unexpected segmented digest",
            )
            reg(1, model.m)
            buf(2, model.r)
            buf(3, model.sk[2])
            buf(4, model.sk[3])
            reg(5, CONTEXT)
            reg(6, model.ctxlen)
            reg(7, MESSAGE)
            equal(
                st, unsigned(st, st.regs.sp), model.msglen, "segmented message length"
            )
            model.vec(st, integer(st, x[0]), "digest", model.m, 1, [(0, model.digest)])
            st.globals["calls"] = ("hmsg",)
            clobber_scratch(st)
        elif name in ("hmsg", "seed", "free", "grow", "frame"):
            model.call(st, name)
        elif name in ("recover", "sha_recover"):
            require(
                not recovered and st.globals["calls"] == model.schedule,
                "unexpected FORS recovery",
            )
            reg(0, param)
            if shake:
                reg(1, st.globals["indices"])
                buf(1, model.idx)
                reg(2, model.k)
                reg(3, SIGNATURE + n)
                reg(4, model.forslen)
                buf(5, model.sk[2])
            else:
                reg(1, SIGNATURE + n)
                reg(2, model.forslen)
                buf(3, model.digest.get_bytes(0, model.md))
                reg(4, model.md)
                buf(5, model.seed)
            model.check_address(st, integer(st, x[6]))
            wrbytes(st, model.workspace(st, x[8], n), model.pkfors)
            clobber_scratch(st)
            recovered = True
        elif name == "verify_layer":
            require(recovered and layer < model.d, "extra or early verification layer")
            offset = 0 if shake else 1
            reg(offset, param if shake else model.hp)
            tree = c.LShR(model.tree, layer * model.hp)
            leaf = (
                model.leaf
                if layer == 0
                else c.LShR(model.tree, (layer - 1) * model.hp) & ((1 << model.hp) - 1)
            )
            reg(offset + 1, leaf)
            reg(offset + 2, SIGNATURE + n + model.forslen + layer * model.layerlen)
            reg(offset + 3, model.layerlen)
            buf(offset + 4, roots[layer])
            buf(offset + 5, model.sk[2] if shake else model.seed)
            adrs = integer(st, x[offset + 6])
            equal(st, unsigned(st, adrs), tree, "verification subtree")
            equal(st, unsigned(st, adrs + 8, 4), layer, "verification layer")
            equal(st, load(st, adrs + 12, 16), 0, "remaining verification address")
            layer += 1
            wrbytes(st, model.workspace(st, x[8 if shake else 0], n), roots[layer])
            clobber_scratch(st)
        else:
            if name == "indices":
                model.call(st, name)
            require(
                any(start <= pc < start + 4 * len(words) for start, words in extents),
                f"unexpected verifier exit {pc:#x}",
            )
            st.globals["in_driver"] = True
            nxt = project.factory.successors(st)
            require(
                nxt.flat_successors and not nxt.unconstrained_successors,
                "unresolved verification control flow",
            )
            todo.extend(
                (child, layer, recovered, steps + 1) for child in nxt.flat_successors
            )
            continue
        st.regs.pc = st.regs.lr
        todo.append((st, layer, recovered, steps + 1))
    expected_terminals = (
        [False, True]
        + ([False] if contextual else [])
        + ([False, True] if segmented else [])
    )
    require(
        sorted(terminals) == sorted(expected_terminals), "missing verification case"
    )
    print(
        f"{label} {entry}: invalid length and complete verification through root comparison",
        flush=True,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    data = args.binary.read_bytes()
    with tempfile.TemporaryDirectory() as folder:
        path = Path(folder) / "consumer"
        path.write_bytes(data)
        image = Image(data)
        for family in ("shake", "sha2"):
            for n in (16, 24, 32):
                for variant in "sf":
                    for entry in ("slh_verify_internal", "verify", "slh_verify"):
                        verify(path, image, n, variant, family, entry)
        if args.self_test:
            pc, words = image.function(
                b"3slh19slh_verify_internalKj10_EB6_", b"6slhdsa5shake"
            )
            (i,) = [j for j, word in enumerate(words) if word == 0x1A9F17E0]
            altered = bytearray(data)
            struct.pack_into("<I", altered, pc - image.base + 4 * i, 0x1A9F07E0)
            path.write_bytes(altered)
            try:
                verify(path, Image(altered), 16, "s", "shake")
            except ValueError as ex:
                require("verification verdict" in str(ex), f"unexpected failure: {ex}")
            else:
                raise AssertionError("accepted inverted verdict")
            print("Rejected inverted final verification verdict")
    print("Mach-O SHA-256", hashlib.sha256(data).hexdigest())
