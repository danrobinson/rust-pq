"""Check the initialization, refill and return edges in the native SHA256 chain scheduler."""

import sys

sys.dont_write_bytecode = True
from driver import (
    STACK,
    KEY,
    RETURN,
    c,
    angr,
    put,
    load,
    wrbytes,
    integer,
    blob,
    require,
)
from sha2_chain_context import (
    CUTS,
    ENTRY,
    persistent,
    set_context,
    activate,
    check_context,
)
from sha2_chain_episode import pack
from sha2_chain import BLOCKS, START, END
from wots_chains import ImageEnv, agrees, return_call
from signer_inventory import import_stubs
from segmented import Compression


def verify(path, image, n, *, fors=False):
    env = ImageEnv(path, image, n)
    pc, words = image.function(
        b"4hash12chain_blocks" + f"Kj{n:x}_EB4_".encode(), b"6slhdsa"
    )
    entry = pc + ENTRY[n]
    dispatch, refill = [pc + x for x in CUTS[n]]
    (zero,) = [a for a, name in import_stubs(image, path).items() if name == "_bzero"]
    h = [c.BVS("arbitrary_seed_word", 32) for _ in range(8)]
    hash = Compression(16, None)
    count = c.BVS("num_blocks", 64)
    avail = [c.BVS("bounds_slice_length", 64) for _ in range(2)]
    st = env.blank(pc)
    st.add_constraints(c.ULE(count, 128 if fors else 67))
    for length in avail:
        st.add_constraints(c.ULE(count, length), c.ULE(length, ((1 << 63) - 1) // 4))
    for i, v in enumerate([KEY, BLOCKS, count, START, avail[0], END, avail[1]]):
        setattr(st.regs, f"x{i}", v)
    for i, v in enumerate(h):
        put(st, KEY + 4 * i, v, 4)
    preserved = [getattr(st.regs, f"x{i}") for i in range(18, 30)]
    vectors = [getattr(st.regs, f"q{i}")[63:0] for i in range(8, 16)]

    def guard_init(s, kind):
        if not s.globals.get("init", False):
            return
        p = integer(s, getattr(s.inspect, f"mem_{kind}_address"))
        size = integer(s, getattr(s.inspect, f"mem_{kind}_length"))
        allowed = [(STACK - 2048, 2048)]
        if kind == "read":
            allowed.extend([env.const, (KEY, 32)])
        require(
            any(a <= p and p + size <= a + l for a, l in allowed), "prologue access"
        )

    for k in ("read", "write"):
        st.inspect.b(
            f"mem_{k}", when=angr.BP_BEFORE, action=lambda s, k=k: guard_init(s, k)
        )
    used = 0
    while st.addr != entry:
        used += 1
        require(used < 50, "prologue bound")
        if st.addr == zero:
            st.globals["init"] = False
            ptr, width = integer(st, st.regs.x0), integer(st, st.regs.x1)
            require(
                integer(st, st.regs.sp) <= ptr <= STACK - width and width == 640,
                "zero slots",
            )
            wrbytes(st, ptr, c.BVV(0, 8 * width))
            return_call(st)
        else:
            require(pc <= st.addr < entry, "unexpected SHA scheduler prologue exit")
            st.globals["init"] = True
            ns = env.project.factory.successors(st, extra_stop_points={entry})
            require(
                len(ns.flat_successors) == 1 and not ns.unconstrained_successors,
                "prologue transfer",
            )
            st = ns.flat_successors[0]
    st.globals["init"] = False
    sp = integer(st, st.regs.sp)
    base = integer(st, st.regs.x24)
    root = persistent(st, n)
    for reg, v in [
        (8, 0),
        (13, 0),
        (11 if n == 32 else 12, 0),
        (19, count),
        (20, END),
        (21, START),
        (22, BLOCKS),
        (23, KEY),
    ]:
        agrees(st, getattr(st.regs, f"x{reg}"), v, "initial scheduler context")
    # A core-window certificate uses a shorter array to derive exactly this
    # invariant. Only the designated count register may depend on its length.
    lengths = set().union(*(v.variables for v in [count, *avail]))
    for bank, items in enumerate(root):
        for field, val in items:
            if bank != 0 or field != 19:
                require(
                    not lengths.intersection(val.variables),
                    "undeclared length-dependent machine context",
                )
    saved = load(st, STACK - 0x90, 0x90)
    head = blob("WOTS_address_prefix", 16)
    block = c.Concat(head, blob("remaining_block_bytes", 48))
    if fors:
        a = c.BVS("FORS_tree_index", 20).zero_extend(12)
        b = a + 1
    else:
        a, b = [c.BVS(i, 4).zero_extend(28) for i in ("start", "end")]
    ix = c.BVS("next_unread_lane", 64)
    packed = pack(hash, h, block, n, ix, a, b)
    hot = activate(
        root,
        n,
        head,
        packed.get_bytes(112, 16).reversed,
        packed.get_bytes(128, 16).reversed,
    )
    hash.hooks(env.project, path, pc, words)

    def context(cached, cursor):
        scal, vec, stack = hot if cached else root
        return ([(j, cursor if j == 8 else val) for j, val in scal], vec, stack)

    # An empty fresh slot never requires the earlier, unused bytes of its storage.
    arbitrary = [blob("old_active_record", 160) for _ in range(4)]

    def check_edge(where, num, cached):
        s = env.blank(where)
        s.add_constraints(
            *st.solver.constraints, c.ULE(num, ix), c.ULE(ix, count), c.ULE(a, b)
        )
        s.regs.sp = sp
        set_context(s, *context(cached, ix))
        setattr(s.regs, "x13" if where == entry else "x14", num)
        for j in range(num):
            wrbytes(s, base + j * 160, arbitrary[j])
        for j, v in enumerate(h):
            put(s, KEY + j * 4, v, 4)
        wrbytes(s, BLOCKS, block)
        put(s, START, a, 4)
        put(s, END, b, 4)

        def guard(t, kind):
            if not t.globals.get("native", False):
                return
            expr = getattr(t.inspect, f"mem_{kind}_address")
            size = integer(t, getattr(t.inspect, f"mem_{kind}_length"))
            if expr.symbolic:
                require(kind == "read", "unexpected indexed write while filling")
                for address, delta, length in [
                    (START, 4, 4),
                    (END, 4, 4),
                    (BLOCKS, 64, 64),
                ]:
                    off = c.simplify(expr - (address + delta * ix))
                    candidates = t.solver.eval_upto(off, 2)
                    if len(candidates) == 1 and 0 <= candidates[0] <= length - size:
                        agrees(
                            t, c.ULT(ix, count), True, "fill input index is in range"
                        )
                        setattr(t.inspect, "mem_read_address", address + candidates[0])
                        return
                raise ValueError(f"unmatched refill memory address {expr}")
            ptr = integer(t, expr)
            allowed = [(sp, STACK - 0x90 - sp)]
            if kind == "read":
                allowed.extend([env.const, (KEY, 32)])
            require(
                any(x <= ptr and ptr + size <= x + l for x, l in allowed),
                f"refill memory bounds {ptr:#x}",
            )

        for kind in ("read", "write"):
            s.inspect.b(
                f"mem_{kind}", when=angr.BP_BEFORE, action=lambda t, k=kind: guard(t, k)
            )
        todo = [(s, 0)]
        leaves = 0
        while todo:
            t, steps = todo.pop()
            t.globals["native"] = False
            require(steps < 50, "refill local execution bound")
            if steps and t.addr in (entry, dispatch):
                # One edge either dispatched without scanning or consumed one input.
                scanned = t.addr == entry
                added = scanned and t.solver.satisfiable(
                    extra_constraints=[c.ULT(a, b)]
                )
                if scanned:
                    agrees(t, c.ULT(ix, count), True, "scan next ID")
                    require(num < 4, "scan into full batch")
                    agrees(t, c.ULT(a, b), added, "skip exactly empty chains")
                else:
                    agrees(
                        t,
                        c.Or(ix == count, c.BoolV(num == 4)),
                        True,
                        "dispatch when ready",
                    )
                agrees(t, t.regs.sp, sp, "unchanged refill stack")
                next_expected = ix + 1 if scanned else ix
                check_context(
                    t,
                    persistent(t, n),
                    context(cached or added, next_expected),
                    "refill context",
                )
                agrees(t, t.regs.x13, num + int(added), "updated active lane count")
                for j in range(num):
                    agrees(
                        t,
                        load(t, base + j * 160, 160),
                        arbitrary[j],
                        "preserve earlier slot",
                    )
                if added:
                    agrees(
                        t,
                        load(t, base + 160 * num, 160),
                        packed,
                        "new slot representation",
                    )
                leaves += 1
                continue
            require(pc <= t.addr < pc + 4 * len(words), "refill native transfer")
            t.globals["native"] = True
            nx = env.project.factory.successors(t, extra_stop_points={entry, dispatch})
            require(
                nx.flat_successors and not nx.unconstrained_successors,
                "unresolved refill edge",
            )
            todo.extend((v, steps + 1) for v in nx.flat_successors)
        require(leaves >= 1, "empty refill proof")
        return leaves

    checks = 0
    for where in (entry, refill):
        for num in range(5):
            for cached in [False, True] if num == 0 else [True]:
                checks += check_edge(where, num, cached)
    # Return with no live slots, after exhausting the pending inputs. The only
    # restored memory supplied here is the frame that the prologue wrote. The
    # round/refill checks prohibit modifications to these saved bytes.
    s = env.blank(dispatch)
    s.regs.sp = sp
    for j, v in root[0]:
        if j in (18, 27, 28):
            setattr(s.regs, f"x{j}", v)
    s.regs.x13 = 0
    wrbytes(s, STACK - 0x90, saved)
    for kind in ("read", "write"):

        def guard_return(t, k=kind):
            if not t.globals.get("returning", False):
                return
            p = integer(t, getattr(t.inspect, f"mem_{k}_address"))
            size = integer(t, getattr(t.inspect, f"mem_{k}_length"))
            require(
                k == "read" and STACK - 0x90 <= p <= STACK - size,
                "unexpected return memory access",
            )

        s.inspect.b(f"mem_{kind}", when=angr.BP_BEFORE, action=guard_return)
    steps = 0
    while s.addr != RETURN:
        steps += 1
        require(steps < 10, "scheduler return bound")
        s.globals["returning"] = True
        ns = env.project.factory.successors(s)
        require(
            len(ns.flat_successors) == 1 and not ns.unconstrained_successors,
            "return transfer",
        )
        s = ns.flat_successors[0]
    s.globals["returning"] = False
    agrees(s, s.regs.sp, STACK, "normal return stack")
    for j, v in enumerate(preserved, 18):
        agrees(s, getattr(s.regs, f"x{j}"), v, "restored integer")
    for j, v in enumerate(vectors, 8):
        agrees(s, getattr(s.regs, f"q{j}")[63:0], v, "restored vector")
    print(
        "SHA-256", n, "initialization, return and", checks, "refill edges", flush=True
    )


if __name__ == "__main__":
    from pathlib import Path
    from driver import Image

    path = Path(sys.argv[1])
    for n in (16, 24, 32):
        verify(path, Image(path.read_bytes()), n)
