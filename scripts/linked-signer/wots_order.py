# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Inductive binary proof of the histogram, prefix sums and rank scatter used by WOTS.

For input position i, rank = number of smaller digits in the whole input plus the
occurrences of digit[i] before i. The Lean theorem linkedSlot_bijective in
Shakebatch.LinkedOrder shows these slots form a permutation.
"""

import argparse
from pathlib import Path
import re, subprocess, sys

sys.dont_write_bytecode = True
from wots_chains import (
    ImageEnv,
    c,
    Image,
    angr,
    load,
    unsigned,
    put,
    wrbytes,
    agrees,
    integer,
    require,
    return_call,
    STACK,
    KEY,
    RESULT,
    RETURN,
)

BASE = KEY
FRAME = STACK - 176
TMP = KEY + 4096


def prove(env, path):
    pc, hi = env.fun(b"5batch11chain_order")
    start, size, _ = env.image.sections[b"__stubs"]
    stubs = subprocess.check_output(
        ["xcrun", "llvm-objdump", "--macho", "--indirect-symbols", path], text=True
    )
    (zero,) = [
        int(x, 16)
        for x in re.findall(r"^(0x[0-9a-f]+)\s+\d+\s+_bzero$", stubs, re.M)
        if start <= int(x, 16) < start + size
    ]
    n = c.BVS("length", 7).zero_extend(57)
    i = c.BVS("i", 7).zero_extend(57)
    rem = n - i
    counters = [c.BVS("bucket", 7).zero_extend(57) for _ in range(16)]
    saved = {j: c.BVS("callee_saved", 64) for j in range(18, 30)}
    saved[30] = RETURN
    total = 0
    for phase, head, stops in [
        ("entry", 0, [0x48]),
        ("count", 0x48, [0x48, 0x68]),
        ("prefix", 0x68, [0x134]),
        ("scatter", 0x134, [0x134, 0x164]),
        ("return", 0x164, [RETURN - pc]),
    ]:
        for d in range(16 if phase in ("count", "scatter") else 1):
            s = env.blank(pc + head)
            s.add_constraints(c.UGE(n, 1), c.ULE(n, 67), c.ULT(i, n))
            for j, x in saved.items():
                setattr(s.regs, "x" + str(j), x)
            if phase == "entry":
                s.regs.x0 = BASE
                s.regs.x1 = n
                s.regs.x8 = RESULT
            else:
                s.regs.x19 = BASE
                s.regs.x20 = RESULT
                s.regs.x21 = n
                s.regs.x22 = 4 * n
                s.regs.sp = FRAME
                for j in range(16):
                    put(s, FRAME + 8 * j, counters[j], 8)
                for j, r in enumerate((22, 21, 20, 19, 29, 30)):
                    put(s, FRAME + 128 + 8 * j, saved[r], 8)
            if phase == "count":
                s.regs.x8 = FRAME
                s.regs.x9 = 4 * rem
                s.regs.x10 = BASE + 4 * i
            if phase == "scatter":
                s.regs.x9 = i
                s.regs.x10 = FRAME
                s.regs.x22 = 4 * rem
                # Before scatter, the cursor for this bucket is rank(digits,i).
                # rank_lt ensures this element fits the output; it also precludes overflow.
                s.add_constraints(c.ULT(counters[d], n))
            vkept = {j: getattr(s.regs, f"q{j}")[63:0] for j in range(8, 16)}
            domain = tuple(s.solver.constraints)

            def watch(st, kind):
                ptr = getattr(st.inspect, "mem_" + kind + "_address")
                le = getattr(st.inspect, "mem_" + kind + "_length")
                count = (
                    integer(st, le)
                    if le is not None
                    else getattr(st.inspect, "mem_" + kind + "_expr").size() // 8
                )
                if not isinstance(ptr, int) and ptr.symbolic:
                    if kind == "read" and phase in ("count", "scatter"):
                        agrees(st, ptr, BASE + 4 * i, "digit read address")
                        require(count == 4, "digit width")
                        put(st, TMP, d, 4)
                        st.inspect.mem_read_address = TMP
                        st.globals["digit"] = st.globals.get("digit", 0) + 1
                    elif kind == "write" and phase == "scatter":
                        agrees(
                            st,
                            ptr,
                            RESULT + 8 * counters[d],
                            "ranked order write address",
                        )
                        require(count == 8, "rank width")
                        agrees(
                            st, st.inspect.mem_write_expr, i, "scattered original index"
                        )
                        require(
                            st.inspect.mem_write_endness == "Iend_LE",
                            "index word endian",
                        )
                        st.globals["scatter"] = st.globals.get("scatter", 0) + 1
                        st.inspect.mem_write_address = TMP
                    else:
                        raise ValueError("unmodeled symbolic order access")
                else:
                    p = integer(st, ptr)
                    require(
                        any(
                            a <= p and p + count <= b
                            for a, b in [(FRAME, STACK), (TMP, TMP + 8)]
                        ),
                        f"order access outside frame {phase} {kind} {st.addr - pc:#x} {p:#x} size={count}",
                    )

            for k in ("read", "write"):
                s.inspect.b(
                    "mem_" + k, when=angr.BP_BEFORE, action=lambda st, k=k: watch(st, k)
                )
            todo = [(s, 0)]
            paths = []
            while todo:
                st, steps = todo.pop()
                require(steps < 15, "order path bound")
                off = st.addr - pc
                if off in stops and steps:
                    agrees(st, st.regs.x18, saved[18], "platform register")
                    for j, v in vkept.items():
                        agrees(
                            st,
                            getattr(st.regs, f"q{j}")[63:0],
                            v,
                            "preserved vector lane",
                        )
                    if phase in ("entry", "count", "prefix", "scatter"):
                        agrees(st, st.regs.sp, FRAME, "order frame")
                        for j, r in enumerate((22, 21, 20, 19, 29, 30)):
                            agrees(
                                st,
                                unsigned(st, FRAME + 128 + 8 * j),
                                saved[r],
                                "saved order frame",
                            )
                        for r, v in [
                            (19, BASE),
                            (20, RESULT),
                            (21, n),
                            (22, 4 * (rem - 1) if phase == "scatter" else 4 * n),
                        ]:
                            agrees(
                                st,
                                getattr(st.regs, "x" + str(r)),
                                v,
                                "order loop invariant",
                            )
                        for j in range(16):
                            expected = {
                                "entry": 0,
                                "count": counters[j] + int(j == d),
                                "prefix": sum(counters[:j]),
                                "scatter": counters[j] + int(j == d),
                            }[phase]
                            agrees(
                                st,
                                unsigned(st, FRAME + 8 * j),
                                expected,
                                "bucket " + str(j),
                            )
                        if phase in ("count", "scatter"):
                            require(st.globals.get("digit") == 1, "missing digit read")
                            agrees(st, (rem == 1), off != head, "iteration guard")
                        if phase == "entry":
                            agrees(st, st.regs.x8, FRAME, "histogram address")
                            agrees(st, st.regs.x9, 4 * n, "histogram length")
                            agrees(st, st.regs.x10, BASE, "digit pointer")
                            for j, r in enumerate((22, 21, 20, 19, 29, 30)):
                                agrees(
                                    st,
                                    unsigned(st, FRAME + 128 + 8 * j),
                                    saved[r],
                                    "saved order register",
                                )
                        if phase == "count":
                            agrees(st, st.regs.x8, FRAME, "next bucket pointer")
                            agrees(
                                st,
                                st.regs.x9,
                                4 * (rem - 1),
                                "remaining histogram bytes",
                            )
                            agrees(
                                st,
                                st.regs.x10,
                                BASE + 4 * (i + 1),
                                "next histogram digit",
                            )
                        if phase == "prefix":
                            require(
                                st.globals.get("zeroed"), "order buffer initialization"
                            )
                            agrees(st, st.regs.x9, 0, "initial scatter index")
                            agrees(st, st.regs.x10, FRAME, "scatter offsets")
                        if phase == "scatter":
                            require(
                                st.globals.get("scatter") == 1, "missing rank store"
                            )
                            agrees(st, st.regs.x9, i + 1, "next original index")
                            agrees(st, st.regs.x10, FRAME, "next bucket")
                    else:
                        for j, v in saved.items():
                            agrees(
                                st,
                                getattr(st.regs, "x" + str(j)),
                                v,
                                "order return ABI",
                            )
                        agrees(st, st.regs.sp, STACK, "order return frame")
                    paths.append(c.And(*st.solver.constraints))
                    continue
                if st.addr == zero:
                    agrees(st, st.regs.x0, RESULT, "order zero destination")
                    agrees(st, st.regs.x1, 536, "order zero length")
                    st.globals["zeroed"] = True
                    return_call(st)
                    todo.append((st, steps + 1))
                    continue
                require(pc <= st.addr < hi, "unexpected order transfer")
                nxt = env.project.factory.successors(
                    st, extra_stop_points={pc + o for o in stops}
                )
                require(
                    nxt.flat_successors and not nxt.unconstrained_successors,
                    "unresolved order exit",
                )
                todo.extend((t, steps + 1) for t in nxt.flat_successors)
            solver = c.Solver()
            solver.add(domain)
            require(
                paths
                and not solver.satisfiable(extra_constraints=[c.Not(c.Or(*paths))]),
                "incomplete order input domain",
            )
            total += len(paths)
    return total


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("image", type=Path)
    arg = p.parse_args()
    print(
        "ranked order paths",
        prove(ImageEnv(arg.image, Image(arg.image.read_bytes()), 16), arg.image),
    )
