# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the compiled Arm SHA-256 short-block SIMD packing and digest load/store."""

import re
import sys
import tempfile
from pathlib import Path

sys.dont_write_bytecode = True
import angr
import claripy as bv
from build import SRC, compile_probe
from subtree import project_for, zeros


def function(source, decl, indent):
    start = source.index(decl)
    return source[start : source.index("\n" + " " * indent + "}", start) + indent + 2]


def build_arm(folder):
    wide = (SRC / "sha256/arm_wide.rs").read_text()
    core = (SRC / "sha256.rs").read_text()
    source = """#![no_std]
use core::arch::aarch64::*;
type V = uint32x4_t;
mod arm { use super::*;
"""
    source += function(core, "pub fn load_be(b:", 12) + "\n}\n"
    for name in ("load_n", "store_n", "make_hdr", "pack_short"):
        source += function(wide, "unsafe fn " + name, 4) + "\n"
    for n in (16, 24, 32):
        source += f"""
#[no_mangle] pub unsafe extern "C" fn pack{n}(out:*mut u32, copy:&mut [u8;{n}],
            src:&[u8;{n}], word2:u32, word3:u32) {{
    let (x,xb)=load_n::<{n}>(src);
    let (a,b,c)=pack_short::<{n}>(make_hdr(word2,word3),x,xb);
    vst1q_u32(out,a); vst1q_u32(out.add(4),b); vst1q_u32(out.add(8),c);
    store_n::<{n}>(copy,x,xb);
}}
"""
    return compile_probe(folder, source, "aarch64-unknown-linux-gnu")


class ArmPackingEngine(angr.engines.UberEngine):
    def _perform_vex_expr_Op(self, op, args):
        # VEX uses these operations for NEON REV instructions. The pinned
        # angr release only implements the 32-in-64 variant.
        if op == "Iop_ZeroHI64ofV128":
            ((value, deps),) = args
            return bv.ZeroExt(64, value[63:0]), deps
        reverse = re.fullmatch(r"Iop_Reverse(8|16|32)sIn(16|32|64)_x(2|4|8)", op)
        if reverse:
            elem, group, count = map(int, reverse.groups())
            ((value, deps),) = args
            assert value.size() == group * count and group % elem == 0
            groups = value.chop(group)
            return bv.Concat(
                *(bv.Concat(*reversed(g.chop(elem))) for g in groups)
            ), deps
        return super()._perform_vex_expr_Op(op, args)


def check(project, n):
    out, copy, src, stop = 0x700000, 0x710000, 0x720000, 0x740000
    data = bv.BVS("digest", 8 * n)
    w2, w3 = bv.BVS("word2", 32), bv.BVS("word3", 32)
    st = project.factory.call_state(
        project.loader.find_symbol(f"pack{n}").rebased_addr,
        out,
        copy,
        src,
        w2,
        w3,
        ret_addr=stop,
        prototype="void f(void*,void*,void*,unsigned,unsigned)",
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    st.memory.store(src, data)
    # W4..W15 follow the first 16 compressed address bytes.
    suffix = bv.Concat(
        w2[15:0], w3, data, bv.BVV(128, 8), zeros(33 - n), bv.BVV((64 + 22 + n) * 8, 64)
    )
    expected = bv.Concat(*(suffix.get_bytes(i, 4).reversed for i in range(0, 48, 4)))
    writes = [(out, 48), (copy, n)]

    def bounds(state, event):
        address = getattr(state.inspect, event + "_address")
        length = getattr(state.inspect, event + "_length")
        if getattr(address, "symbolic", False) or getattr(length, "symbolic", False):
            raise ValueError("symbolic memory access")
        a = state.solver.eval(address)
        size = state.solver.eval(length) if not isinstance(length, int) else length
        allowed = writes if event == "mem_write" else [(src, n)] + writes
        # LLVM may load shuffle masks from read-only ELF data.
        if event == "mem_read" and project.loader.main_object.contains_addr(a):
            return
        if not any(b <= a and a + size <= b + l for b, l in allowed):
            raise ValueError(f"unexpected {event} at {a:#x} ({size} bytes)")

    for event in ("mem_read", "mem_write"):
        st.inspect.b(
            event, when=angr.BP_BEFORE, action=lambda state, e=event: bounds(state, e)
        )
    engine = ArmPackingEngine(project)
    while st.addr != stop:
        if project.is_hooked(st.addr):
            raise ValueError("unexpected external call")
        succ = project.factory.successors(st, engine=engine)
        if len(succ.flat_successors) != 1 or succ.unconstrained_successors:
            raise ValueError("nonunique control flow")
        st = succ.flat_successors[0]
        if any(c.symbolic for c in st.solver.constraints):
            raise ValueError("symbolic input restriction")
    if st.solver.satisfiable(
        extra_constraints=[
            bv.Or(st.memory.load(out, 48) != expected, st.memory.load(copy, n) != data)
        ]
    ):
        raise ValueError("incorrect Arm packed words or digest")
    print(f"Arm SHA-256 pack, load and store checked at {n} bytes")


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        project = project_for(build_arm(Path(tmp)))
        for n in (16, 24, 32):
            check(project, n)
