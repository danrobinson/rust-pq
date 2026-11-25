# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Check the production Metal descriptor loop step for arbitrary batch and tree indices."""

import json
import re
import sys
import tempfile
from pathlib import Path

import angr
import claripy as bv

sys.dont_write_bytecode = True

from build import SRC, compile_probe
from subtree import project_for

# (N, layers, XMSS height, FORS height, FORS trees), FIPS 205 Table 2.
ROWS = (
    (16, 7, 9, 12, 14),
    (16, 22, 3, 6, 33),
    (24, 7, 9, 14, 17),
    (24, 22, 3, 8, 33),
    (32, 8, 8, 14, 22),
    (32, 17, 4, 9, 35),
)


def build(folder):
    lib = (SRC.parents[1] / "metal/src/lib.rs").read_text()
    sign = lib.split("fn sign_internal_batch_family<", 1)[1].split("\n    }", 1)[0]
    (base,) = re.findall(r"let sig_byte_off = .*?;", sign)
    (step,) = re.findall(r"for j in 0\.\.d \{(.*?)\n            \}", sign, re.S)
    # Replace each Vec by a one-entry output sink for this symbolic loop step.
    # The descriptors, constructor expressions and cursor updates are verbatim.
    probe = (
        "#![no_std]\n" + f"#[path={json.dumps(str(SRC / 'params.rs'))}] mod params;\n"
    )
    bindings = []
    for name in ("sig_bytes", "fors_sig_bytes", "xmss_sig_bytes", "wots_len", "hp"):
        (binding,) = re.findall(rf"let {name} = [^;]*;", sign)
        bindings.append(binding)
    geometry = "\n".join(bindings)
    for typ in ("XmssTreeDesc", "WotsSignLayerDesc"):
        (decl,) = re.findall(rf"struct {typ} \{{[^}}]*\}}", lib)
        probe += "#[repr(C)]\n" + decl + "\n"
    probe += """
struct Sink<T>(Option<T>);
impl<T> Sink<T> { fn push(&mut self, v:T) { assert!(self.0.is_none()); self.0 = Some(v); } }
"""
    for n, d, hp, a, k in ROWS:
        row = f"r{n}_{hp}"
        param = f"SHA2_{n * 8}{'S' if d <= 8 else 'F'}"
        probe += f"""
#[no_mangle] pub extern "C" fn {row}(out: &mut [u64;14],sig_idx:usize,j:usize,key_idx:u32,mut tree:u64,mut leaf:u32) {{
const N: usize = {n}; let p = &params::{param};
{geometry}
let mut xmss_trees_host = Sink(None);
let mut wots_layers_host = Sink(None);
{base}
{step}
let x = xmss_trees_host.0.unwrap(); let w = wots_layers_host.0.unwrap();
*out = [x.tree,x.key_idx as u64,x.layer as u64,x.target_leaf as u64,x.auth_byte_off as u64,
w.tree,w.key_idx as u64,w.layer as u64,w.keypair as u64,w.sig_idx as u64,w.wots_byte_off as u64,
w._pad as u64,tree,leaf as u64];
}}
"""
    return compile_probe(folder, probe)


def check(project, n, d, hp, a, k):
    out, stop = 0x710000, 0x720000
    item, layer, tree = (bv.BVS(x, 64) for x in ("item", "layer", "tree"))
    key, leaf = (bv.BVS(x, 32) for x in ("key", "leaf"))
    st = project.factory.call_state(
        project.loader.find_symbol(f"r{n}_{hp}").rebased_addr,
        out,
        item,
        layer,
        key,
        tree,
        leaf,
        ret_addr=stop,
        prototype="void f(void*,unsigned long long,unsigned long long,unsigned,unsigned long long,unsigned)",
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    size = n * (1 + k * (1 + a) + d * (2 * n + 3 + hp))
    st.solver.add(item.ULT(0xFFFFFFFF // size), layer.ULT(d))
    if not st.solver.satisfiable():
        raise AssertionError("empty descriptor domain")
    domain = st.copy()
    while st.addr != stop:
        if project.is_hooked(st.addr):
            raise ValueError("unexpected call from descriptor constructor")
        succ = project.factory.successors(st)
        if len(succ.flat_successors) != 1 or succ.unconstrained_successors:
            raise ValueError("unexpected control flow in descriptor constructor")
        st = succ.flat_successors[0]
    if domain.solver.satisfiable(
        extra_constraints=[bv.Not(bv.And(*st.solver.constraints))]
    ):
        raise ValueError("descriptor execution excluded valid inputs")
    wots = item * size + n * (1 + k * (1 + a)) + layer * (n * (2 * n + 3 + hp))
    outputs = [
        tree,
        key.zero_extend(32),
        layer,
        leaf.zero_extend(32),
        wots + n * (2 * n + 3),
        tree,
        key.zero_extend(32),
        layer,
        leaf.zero_extend(32),
        item,
        wots,
        0,
        bv.LShR(tree, hp),
        tree % (1 << hp),
    ]
    actual = [
        st.memory.load(out + i * 8, 8, endness=project.arch.memory_endness)
        for i in range(len(outputs))
    ]
    if st.solver.satisfiable(
        extra_constraints=[bv.Or(*(a != b for a, b in zip(actual, outputs)))]
    ):
        raise ValueError(f"descriptor mismatch for N={n}, hp={hp}")
    print(
        f"checked all descriptor fields and next layer cursor: N={n}, hp={hp}",
        flush=True,
    )


if __name__ == "__main__":
    with tempfile.TemporaryDirectory() as tmp:
        project = project_for(build(Path(tmp)))
        for row in ROWS:
            check(project, *row)
