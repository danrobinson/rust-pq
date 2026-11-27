# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Symbolic replay of active-lane SHAKE short hashes, parent hashes and fused FORS leaves."""

from pathlib import Path
import tempfile
import angr
import claripy as bv

from build import SRC, compile_probe, function
from subtree import execute, project_for, word_row, zeros


def image(folder, width):
    body = (SRC / "shake/batch.rs").read_text()
    functions = [
        function(body, n)
        for n in (
            "word",
            "seed_words",
            "adrs_words",
            "header_active",
            "put_active",
            "read_active",
            "short_active",
            "pair_active",
        )
    ]
    functions.append(
        function((SRC / "shake/fors_batch.rs").read_text(), "fors_leaves_fused")
    )
    probe = Path(__file__).with_name("probe.rs").read_text()
    probe = probe.replace(
        "use crate::address::{", "use crate::address::{FORS_TREE, FORS_PRF, "
    )
    probe = probe.replace("// PRODUCTION_HELPERS", "\n".join(functions))
    layout = (SRC / "shake256/parallel.rs").read_text()
    # Compile both production layouts using the same x86 symbolic executor.
    layout = layout[
        layout.index('#[cfg(target_arch = "x86_64")]') : layout.index("/// One copy")
    ]
    if width == 3:
        layout = layout.replace('target_arch = "x86_64"', "any()")
        layout = layout.replace(
            'all(target_arch = "aarch64", not(target_vendor = "apple"))', "all()"
        )
    probe = probe.replace("// PRODUCTION_LAYOUT", layout)
    for name in ("address", "params"):
        probe = probe.replace(name.upper() + "_PATH", str(SRC / (name + ".rs")))
    for n in (16, 24, 32):
        probe += f"""
#[no_mangle] pub extern "C" fn active{n}(out:&mut [[u8;{n}];{width}], seed:&[u8;{n}],
  fields:&[[u8;32];{width}], left:&[[u8;{n}];{width}], right:&[[u8;{n}];{width}], active:usize, op:u32) {{
    let addrs=fields.map(|f| {{
        let u=|i:usize| u32::from_be_bytes(f[i..i+4].try_into().unwrap());
        address::Adrs {{ layer:u(0), tree:u64::from_be_bytes(f[8..16].try_into().unwrap()),
        typ:u(16), keypair:u(20), word2:u(24), word3:u(28) }}
    }});
    *out=match op {{
        0 => batch::short_active(seed,&addrs,left,active),
        1 => batch::pair_active(seed,&addrs,left,right,active),
        _ => batch::fors_leaves_fused(&left[0],seed,addrs[0],&addrs.map(|a|a.word3),active)
    }};
}}
"""
    return compile_probe(folder, probe)


def check(width, project, n, active, op):
    out, pk, addr, left, right, stop = [0x710000 + i * 0x10000 for i in range(6)]

    def fresh(label, size):
        return bv.BVS(label, size * 8)

    seed = fresh("seed", n)
    fields = [fresh("address", 32) for _ in range(width)]
    l, r = [[fresh(label, n) for _ in range(width)] for label in ("left", "right")]
    st = project.factory.call_state(
        project.loader.find_symbol(f"active{n}").rebased_addr,
        out,
        pk,
        addr,
        left,
        right,
        active,
        op,
        ret_addr=stop,
        prototype="void f(void*,void*,void*,void*,void*,unsigned long,unsigned)",
        add_options={
            angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    for ptr, data in [
        (pk, seed),
        (addr, bv.Concat(*fields)),
        (left, bv.Concat(*l)),
        (right, bv.Concat(*r)),
    ]:
        st.memory.store(ptr, data)

    def stream():
        values = l
        for phase in range(2 if op == 2 else 1):
            blocks = []
            for lane in range(active):
                field = fields[0 if op == 2 else lane]
                prefix = bv.Concat(
                    field.get_bytes(0, 4), zeros(4), field.get_bytes(8, 8)
                )
                if op == 2:
                    a = bv.Concat(
                        prefix,
                        bv.BVV(6 if phase == 0 else 3, 32),
                        field.get_bytes(20, 4),
                        zeros(4),
                        fields[lane].get_bytes(28, 4),
                    )
                    msg = bv.Concat(seed, a, l[0] if phase == 0 else values[lane])
                else:
                    a = bv.Concat(prefix, field.get_bytes(16, 16))
                    msg = (
                        bv.Concat(seed, a, l[lane], r[lane])
                        if op == 1
                        else bv.Concat(seed, a, l[lane])
                    )
                blocks.append(
                    bv.Concat(
                        msg,
                        bv.BVV(31, 8),
                        zeros(134 - msg.size() // 8),
                        bv.BVV(128, 8),
                        zeros(64),
                    )
                )
            permutation = [fresh("permute", 8 * width) for _ in range(25)]
            rows = [word_row(blocks, j) for j in range(25)] if active else []
            yield "active", (active, rows), permutation
            values = [
                bv.Concat(*(row.get_bytes(i * 8, 8) for row in permutation[: n // 8]))
                for i in range(active)
            ]
        yield "return", (), bv.Concat(*(values + [zeros(n)] * (width - active)))

    execute(
        project,
        st,
        out,
        stop,
        iter(stream()),
        width,
        f"width={width} n={n} active={active} op={op}",
    )


def main():
    with tempfile.TemporaryDirectory() as tmp:
        for width in (3, 8):
            project = project_for(image(Path(tmp), width))
            for n in (16, 24, 32):
                for active in range(width + 1):
                    for op in range(3):
                        check(width, project, n, active, op)


if __name__ == "__main__":
    main()
