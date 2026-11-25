# /// script
# requires-python = ">=3.11,<3.14"
# dependencies = ["angr==9.2.213", "bitstring==4.3.1", "pycparser==3.0"]
# ///
"""Prove observable x86 FORS gather/refill values with fresh bytes at each oracle call."""

from concurrent.futures import ProcessPoolExecutor
from pathlib import Path
import os
import logging
import tempfile

from buffered_lift import lift_rows
from buffered_tree import calls
from build import SRC
from fors_buffered_image import image
import subtree
import fors_gather

logging.getLogger("cle.loader").setLevel(logging.ERROR)
bv = subtree.bv


def check(args):
    path, n, h, label = args
    p = subtree.project_for(path)
    idx = bv.ZeroExt(h, bv.BVS("index", 32 - h))
    sk, seed = bv.BVS("secret", 8 * n), bv.BVS("seed", 8 * n)
    words = [bv.BVS("word", 32) for _ in range(7)]
    layer, hi, lo = words[:3]
    tail = bv.Concat(*(word.reversed for word in words[3:]))
    out, skp, seedp, addrp, stop = 0x710000, 0x720000, 0x730000, 0x740000, 0x750000
    st = p.factory.call_state(
        p.loader.find_symbol(f"tree{n}").rebased_addr,
        out,
        skp,
        seedp,
        idx,
        h,
        addrp,
        ret_addr=stop,
        prototype="void f(void*,void*,void*,unsigned,unsigned,void*)",
        add_options={
            subtree.angr.options.SYMBOL_FILL_UNCONSTRAINED_MEMORY,
            subtree.angr.options.SYMBOL_FILL_UNCONSTRAINED_REGISTERS,
        },
    )
    for ptr, data in [
        (skp, sk),
        (seedp, seed),
        (addrp, bv.Concat(*(word.reversed for word in words))),
    ]:
        st.memory.store(ptr, data)
    fors_gather.check_output_frame(st, out, n)
    stream = calls(n, h, sk, seed, idx, layer, bv.Concat(hi, lo), tail, fors=True)
    subtree.execute(p, st, out, stop, stream, 8, f"FORS {label} n={n} h={h}")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:" + os.environ["PATH"]
    source = (SRC / "shake/fors_batch.rs").read_text()
    with tempfile.TemporaryDirectory() as tmp:
        jobs = []
        gathers = []
        for label, s in (
            ("original", source),
            ("snapshots", lift_rows(source, "fors_subtree_horiz")),
        ):
            folder = Path(tmp) / label
            folder.mkdir()
            binary = image(folder, s)
            fragment = folder / "fragments"
            fragment.mkdir()
            gather_image = fors_gather.build(fragment, s)
            gathers.extend(
                (gather_image, n, h, label) for n in (16, 24, 32) for h in range(14)
            )
            jobs.extend((binary, n, h, label) for n in (16, 24, 32) for h in (3, 4, 5))
        with ProcessPoolExecutor(max_workers=min(4, os.cpu_count() or 1)) as workers:
            list(workers.map(check, jobs))
            list(workers.map(fors_gather.check, gathers))
        print(
            f"Compared all eight output lanes of {3 * len(gathers)} optimized gather calls with arbitrary rows and prior scratch."
        )


if __name__ == "__main__":
    main()
