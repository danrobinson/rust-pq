#!/usr/bin/env python3
"""Bind the unsigned split geometry, hash-tree index and cell of a queued XMSS chunk."""
from pathlib import Path
import os
import re
import runpy
import tempfile

tickets = runpy.run_path(str(Path(__file__).with_name("check-parallel-xmss-ticket.py")))
common, lean = tickets["common"], tickets["lean"]


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    path = crate/"src/slh/parallel.rs"
    code = path.read_text()
    sign = tickets["shared"]["shared"]["signer"].function(code, "sign")
    target_line, = re.findall(r"let xmss_target: u32 = [^;]+;", sign)
    geometry = sign.split("for h in 0..p.hp {", 1)[1].split("xmss_meta.push", 1)[0]
    meta, = re.findall(r"xmss_meta.push\(XmssAuthMeta\s*\{([^}]+)\}\);", sign)
    fields, = re.findall(r"kind: WorkKind::XmssSubtree\s*\{([^}]+)\}", sign)
    if re.findall(r"\w+", meta) != ["slot_start","split","root_idx","height","h"]:
        raise ValueError("unexpected XMSS reduction metadata")
    values = dict(re.findall(r"(layer|idx|height|slot):\s*([^,]+),", fields))
    if set(values)!={"layer","idx","height","slot"} or sign.count("for c in 0..chunks {")<1:
        raise ValueError("unexpected XMSS job fields")
    record = ",".join(values[k] for k in ("layer","idx","height","slot"))
    path.write_text(code + f"""
fn xmss_chunk(p: &Params, j: usize, index: u32, h: u32, c: usize, mut xmss_slot_count: usize)
 -> (usize, u32, u32, u32, usize, u16, u32, u32, usize) {{
 {target_line}
 {geometry}
 (xmss_slot_count,root_idx,split,h,slot_start,{record})
}}
""")
    return common["extract_target"](target,folder/"generated",["crate::shake::slh::parallel::xmss_chunk"],[],
                                    crate=crate,features="parallel,platform-sha2")


def program(pkg):
    funcs = runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))["decls"](pkg/"Funs.lean","CacheopsRust")
    if len(funcs)!=1 or "xmss_chunk" not in funcs[0]:
        raise ValueError("unexpected XMSS chunk helper")
    return ("import Parallel.XmssTicketHosted\nopen Aeneas Aeneas.Std Result\nnamespace slhdsa.ParallelXmssTicket\n" +
            funcs[0].replace("shake.slh.parallel.xmss_chunk","chunk") + "\nend slhdsa.ParallelXmssTicket\n")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    expected = (lean/"Parallel/XmssPlanProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin","aarch64-unknown-linux-gnu","x86_64-unknown-linux-gnu"):
            pkg=extract(Path(tmp)/target,target)
            if program(pkg).split()!=expected:
                raise ValueError(f"XMSS chunk fields changed on {target}")
            file=pkg/"Funs.lean"
            raw=file.read_text()
            file.write_text(raw.replace("root_idx <<< split","index <<< split"))
            if program(pkg).split()==expected:
                raise ValueError("accepted a chunk of the wrong subtree")
    module="Parallel.XmssPlan"
    common["facade"]["run"](["lake","build",module], lean)
    common["facade"]["audit_theorems"](module,["slhdsa.ParallelXmssTicket."+n for n in ("chunk_spec","issued_subtree")])


if __name__ == "__main__":
    main()
