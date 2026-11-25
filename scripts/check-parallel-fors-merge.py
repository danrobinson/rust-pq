#!/usr/bin/env python3
"""Extract the last finisher's split-FORS input range and physical destination."""
from pathlib import Path
import os
import re
import runpy
import tempfile

ticket=runpy.run_path(str(Path(__file__).with_name("check-parallel-wots-ticket.py")))
common,lean=ticket["common"],ticket["lean"]
decls=runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))["decls"]


def extract(folder,target):
    crate=common["copy_rust_crate"](folder)
    f=crate/"src/slh/parallel.rs"
    code=f.read_text()
    sign=ticket["shared"]["signer"].function(code,"sign")
    begin="for meta in &fors_split_meta {"
    end="let mut sig_fors ="
    if sign.count(begin)!=1 or sign.count(end)!=1:
        raise ValueError("split reducer or following packing changed")
    arm=sign.split(begin)[1].split(end)[0].strip()
    pub=re.fullmatch(r"(.*)fors_direct\[(.*?)\]\s*\.set\(val\)\s*\.expect\(\"unique reduced FORS slot\"\);\s*}",arm,re.S)
    if not pub:
        raise ValueError("changed publication target for a reduced FORS subtree")
    f.write_text(code+"""
fn merge_fors<const N: usize>(meta: &ForsSplitMeta, fors_split: &Vec<OnceLock<[u8;N]>>,
    seed: &Seed<N>, fors_addr: Adrs, fors_stride: usize) -> (usize,[u8;N]) {
""" + pub[1] + "("+pub[2]+",val)\n}\n")
    return common["extract_target"](target,folder/"generated",["crate::shake::slh::parallel::merge_fors"],
                                    ["crate::shake::slh::parallel::reduce_tree","std::sync"],crate=crate,features="parallel,platform-sha2")


def program(pkg):
    funcs=decls(pkg/"Funs.lean","CacheopsRust")
    types=decls(pkg/"Types.lean","CacheopsRust")
    meta,=(d for d in types if "structure shake.slh.parallel.ForsSplitMeta" in d)
    if len(funcs)!=1 or set(re.findall(r"^axiom ([\w.]+)",(pkg/"FunsExternal_Template.lean").read_text(),re.M))!={"shake.slh.parallel.reduce_tree"}:
        raise ValueError("unexpected FORS merge calls")
    body=(meta+"\n\n"+funcs[0]).replace("shake.slh.parallel.ForsSplitMeta","Meta").replace("shake.slh.parallel.merge_fors","merge_fors")
    body=body.replace("std.sync.once_lock.OnceLock","Option").replace("shake.slh.parallel.reduce_tree","@ParallelReduceNative.reduce_tree ParallelReduceNative.shakeFamily N")
    return ("import Parallel.ReduceNative\nopen Aeneas Aeneas.Std Result\nnamespace slhdsa.ParallelForsMerge\n"+
            body+"\nend slhdsa.ParallelForsMerge\n")


def main():
    os.environ["PATH"]=f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:"+os.environ["PATH"]
    checked=(lean/"Parallel/ForsMergeProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin","aarch64-unknown-linux-gnu","x86_64-unknown-linux-gnu"):
            pkg=extract(Path(tmp)/target,target)
            if program(pkg).split()!=checked:
                raise ValueError(f"FORS merge changed on {target}")
            generated = pkg / "Funs.lean"
            original = generated.read_text()
            for before, after in [('start := «meta».slot_start', 'start := 0#usize'), ('i3 + i4', 'i3 + i1')]:
                if original.count(before) != 1:
                    raise ValueError(f"missing mutation site on {target}: {before}")
                generated.write_text(original.replace(before, after))
                if program(pkg).split() == (lean / "Parallel/ForsMergeProgram.lean").read_text().split():
                    raise ValueError(f"undetected mutation on {target}: {before}")
    module="Parallel.ForsMergeHosted"
    common["facade"]["run"](["lake","build",module],lean)
    common["facade"]["audit_theorems"](module,["slhdsa.ParallelForsMerge.merge_spec"] + [host + ".ForsMerge.slhdsa.ParallelForsMerge.merge_spec" for host in ("RootTableApple", "RootTableArm", "RootTableX86")])


if __name__=="__main__":
    main()
