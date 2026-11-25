#!/usr/bin/env python3
"""Match the last-finisher read and concatenate loop on the hosted SHAKE targets."""
from pathlib import Path
import os
import re
import runpy
import tempfile

ticket = runpy.run_path(str(Path(__file__).with_name("check-parallel-wots-ticket.py")))
common, lean = ticket["common"], ticket["lean"]
decls = runpy.run_path(str(Path(__file__).with_name("check-cache-mutation.py")))["decls"]


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    path = crate/"src/slh/parallel.rs"
    source = path.read_text()
    sign = ticket["shared"]["signer"].function(source, "sign")
    start = "let mut sig_fors = Vec::with_capacity(p.fors_sig_bytes());"
    stop = "let mut xmss_auth:"
    if sign.count(start)!=1 or sign.count(stop)!=1:
        raise ValueError("FORS packing region changed")
    body = start + sign.split(start)[1].split(stop)[0]
    path.write_text(source + "\nfn pack_fors<const N: usize>(p: &Params, fors_direct: Vec<OnceLock<[u8; N]>>) -> Vec<u8> {\n" +
                    body + "\nsig_fors\n}\n")
    return common["extract_target"](target,folder/"generated",["crate::shake::slh::parallel::pack_fors"],
                                    ["std::sync"],crate=crate,features="parallel,platform-sha2")


def program(pkg):
    calls = decls(pkg/"Funs.lean","CacheopsRust")
    known = set(decls(common["ROOT"]/"lean/Slhdsa/Funs.lean","slhdsa"))
    selected = [c for c in calls if "def shake.slh.parallel.pack_fors" in c]
    if len(selected)!=3 or set(calls)-set(selected)-known:
        raise ValueError("FORS packing dependencies changed")
    body = "\n\n".join(selected).replace("shake.slh.parallel.","")
    body = body.replace("std.sync.once_lock.OnceLock.get","ParallelSignJoin.readCell").replace("std.sync.once_lock.OnceLock","Option")
    body = re.sub(r"SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter\s+alloc.alloc.Global fors_direct",
                  "core.slice.Slice.iter fors_direct.deref",body)
    if set(re.findall(r"^axiom ([\w.]+)",(pkg/"FunsExternal_Template.lean").read_text(),re.M)) != {
            "std.sync.once_lock.OnceLock.get", "SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter"}:
        raise ValueError("unexpected FORS packing external functions")
    return ("import Parallel.SignJoinProgram\nopen Aeneas Aeneas.Std Result ControlFlow\n"
            "namespace slhdsa.ParallelForestPack\n" + body + "\nend slhdsa.ParallelForestPack\n")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin","aarch64-unknown-linux-gnu","x86_64-unknown-linux-gnu"):
            pkg=extract(Path(tmp)/target,target)
            if program(pkg).split()!=(lean/"Parallel/ForestPackProgram.lean").read_text().split():
                raise ValueError(f"FORS field concatenation changed on {target}")
            generated = pkg / "Funs.lean"
            original = generated.read_text()
            for before, after in [('core.clone.CloneU8 sig_fors s', 'core.clone.CloneU8 (alloc.vec.Vec.new Std.U8) s')]:
                if original.count(before) != 1:
                    raise ValueError(f"missing mutation site on {target}: {before}")
                generated.write_text(original.replace(before, after))
                if program(pkg).split() == (lean / "Parallel/ForestPackProgram.lean").read_text().split():
                    raise ValueError(f"undetected mutation on {target}: {before}")
    module="Parallel.ForestPack"
    common["facade"]["run"](["lake","build",module], lean)
    common["facade"]["audit_theorems"](module, ["slhdsa.ParallelForestPack.pack_spec","slhdsa.ParallelForestPack.pack_fips"])


if __name__=="__main__":
    main()
