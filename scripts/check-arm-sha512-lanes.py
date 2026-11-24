#!/usr/bin/env python3
"""Bind the interleaved Arm SHA-512 schedule to the extracted two-round theorem."""

import os
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
facade = runpy.run_path(str(HERE / "check-platform-facade.py"))
common = facade["common"]
ROOT, LEAN = facade["ROOT"], facade["LEAN"]


def schedule(folder):
    src = (ROOT / "rust/src/sha512/paired.rs").read_text()
    start = src.index("unsafe fn rounds_lanes")
    rounds = src[start : src.index("\n}", start) + 2]
    # Replace the pointer load with checked indexing into an array of constant
    # word positions. The extracted lane body consumes two words per call.
    load = "vld1q_u64(k_ptr.add(2 * $i))"
    if rounds.count(load) != 1:
        raise ValueError("review the paired round-constant load")
    rounds = rounds.replace("k_ptr: *const u64", "k_ptr: &[u64; 80]").replace(
        load, "&k_ptr[2*$i..2*$i+2]"
    )
    probe = """
struct Lane { state: (usize,usize), schedule:(usize,usize) }
fn lane_step<const I:usize>(s:&mut (usize,usize), w:&mut (usize,usize), k:&[u64]) {
    assert_eq!(s,w);
    assert_eq!(s.1,I);
    assert_eq!(k,[(2*I) as u64,(2*I+1) as u64]);
    s.1+=1;
    w.1+=1;
}
fn check<const L:usize>() {
    let mut lanes=std::array::from_fn::<_,L,_>(|j|Lane{state:(j,0),schedule:(j,0)});
    unsafe { rounds_lanes(&mut lanes,&std::array::from_fn(|i|i as u64)); }
    for (j,l) in lanes.iter().enumerate(){assert_eq!(l.state,(j,40));assert_eq!(l.schedule,l.state);}
}
"""
    # Check every production instantiation, including generic wrappers.
    if re.search(r"rounds_lanes::<(?!K_LANES>|[124]>)", src):
        raise ValueError("review the new rounds_lanes instantiation")
    path = folder / "schedule.rs"
    path.write_text(
        probe + rounds + "\nfn main(){check::<1>();check::<2>();check::<4>();}"
    )
    subprocess.run(["rustc", path, "-o", folder / "schedule"], check=True)
    subprocess.run([folder / "schedule"], check=True)


def extraction(folder, target):
    fresh = facade["extract"](
        "rust",
        target,
        "Lane",
        folder,
        ("crate::sha512::paired::lane_step",),
        ("crate::sha512::hw::arm",),
    )
    reference = set(
        common["declarations"](common["body"](LEAN / "Paired/Funs.lean", "PairedRust"))
    )
    decls = list(common["declarations"](common["body"](fresh / "Funs.lean")))
    if (
        len(decls) != 1
        or decls[0] not in reference
        or not decls[0].startswith("def sha512.paired.lane_step")
    ):
        raise ValueError(
            f"the lane body differs from the proved extraction on {target}"
        )
    template = (
        (fresh / "FunsExternal_Template.lean").read_text().split("open slhdsa", 1)[1]
    )
    check = ["import Paired.Proof", "open Aeneas Aeneas.Std Result PairedRust"]
    names = set()
    for decl in common["declarations"](template):
        m = re.fullmatch(r"axiom (\S+)\s*:\s*(.*)", decl, re.S)
        name, typ = m.groups()
        names.add(name)
        check.append(f"example : {typ} := PairedRust.{name}")
    if names != {
        "sha512.hw.arm." + x
        for x in ("add", "ext1", "sha512h", "sha512h2", "sha512su0", "sha512su1")
    }:
        raise ValueError("unexpected two-round primitive boundary")
    common["run"](
        ["lake", "env", "lean", "--stdin"], LEAN, input="\n".join(check), text=True
    )


def main():
    os.environ["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".cargo/bin"),
            str(Path.home() / ".elan/bin"),
            os.environ["PATH"],
        ]
    )
    common["run"](["lake", "build", "Paired.Proof"], LEAN)
    constants = re.search(
        r"const K: \[u64; 80\] = \[([^\]]+)\];",
        (ROOT / "rust/src/sha512.rs").read_text(),
    )[1]
    words = [
        re.fullmatch(r"0x[0-9a-f]+", k.strip())[0]
        for k in constants.strip().rstrip(",").split(",")
    ]
    common["run"](
        ["lake", "env", "lean", "--stdin"],
        LEAN,
        input=f"import Paired.Proof\nexample : Spec.SHA512.K = [{','.join(words)}] := by decide",
        text=True,
    )
    with tempfile.TemporaryDirectory() as tmp:
        scratch = Path(tmp)
        schedule(scratch)
        for target in facade["TARGETS"][:2]:
            folder = scratch / target
            folder.mkdir()
            extraction(folder, target)
    facade["audit_theorems"](
        "Paired.Proof", ["slhdsa.H512.Paired.lane_spec", "slhdsa.H512.kcompress_eq"]
    )


if __name__ == "__main__":
    main()
