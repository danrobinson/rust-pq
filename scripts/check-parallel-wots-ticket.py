#!/usr/bin/env python3
"""Extract the uncached worker's ticket-local signing computation from production."""
from pathlib import Path
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-parallel-sign-join.py")))
root, lean, common = (shared[name] for name in ("root", "lean", "common"))
start = "            let (addr, index) = layers[j];"
stop = '            slot.set(sig).expect("unique WOTS sign job");'


def ticket_body(source):
    sign = shared["signer"].function(source, "sign")
    phase = sign.split("let j = phase2_next.fetch_add(1, Ordering::Relaxed);")
    if len(phase) != 2 or phase[1].count(start) != 1 or phase[1].count(stop) != 1:
        raise ValueError("phase-two ticket boundaries changed")
    before, body = phase[1].split(start)
    if before.split() != "let Some(slot) = wots_sigs.get(j) else { break; };".split():
        raise ValueError("ticket slot owner changed")
    return start + body.split(stop)[0]


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    file = crate / "src/slh/parallel.rs"
    code = file.read_text()
    body = ticket_body(code)
    file.write_text(code + """
fn wots_ticket<const N: usize>(layers: &Vec<(Adrs, u32)>, roots: &Vec<[u8; N]>,
    j: usize, sk: &[u8; N], seed: &Seed<N>) -> Vec<u8> {
""" + body + "\n    sig\n}\n")
    return common["extract_target"](
        target, folder / "generated", ["crate::shake::slh::parallel::wots_ticket"],
        ["crate::shake::wots::wots_sign"], crate=crate, features="parallel,platform-sha2")


def program(pkg):
    text = (pkg / "Funs.lean").read_text()
    body = text[text.index("def shake.slh.parallel.wots_ticket"):text.rindex("end CacheopsRust")].strip()
    decls = runpy.run_path(str(Path(__file__).with_name("check-cache-construction.py")))["decls"]
    known = set(decls(root / "lean/Slhdsa/Funs.lean", "slhdsa"))
    imported = [decl for decl in decls(pkg / "Funs.lean", "CacheopsRust")
                if "def shake.slh.parallel.wots_ticket" not in decl]
    if len(imported) != 3 or any(decl not in known for decl in imported):
        raise ValueError("ticket address constant or operations changed")
    types = set(decls(pkg / "Types.lean", "CacheopsRust"))
    if not types.issubset(decls(root / "lean/Slhdsa/Types.lean", "slhdsa")):
        raise ValueError("ticket input types changed")
    external = re.findall(r"^axiom ([\w.]+)", (pkg / "FunsExternal_Template.lean").read_text(), re.M)
    if external != ["shake.wots.wots_sign"]:
        raise ValueError(f"unexpected ticket calls {external}")
    return ("import Shakebatch.WidthThreeNative\nopen Aeneas Aeneas.Std Result\n"
            "namespace slhdsa.ParallelSignTicket\n\n"
            + body.replace("def shake.slh.parallel.wots_ticket", "noncomputable def ticket")
              .replace("shake.wots.wots_sign a", "@WidthThree.shake.wots.wots_sign WidthThree.linuxWots N a")
            + "\n\nend slhdsa.ParallelSignTicket\n")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    with tempfile.TemporaryDirectory() as d:
        pkg = extract(Path(d), "aarch64-unknown-linux-gnu")
        checked = (lean / "Parallel/SignTicketProgram.lean").read_text().split()
        if program(pkg).split() != checked:
            raise ValueError("extracted Linux Arm WOTS ticket changed")
        path = pkg / "Funs.lean"
        source = path.read_text()
        for before, after in [("roots j", "roots 0#usize"), ("with_keypair a1 index", "with_keypair a1 0#u32")]:
            path.write_text(shared["signer"].once(source, before, after))
            if program(pkg).split() == checked:
                raise ValueError("accepted modified ticket data flow")
    module = "Parallel.SignTicket"
    shared["facade"]["run"](["lake", "build", module], lean)
    shared["facade"]["audit_theorems"](module, ["slhdsa.ParallelSignTicket." + n for n in
        ("ticket_spec", "published_row")])


if __name__ == "__main__":
    main()
