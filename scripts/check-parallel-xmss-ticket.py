#!/usr/bin/env python3
"""Re-extract the computation and destination of both phase-one XMSS ticket variants."""
from pathlib import Path
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-parallel-wots-ticket.py")))
common, lean = shared["common"], shared["lean"]
types = {"subtree": "layer: u16, idx: u32, height: u32, slot: usize",
         "leaf": "layer: u16"}


def extract(folder, target):
    crate = common["copy_rust_crate"](folder)
    file = crate / "src/slh/parallel.rs"
    source = file.read_text()
    sign = shared["shared"]["signer"].function(source, "sign")
    leaf_jobs = """let leaf_pk_count = d.saturating_sub(1);
        for j in 0..leaf_pk_count {
            jobs.push(WorkItem { weight: 256, kind: WorkKind::XmssLeafPk { layer: j as u16 }, });
        }"""
    code = re.sub(r"//[^\n]*|\s+", "", sign)
    if code.count("".join(leaf_jobs.split())) != 1:
        raise ValueError("XMSS signing-leaf ticket coverage or layer cast changed")
    if code.count("leaf_pks:Vec<OnceLock<[u8;N]>>=(0..leaf_pk_count).map(|_|OnceLock::new()).collect()") != 1:
        raise ValueError("XMSS signing-leaf storage initialization changed")
    body = sign.split("match item.kind {")[-1]
    for name, arm, next_arm, table in [("subtree", "XmssSubtree", "XmssLeafPk", "xmss_slots"),
                                      ("leaf", "XmssLeafPk", "ForsTreeLow", "leaf_pks")]:
        raw = body.split("WorkKind::" + arm + " {", 1)[1].split("WorkKind::" + next_arm, 1)[0]
        fields, computation = raw.split("} => {", 1)
        required = [field.split(":")[0] for field in types[name].split(", ")]
        if re.findall(r"\w+", fields) != required:
            raise ValueError(f"incorrect {arm} pattern")
        pre, publication = computation.split(table + "[", 1)
        destination, end = publication.split("]", 1)
        if not re.fullmatch(r'\s*\.set\(val\)\s*\.expect\("unique XMSS [^"]+"\);\s*}', end.strip()):
            raise ValueError(f"unexpected {arm} publication")
        source += ("\nfn " + name + "_ticket<const N: usize>(layers: &Vec<(Adrs, u32)>, " +
                   types[name] + ", sk: &[u8; N], seed: &Seed<N>) -> (usize, [u8; N]) {\n" +
                   pre + "(" + destination + ", val)\n}\n")
    begin = "    let mut layers = Vec::with_capacity(d);"
    end = "    let fors_indices = "
    if sign.count(begin) != 1 or sign.count(end) != 1 or sign.count("let d = p.d as usize;") != 1:
        raise ValueError("worker layer initialization changed")
    layers = begin + sign.split(begin)[1].split(end)[0]
    source += ("\nfn build_layers(p: &Params, mut tree: u64, mut leaf: u32) -> Vec<(Adrs, u32)> {\n"
               + "let d = p.d as usize;\n" + layers + "layers\n}\n")
    file.write_text(source)
    return common["extract_target"](target, folder/"generated", ["crate::shake::slh::parallel::" + n + "_ticket"
        for n in types] + ["crate::shake::slh::parallel::build_layers"], ["crate::shake::xmss::xmss_node", "crate::address"], crate=crate, features="parallel,platform-sha2")


def program(pkg):
    expected = {"address.Adrs.new", "address.Adrs.with_layer", "address.Adrs.with_tree", "shake.xmss.xmss_node"}
    if set(re.findall(r"^axiom ([\w.]+)", (pkg/"FunsExternal_Template.lean").read_text(), re.M)) != expected:
        raise ValueError("unexpected phase-one externals")
    calls = (pkg/"Funs.lean").read_text()
    calls = re.sub(r"/--[\s\S]*?-/", "", calls)
    body = calls[calls.index("def shake.slh.parallel."):calls.rindex("end CacheopsRust")]
    body = body.replace("shake.slh.parallel.", "").replace("{N : Std.Usize}", "{N : Std.Usize} (node : Node N)")
    body = body.replace("shake.xmss.xmss_node", "node")
    return ("import Shakebatch.WidthThreeNative\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace slhdsa.ParallelXmssTicket\n"
            "abbrev Node (N : Usize) := Array U8 N → U32 → U32 → Array U8 N → address.Adrs → Result (Array U8 N)\n\n"
            + body.strip() + "\nend slhdsa.ParallelXmssTicket\n")


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    checked = (lean/"Parallel/XmssTicketProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as tmp:
        for target in ("aarch64-apple-darwin", "aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"):
            pkg = extract(Path(tmp)/target, target)
            if program(pkg).split() != checked:
                raise ValueError(f"phase-one XMSS ticket changed on {target}")
            file = pkg/"Funs.lean"
            raw = file.read_text()
            file.write_text(raw.replace("sk idx height seed", "sk height idx seed"))
            if program(pkg).split() == checked:
                raise ValueError("accepted swapped tree index and height")
    module = "Parallel.LeafVisibility"
    common["facade"]["run"](["lake", "build", module], lean)
    common["facade"]["audit_theorems"](module, ["slhdsa.ParallelLeafTable.node_law", "slhdsa.ParallelLeafTable.leaves_spec", "slhdsa.ParallelLeafTable.visible_leaves"])
    common["facade"]["audit_theorems"](module, ["slhdsa.ParallelXmssTicket." + n for n in
        ("subtree_spec", "leaf_spec", "linux_subtree", "linux_leaf", "hosted_law", "hosted_subtree", "hosted_leaf",
         "layer_table", "subtree_from_layers", "leaf_from_layers", "wots_from_layers", "published_leaf_returns")])


if __name__ == "__main__":
    main()
