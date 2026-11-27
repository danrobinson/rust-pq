#!/usr/bin/env python3
"""Bind the native reduction loops on six hosted family/configuration pairs."""
from pathlib import Path
import hashlib
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-parallel-fors-tickets.py")))
common, lean, decls = (shared[key] for key in ("common","lean","decls"))
opening = """import Slhdsa.Proofs.ShakeXmss
import Shakebatch.Range
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelReduceNative
noncomputable section
class Family where
  Seed : Usize → Type
  hash {N : Usize} : Seed N → address.Adrs → Array U8 N → Array U8 N → Result (Array U8 N)
variable [family : Family]

def getCell {α : Type} (cell : Option α) : Result (Option α) := ok cell

def truncate {α : Type} (v : alloc.vec.Vec α) (n : Usize) : Result (alloc.vec.Vec α) :=
  ok (alloc.vec.Vec.from (v.val.take n.val) ((List.length_take_le ..).trans (by scalar_tac)))

"""
collect = """
/-- Read-only slots retain slice order. Iterator allocation and Rust's OnceLock memory
ordering are modeled at this boundary. Each element still runs the extracted expect closure. -/
def collectRows {N : Usize} (slots : Slice (Option (Array U8 N))) : Result (alloc.vec.Vec (Array U8 N)) := do
  let xs ← slots.val.mapM (fun slot => do
    let (v,_) ← reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N.call_mut (N:=N) () slot
    ok v)
  if h : xs.length ≤ Usize.max then ok (alloc.vec.Vec.from xs h) else fail .panic

"""
prefix = """let i ← core.slice.Slice.iter slots
  let m ← core.iter.traits.iterator.Iterator.map.default
      (core.iter.traits.iterator.IteratorSliceIter (Option (Array Std.U8 N)))
      (reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N N) i ()
  let cur ← core.iter.traits.iterator.Iterator.collect.default
      (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      (core.iter.traits.iterator.IteratorSliceIter (Option (Array Std.U8 N)))
      (reduce_tree.closure.Insts.CoreOpsFunctionFnMutTupleShared0OnceLockArrayU8NArrayU8N N))
      (core.iter.traits.collect.FromIteratorVec (Array Std.U8 N)) m"""


def program(pkg, shake):
    family = "shake." if shake else ""
    name = family+"slh.parallel.reduce_tree"
    defs = []
    for file in ("Types","Funs"):
        known = set(decls(lean.parent/f"lean/Slhdsa/{file}.lean","slhdsa"))
        for d in decls(pkg/(file+".lean"),"CacheopsRust"):
            if re.search(r"\bdef\s+"+re.escape(name),d):
                defs.append(d)
            elif "impl_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator" in d:
                if hashlib.sha256(" ".join(d.split()).encode()).hexdigest() != "6c02372d233ea860b70594f1bfe1f02d4efac46dbf717686b466f7cfcb0f00a4":
                    raise ValueError("Iterator<Map> adapter changed")
            elif d not in known:
                raise ValueError(f"unknown dependency {d}")
    extern = set(re.findall(r"^axiom ([\w.]+)",(pkg/"FunsExternal_Template.lean").read_text(),re.M))
    if extern != {"core.iter.traits.iterator.Iterator.map.default","core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next",
                  "std.sync.once_lock.OnceLock.get","alloc.vec.Vec.truncate",family+"xmss.hash2"}:
        raise ValueError(f"unexpected imports {extern}")
    imported_types = set(re.findall(r"^axiom ([\w.]+)", (pkg/"TypesExternal_Template.lean").read_text(), re.M))
    if imported_types != {"std.sync.once_lock.OnceLock"}:
        raise ValueError(f"unexpected types {imported_types}")
    raw = "\n\n".join(defs).replace(name,"reduce_tree")
    for old,new in [("std.sync.once_lock.OnceLock.get","getCell"),("std.sync.once_lock.OnceLock","Option"),
                    ("alloc.vec.Vec.truncate alloc.alloc.Global","truncate"),(family+"xmss.hash2","family.hash"),
                    (("(seed : Array Std.U8 N)" if shake else "(seed : hash.Seed N)"),"(seed : family.Seed N)")]:
        raw=raw.replace(old,new)
    before, tail=raw.split("let i ← core.slice.Slice.iter slots")
    reads, tail=tail.split("  let i1 ← sub_h + 1#u32")
    if ("let i ← core.slice.Slice.iter slots"+reads).split()!=prefix.split():
        raise ValueError("read-only iterator, closure or collect order changed")
    raw = before+"let cur ← collectRows slots\n  let i1 ← sub_h + 1#u32"+tail
    marker = "@[rust_loop_body]\ndef reduce_tree_loop0_loop0.body"
    if raw.count(marker)!=1:
        raise ValueError("expected exactly one parent loop")
    return opening+raw.replace(marker,collect+marker)+"\nend\nend slhdsa.ParallelReduceNative\n"


def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    expected = (lean/"Parallel/ReduceNativeProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as d:
        for t in ("aarch64-apple-darwin","x86_64-unknown-linux-gnu","aarch64-unknown-linux-gnu"):
            for shake in (False,True):
                mod = "crate::"+("shake::" if shake else "")
                pkg = common["extract_target"](t,Path(d)/(t+str(shake)),[mod+"slh::parallel::reduce_tree"],
                                              [mod+"xmss::hash2"],features="parallel,platform-sha2")
                if program(pkg,shake).split()!=expected:
                    raise ValueError(f"changed {mod} reducer on {t}")
                if t == "aarch64-apple-darwin" and shake:
                    path = pkg / "Funs.lean"
                    original = path.read_text()
                    for old, new in [
                        ("hash2 seed a1 a2 a3", "hash2 seed a1 a3 a2"),
                        ("2#usize * idx", "1#usize * idx"),
                        ("root_idx <<< shift", "root_idx >>> shift"),
                        ("cur1 next_len", "cur1 0#usize"),
                        ("FromIteratorVec (Array Std.U8 N)) m","FromIteratorVec (Array Std.U8 N)) i"),
                    ]:
                        if original.count(old) != 1:
                            raise ValueError(f"could not locate mutation {old}")
                        path.write_text(original.replace(old,new))
                        try:
                            actual = program(pkg,shake)
                        except ValueError:
                            continue
                        if actual.split() == expected:
                            raise ValueError(f"accepted mutation {new}")
                    path.write_text(original)
    facade=shared["shared"]["shared"]["facade"]
    facade["run"](["lake","build","Parallel.ReduceNative"],lean)
    facade["audit_theorems"]("Parallel.ReduceNative",["slhdsa.ParallelReduceNative."+r for r in
                              ("published_layer","reduce_spec","shake_xmss","sha2_xmss","shake_fors","sha2_fors")])


if __name__=="__main__":
    main()
