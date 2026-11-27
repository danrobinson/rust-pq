#!/usr/bin/env python3
"""Bind the SIMD low FORS worker's ordered (slot, row) publication journal."""
from pathlib import Path
import os
import re
import runpy
import tempfile

shared = runpy.run_path(str(Path(__file__).with_name("check-parallel-fors-tickets.py")))
common, lean, decls = (shared[key] for key in ("common","lean","decls"))
stem = "crate::shake::slh::parallel::"
module = "shake.slh.parallel."
native = module+"shake_fors_simd."
cuts = ["crate::shake::batch::short_active","crate::shake::batch::pair_active",
        "crate::shake::fors_batch::fors_leaves_fused","crate::shake::fors_batch::fors_subtree_horiz"]


def extract(tmp,target):
    crate = common["copy_rust_crate"](tmp)
    path = crate/"src/slh/parallel.rs"
    src = path.read_text()
    group = re.search(r"^    ForsShakeLow \{([^}]+)\}",src,re.M)
    if not group or group[1].split() != "first: u16, active: u8, low_h: u8,".split():
        raise ValueError("low worker payload changed")
    work = shared["shared"]["shared"]["signer"].function(src,"sign").split("match item.kind {")[-1]
    code=work.split("WorkKind::ForsShakeLow {",1)[1].split("WorkKind::ForsShakeDirect {",1)[0]
    before,body=code.split("let first = first as usize;",1)
    expected='''first, active, low_h, } => { let _ = (first, active, low_h);
      shake_only! { #[cfg(any( all(target_arch = "aarch64", target_endian = "little"),
      all(target_arch = "x86_64", target_feature = "sse2") ))] {'''
    if before.split()!=expected.split() or not body.rstrip().endswith("}"):
        raise ValueError("worker arm or cfg guard changed")
    body,n=re.subn(r'\s*}\s*}\s*}\s*$',"",body)
    for name,value in (("sk","secret"),("low","sibs")):
        pattern=r'fors_direct\[([^\]]+)\]\s*\.set\('+value+r'\[lane\]\)\s*\.expect\("unique SHAKE FORS '+name+r' slot"\);'
        body,changed=re.subn(pattern,lambda m:"journal.push(("+m[1]+", "+value+"[lane]));",body)
        if changed!=1:
            raise ValueError(f"{name} row publication changed")
    if n!=1 or ".set(" in body:
        raise ValueError("unexpected publication or worker suffix")
    path.write_text(src+'''
shake_only! {
    fn low_ticket<const N: usize>(sk: &[u8; N], seed: &[u8; N], fors_addr: Adrs,
        fors_indices: &Vec<u32>, a: u32, first: u16, active: u8, low_h: u8, fors_stride: usize)
        -> Vec<(usize,[u8;N])> {
        let mut journal=Vec::new();
        let first=first as usize;
'''+body+'''
        journal
    }
}
''')
    return common["extract_target"](target,tmp/"generated",[stem+"low_ticket"],cuts,crate=crate,features="parallel,platform-sha2")


def program(pkg,width):
    text=[]
    extern=set(re.findall(r"^axiom ([\w.]+)",(pkg/"FunsExternal_Template.lean").read_text(),re.M))
    allowed={"core.array.Array.map",*(c.replace("crate::","").replace("::",".") for c in cuts)}
    if extern!=allowed:
        raise ValueError(f"unexpected native calls {extern ^ allowed}")
    w="@[global_simps, irreducible] def shake256.parallel.WIDTH : Std.Usize := "+str(width)+"#usize"
    seen=False
    for name in ("Types","Funs"):
        known=set(decls(lean.parent/f"lean/Slhdsa/{name}.lean","slhdsa"))
        for d in decls(pkg/(name+".lean"),"CacheopsRust"):
            if re.search(r"\bdef\s+"+re.escape(module),d):
                text.append(d)
            elif d==w:
                seen=True
            elif d not in known:
                raise ValueError("unbound dependency "+d)
    if not seen:
        raise ValueError("target width changed")
    raw="\n\n".join(text)
    for old,new in [(native+"nodes_active","nodes"),(native+"secrets","secrets"),(module+"low_ticket","ticket"),
                    ("shake.fors_batch.fors_subtree_horiz","wide.run"),
                    ("shake.batch.short_active","(ActiveHash.short_active host.perm)"),("shake.batch.pair_active","(ActiveHash.pair_active host.perm)"),
                    ("shake.fors_batch.fors_leaves_fused","(ForsFused.fused host.perm)"),("shake256.parallel.WIDTH","machine.width")]:
        raw=raw.replace(old,new)
    # Array capacity occurrences are monomorphized target constants. Preserve the algorithm's separate literal 8 comparison.
    wlit=str(width)+"#usize"
    for start in ("Array Std.U32 ", "(Array Std.U8 N) ", "N) ", "Array.repeat ", "core.array.from_fn "):
        raw=raw.replace(start+wlit, start+"machine.width")
    return """import Cachepath.NativeVerify.ActiveHashes
import Cachepath.NativeVerify.ForsFused
open Aeneas Aeneas.Std Result ControlFlow
namespace slhdsa.ParallelLowFors
open ShakeBatch NativeVerify
noncomputable section
class Wide where
  run {N : Usize} : Array U8 N → Array U8 N → address.Adrs → U32 → U32 → Result (Array U8 N)
class Host (m : Machine) where
  perm : Active m
variable [machine : Machine] [host : Host machine] [wide : Wide]

"""+raw+"\nend\nend slhdsa.ParallelLowFors\n"

def main():
    os.environ["PATH"] = f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:" + os.environ["PATH"]
    expected = (lean/"Parallel/LowForsProgram.lean").read_text().split()
    with tempfile.TemporaryDirectory() as folder:
        for target,width in [("aarch64-unknown-linux-gnu",3),("aarch64-apple-darwin",8),("x86_64-unknown-linux-gnu",8)]:
            pkg=extract(Path(folder)/target,target)
            if program(pkg,width).split()!=expected:
                raise ValueError(f"low FORS worker or cfg changed on {target}")
            path=pkg/"Funs.lean"
            source=path.read_text()
            for old,new in [
                ("with_keypair a addr.keypair","with_keypair a 0#u32"),
                ("i ^^^ 1#u32","i ^^^ 0#u32"),
                ("OrdUsize.min tupled_args i3","OrdUsize.min tupled_args 0#usize"),
                ("Vec.push journal (i1, a)","Vec.push journal (0#usize, a)"),
                ("Vec.push journal (i4, a)","Vec.push journal (0#usize, a)"),
                ("if level >= 3#u32","if level >= 2#u32"),
            ]:
                if source.count(old)!=1:
                    raise ValueError(f"mutation {old} no longer identifies one operation")
                path.write_text(source.replace(old,new))
                if program(pkg,width).split()==expected:
                    raise ValueError(f"accepted {new}")
            path.write_text(source)
    facade=shared["shared"]["shared"]["facade"]
    module="Parallel.LowForsHosted"
    facade["run"](["lake","build",module],lean)
    facade["audit_theorems"](module,["slhdsa.ParallelLowFors."+name for name in
                            ("absolute_indices","sibling_indices","nodes_spec","secrets_spec","slots_injective","ticket_spec",
                             "linux_spec","apple_spec","x86_spec")])


if __name__=="__main__":
    main()
