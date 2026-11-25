#!/usr/bin/env python3
"""Re-extract all split-FORS queue metadata writes, reservations and per-lane loops."""
from pathlib import Path
import os
import re
import runpy
import tempfile

merge=runpy.run_path(str(Path(__file__).with_name("check-parallel-fors-merge.py")))
common,lean,decls=(merge[k] for k in ("common","lean","decls"))
names=("wide","group","scalar")


def project(src):
    sign=merge["ticket"]["shared"]["signer"].function(src,"sign").split("let run = ||")[0]
    start="fors_split_meta.push(ForsSplitMeta"
    if sign.count(start)!=3 or sign.count("fors_split_count +=")!=3:
        raise ValueError("expected exactly three metadata emissions and reservations")
    boundary=sign.split("if WIDTH == 8 {",1)[1]
    wide,rest=boundary.split("// Split tall FORS trees",1)
    group,scalar=rest.split("if !built_shake_simd_fors {",1)
    result=[]
    for name,body in zip(names,(wide,group,scalar)):
        target=re.search(r"let fors_target: u32 = (.*?);",body,re.S)
        if not target: raise ValueError("missing target calculation")
        result.append(f"fn target_{name}(a:u32)->u32 {{ "+target[1]+" }")
        arm=body.split("if split == 0 {",1)[1]
        direct,split=arm.split("} else {",1)
        if "WorkKind::Fors" not in direct or len(arm.split(start))!=2:
            raise ValueError("split predicate or associated direct record changed")
        before,after=split.split("let weight = 1u32 << fors_target;",1)
        context=body.split("if split == 0 {",1)[0]
        delta=re.findall(r"let split = [^;]+;",context)
        if len(delta)!=1: raise ValueError("ambiguous split declaration")
        chunks="let chunks = 1usize << split;"
        if name=="group":
            if context.count(chunks)!=1 or not re.search(r"for j in low_h\.\.a \{",context):
                raise ValueError("group count or height range changed")
            if not re.search(r"for c in 0\.\.chunks \{\s*jobs.push\(WorkItem \{\s*weight,\s*kind: WorkKind::ForsShakeSplit \{\s*first: first as u16,\s*active: active as u8,\s*height: j as u8,\s*sub_h: fors_target as u8,\s*chunk: c as u32,\s*split_base,\s*chunks,",after):
                raise ValueError("SIMD child no longer matches reservation")
            args="first:usize, active:usize"
            pre=delta[0]+chunks
        else:
            idx="let idx = fors_indices[t as usize];"
            root=re.findall(r"let root_idx = [^;]+;",context)
            if context.count(idx)!=1 or len(root)!=1 or not re.search(r"for t in 0\.\.p.k \{",context):
                raise ValueError("scalar tree or digit source changed")
            args="t:u32"
            pre=idx+root[0]+delta[0]
            if not re.search(r"for c in 0\.\.chunks \{\s*jobs.push\(WorkItem \{\s*weight,\s*kind: WorkKind::ForsNodeSplit \{\s*idx: \(root_idx << split\) \+ c as u32,\s*height: fors_target,\s*slot: slot_start \+ c,",after):
                raise ValueError("scalar child no longer matches reservation")
        result.append(f"""
fn meta_{name}(fors_indices:&Vec<u32>, a:u32,j:u32,fors_target:u32,mut fors_split_count:usize,{args},
    mut fors_split_meta:Vec<ForsSplitMeta>)->(usize,Vec<ForsSplitMeta>) {{
    {pre}
    {before}
    (fors_split_count,fors_split_meta)
}}
""")
    return src+"\n"+"\n".join(result)


def extract(folder,t,mutate=None):
    crate=common["copy_rust_crate"](folder)
    f=crate/"src/slh/parallel.rs"
    src=f.read_text()
    if mutate is not None:
        src=mutate(src)
    f.write_text(project(src))
    return common["extract_target"](t,folder/"generated",["crate::shake::slh::parallel::"+prefix+n for n in names for prefix in ("target_","meta_")],[],crate=crate,features="parallel,platform-sha2")


def program(pkg):
    if any(re.search(r"^axiom ", f.read_text(), re.M) for f in pkg.glob("*External_Template.lean")):
        raise ValueError("metadata producer unexpectedly cut an opaque dependency")
    types=decls(pkg/"Types.lean","CacheopsRust")
    meta,=types
    match=(lean/"Parallel/ForsMergeProgram.lean").read_text()
    if meta.replace("shake.slh.parallel.ForsSplitMeta","Meta") not in match:
        raise ValueError("producer and consumer metadata types differ")
    funcs=decls(pkg/"Funs.lean","CacheopsRust")
    if any(not re.search(r"\bdef shake.slh.parallel.(?:meta_|target_)",x) for x in funcs):
        raise ValueError("unexpected metadata dependency")
    raw="\n\n".join(funcs).replace("shake.slh.parallel.ForsSplitMeta","ParallelForsMerge.Meta").replace("shake.slh.parallel.","")
    return "import Parallel.ForsMergeProgram\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace slhdsa.ForsMetadata\n"+raw+"\nend slhdsa.ForsMetadata\n"

def mutation(src, site):
    prefix = "fors_split_meta.push(ForsSplitMeta {"
    chunks = src.split(prefix)
    if len(chunks)!=4:
        raise ValueError("unrecognized metadata push count")
    fields,tail=chunks[site+1].split("});",1)
    if fields.count("height: j,")!=1:
        raise ValueError("mutation cannot find the issued height")
    chunks[site+1]=fields.replace("height: j,","height: fors_target,")+"});"+tail
    return prefix.join(chunks)


def main():
    os.environ["PATH"]=f"{Path.home()}/.cargo/bin:{Path.home()}/.elan/bin:"+os.environ["PATH"]
    expected=(lean/"Parallel/ForsMetaProgram.lean").read_text().split()
    src=(lean.parent/"rust/src/slh/parallel.rs").read_text()
    for old,new in [
        ("slot: slot_start + c,","slot: slot_start,"),
        ("chunk: c as u32,","chunk: 0,"),
        ("fors_split_count += chunks;","fors_split_count -= chunks;"),
    ]:
        if old not in src:
            raise ValueError("missing source control "+old)
        try:
            project(src.replace(old,new))
        except ValueError:
            continue
        raise ValueError("accepted modified producer/child link "+new)
    with tempfile.TemporaryDirectory() as folder:
        for target in ("aarch64-apple-darwin","aarch64-unknown-linux-gnu","x86_64-unknown-linux-gnu"):
            pkg=extract(Path(folder)/target,target)
            if program(pkg).split()!=expected:
                raise ValueError("changed split metadata on "+target)
        for site,name in enumerate(names):
            pkg=extract(Path(folder)/name,"aarch64-unknown-linux-gnu",lambda src: mutation(src,site))
            if program(pkg).split()==expected:
                raise ValueError("accepted source mutant at "+name)
    module="Parallel.ForsMetaIssued"
    common["facade"]["run"](["lake","build",module],lean)
    common["facade"]["audit_theorems"](module,["slhdsa.ForsMetadata."+r for r in
                        ("targets","scalar","group","record_merge","scalar_cells","group_cells","scalar_issued","group_issued","partition","group_cast_geometry")])


if __name__=="__main__":
    main()
