#!/usr/bin/env python3
"""Check the Arm recovery wrapper, scheduler, and physical WOTS lane routes."""
import re
import runpy
import shutil
import subprocess
import tempfile
from pathlib import Path

here = Path(__file__).resolve().parent
facade = runpy.run_path(str(here / "check-platform-facade.py"))
root, lean = facade["ROOT"], facade["LEAN"]
program_path = lean / "Armwide/RecoveryRoutesProgram.lean"

def rust_function(text, name):
    start = re.search(r"\bfn " + name + r"\b", text).start()
    left = text.index("{",start)
    depth = 1
    for i in range(left+1,len(text)):
        if text[i]=="{":
            depth+=1
        if text[i]=="}":
            depth-=1
            if depth==0:
                return text[start:i+1]
    raise ValueError(name)

def native_routes(tmp,src):
    rust=rust_function(src,"wots_recover_active")
    tail=rust.split("    while active > 0 {",1)[1].split("        let mut k = 0;",1)[0]
    tail=tail[tail.index("        if active == 3"):]
    bulk=rust[ rust.index("        run_shared4_steps::<N>("): ].split("        for l in 0..4",1)[0]
    helpers=[rust_function(src,n).replace("super::K","K") for n in ("load_shared_head","run_shared4_steps")]
    helpers[0]=re.sub(r"vld1q_u32\((head\.(?:m0|a1|e1))\.as_ptr\(\)\)",r"\1",helpers[0])
    probe=(here/"arm-wots/hash-routes.rs").read_text().replace("// PRODUCTION","\n".join(helpers))
    probe=probe.replace("let hash_head = Head","let head = Head")
    probe=probe.replace("// TAIL_HASH",tail).replace("// SHARED_HASH","let min_left=steps;"+bulk)
    probe=probe.replace("// MIXED_HASH",'unreachable!()').replace("for active in 1..=4","for active in 1..=3")
    path=tmp/"routes.rs"
    path.write_text(probe)
    subprocess.run(["rustc","-Awarnings",path,"-o",tmp/"routes"],check=True)
    lines=subprocess.check_output([tmp/"routes"],text=True).splitlines()
    widths=[]
    for n in (16,24,32):
        routes=[]
        for active,k in [(a,1) for a in range(1,4)]+[(4,s) for s in range(1,16)]:
            for lane in range(active):
                header,ops=lines.pop(0).split("|")
                fields=list(map(int,header.split()))
                if fields[:5]!=[n,active,k,int(active==4),lane]:
                    raise ValueError("missing native recovery lane")
                calls=[]
                for item in filter(None,ops.split(";")):
                    head,chain,counter,high=map(int,item.split(","))
                    if bool(high)!=(n!=16):
                        raise ValueError("high register feed-forward width mismatch")
                    calls.append((head,chain,counter//32-1,counter%32))
                routes.append((fields[-1],calls))
        widths.append(routes)
    if lines or widths[1:]!=widths[:1]*2:
        raise ValueError("width-dependent physical recovery routing")
    rows=[]
    for origin,calls in widths[0]:
        ops=",".join("⟨"+",".join(map(str,op))+"⟩" for op in calls)
        rows.append(f"  ⟨{origin},[{ops}]⟩,")
    return "\n".join(["-- Generated from the Arm recovery hot and tail hash calls.",
        "import Armwide.TransitionTypes","namespace slhdsa.Armwide.Recovery",
        "def routes : Array Transitions.HashTrace := #["]+rows+["]","end slhdsa.Armwide.Recovery",""])

def native_control(tmp, src):
    rust = rust_function(src, "wots_recover_active")
    tokens = lambda t: re.findall(r"::|\.\.|[A-Za-z0-9_]+|[^\s]", re.sub(r"//[^\n]*", "", t))
    def guard(actual, expected):
        if tokens(actual) != tokens(expected):
            raise ValueError("unprojected Arm WOTS recovery control or pointer expression changed")
    setup = rust.split("let mut order =", 1)[1].split("run_shared4_steps", 1)[0]
    guard(setup, """
        [0u8; LEN_MAX]; let total=sort_descending(&rem_weights[..len],&mut order);
        if total==0 {return;} let head=unsafe {make_head(state,adrs)}; let z=vdupq_n_u32(0);
        let mut x=[z;4]; let mut xb=[z;4]; let mut chain=[0usize;4]; let mut cur_t=[0u32;4]; let mut left=[0u32;4];
        let mut active=0usize; let mut next=0usize;
        while active<4 && next<total {let c=order[next] as usize; next+=1;
          let(vx,vxb)=unsafe{load_n::<N>(&sig[c*N..])};x[active]=vx;xb[active]=vxb;
          chain[active]=c;cur_t[active]=digits[c];left[active]=15-digits[c];active+=1;}
        while active==4 {let min_left=left[0].min(left[1]).min(left[2]).min(left[3]);""")
    shell = rust_function(src, "wots_recover").split("{", 1)[1]
    guard(shell, "debug_assert!(available());unsafe {wots_recover_active::<N>(state,adrs,sig,digits,buf)};}")
    bulk, tail = rust.split("    while active > 0 {")
    hot = bulk[bulk.index("        for l in 0..4",bulk.index("run_shared4_steps")):].rstrip()
    tail = tail[tail.index("        let mut k = 0;"):].rstrip()
    if not hot.endswith("\n    }") or not tail.endswith("\n    }\n}"):
        raise ValueError("unexpected recovery outer loop structure")
    fresh = """
        let nc=order[next] as usize; next+=1; let(vx,vxb)=unsafe{load_n::<N>(&sig[nc*N..])};
        x[l]=vx;xb[l]=vxb;chain[l]=nc;cur_t[l]=digits[nc];left[l]=15-digits[nc];
    """
    store = "let c=chain[l];unsafe{store_n::<N>(&mut buf[22+c*N..],x[l],xb[l])};"
    compact = "x[k]=x[l];xb[k]=xb[l];chain[k]=chain[l];cur_t[k]=cur_t[l];left[k]=left[l];k+=1;"
    guard(hot, "for l in 0..4 {cur_t[l]+=min_left;left[l]-=min_left;if left[l]==0 {"+store+
          "if next<total {"+fresh+"}}} if left[0]==0 || left[1]==0 || left[2]==0 || left[3]==0 {"+
          "let mut k=0;for l in 0..4{if left[l]>0{"+compact+"}}active=k;}}")
    guard(tail, "let mut k=0;for l in 0..active{cur_t[l]+=1;left[l]-=1;if left[l]==0{"+
          store+"}else{"+compact+"}}active=k;}}")
    guard(rust.split("while active > 0 {")[1].split("if active == 3",1)[0],
          "let k_ptr=core::hint::black_box(super::K.as_ptr());")
    code=(here/"arm-wots/recovery-control.rs").read_text().replace("// HOT",hot[:-5]).replace("// TAIL",tail[:-7])
    path=tmp/"control.rs"
    path.write_text(code)
    subprocess.run(["rustc","-Awarnings",path,"-o",tmp/"control"],check=True)
    lines=iter(subprocess.check_output([tmp/"control"],text=True).splitlines())
    origin=[61,3,47,8,56,23,0,64]
    widths=[]
    for n in (16,24,32):
        rows=[]
        for active in range(1,5):
            for mask in range(1<<active):
                for q in range(5 if active==4 else 1):
                    heading, writes, consumed, output = next(lines).split("|")
                    if tuple(map(int,heading.split(","))) != (n,active,mask,q):
                        raise ValueError("incomplete recovery lane control coverage")
                    stores=[]
                    for triple in filter(None,writes.split(";")):
                        off,lo,hi=map(int,triple.split(","))
                        lane=lo-100
                        if lane not in range(active) or hi!=200+lane or off!=22+origin[lane]*n:
                            raise ValueError("recovery store offset or digest bank mismatch")
                        stores.append(lane)
                    live=[int(x) for x in output.split(";") if x]
                    rows.append((active,mask,q,live,int(consumed),stores))
        widths.append(rows)
    if next(lines,None) is not None or widths[1:]!=widths[:1]*2:
        raise ValueError("width-dependent physical recovery lane control")
    rows=[f"  ({a},{m},{q},{live},{num},{w})," for a,m,q,live,num,w in widths[0]]
    return "\n".join(["-- Generated from the production Arm recovery retire/refill and compaction statements.",
        "namespace slhdsa.Armwide.Recovery",
        "def controlRows : List (Nat × Nat × Nat × List Nat × Nat × List Nat) := ["]+
        rows+["]","end slhdsa.Armwide.Recovery",""])

def fresh_wrappers(tmp, target):
    crate=tmp/"crate"
    crate.mkdir()
    for name in ("Cargo.toml","Cargo.lock","rust-toolchain.toml"):
        if (root/"rust"/name).exists(): shutil.copy(root/"rust"/name,crate/name)
    shutil.copytree(root/"rust/src",crate/"src")
    (crate/"benches").mkdir()
    (crate/"benches/platforms.rs").touch()
    path=crate/"src/sha256/arm_wide.rs"
    src=path.read_text()
    prep=rust_function(src,"wots_recover_active").split("{",1)[1].split("let mut order =",1)[0]
    path.write_text(src+"\npub(crate) fn prepare_recovery<const N:usize>(digits:&[u32],sig:&[u8],buf:&mut[u8])->[u32;LEN_MAX]{"+prep+"rem_weights}\n")
    declarations,body=(facade["common"][k] for k in ("declarations","body"))
    shared=set(declarations(body(lean/"Slhdsa/Funs.lean")))
    types=set(declarations(body(lean/"Slhdsa/Types.lean")))
    for name,entry,cuts,model in (
        ("Prep","sha256::arm_wide::prepare_recovery",(),"RecoveryPreProgram"),
        ("Wrap","wots::arm::recover",("wots::arm::compress_tlen_1","wots::arm::wots_digits_stack","sha256::arm_wide::wots_recover"),"RecoveryProgram"),
        ("Gate","wots::wots_pk_from_sig",("sha256::arm_wide::available","wots::arm::recover","wots::wots_digits","hash::chain_blocks","hash::thash_values","hash::short_block","util::block"),"RecoveryDispatch"),
    ):
        package=facade["extract"](crate,target,name,tmp,["crate::"+entry],["crate::"+x for x in cuts])
        text=(lean/"Armwide"/(model+".lean")).read_text()
        if set(declarations(body(package/"Types.lean")))-types: raise ValueError(f"{target}: unexpected types")
        fresh=set(declarations(body(package/"Funs.lean")))
        selected=[d for d in fresh if "def "+entry.replace("::",".")+"\n" in d]
        if len(selected)!=1: raise ValueError(f"{target}: missing entry {entry}")
        for decl in fresh-shared:
            decl=decl.replace("sha256.arm_wide.prepare_recovery","prepare").replace("wots.arm.compress_tlen_1","Keygen.wots.arm.compress_tlen_1") if name!="Gate" else decl
            if decl in text: continue
            if name=="Gate" and re.sub(r"wots_pk_from_sig_loop[01]","wots_pk_from_sig_loop",decl) in shared: continue
            raise ValueError(f"{target}/{name}: unmatched source {decl[:110]}")
    print(f"{target}: replayed Arm recovery wrapper, prepass and full dispatcher",flush=True)

def main():
    src=(root/"rust/src/sha256/arm_wide.rs").read_text()
    with tempfile.TemporaryDirectory() as work:
        previous=runpy.run_path(str(here/"check-arm-wots-transitions.py"))
        for kernel,model in (("load_program","LoadProgram"),("store_program","StoreProgram"),("pack_program","PackProgram")):
            if previous[kernel](Path(work),src)!=(lean/"Armwide"/(model+".lean")).read_text():
                raise ValueError(f"stale shared recovery primitive {model}")
        actual=native_routes(Path(work),src)
        if actual!=program_path.read_text():
            raise ValueError("Arm recovery hash routes changed")
        control=native_control(Path(work),src)
        if control!=(lean/"Armwide/RecoveryControlProgram.lean").read_text():
            raise ValueError("Arm recovery register refill or compaction changed")
        for target in ("aarch64-apple-darwin","aarch64-unknown-linux-gnu"):
            tmp=Path(work)/target
            tmp.mkdir()
            fresh_wrappers(tmp,target)
    facade["run"](["lake","build","Armwide.RecoveryDispatch","Armwide.RecoveryControl"],lean)
    facade["audit_theorems"]("Armwide.RecoveryDispatch",["slhdsa.Armwide.Recovery.Dispatcher.dispatch_eq_scalar"])
    facade["audit_theorems"]("Armwide.RecoveryControl",["slhdsa.Armwide.Recovery.control_complete","slhdsa.Armwide.Recovery.plan_retire","slhdsa.Armwide.Recovery.plan_queue_suffix"])
    print("All Arm WOTS recovery source checks passed.")

if __name__=="__main__":
    main()
