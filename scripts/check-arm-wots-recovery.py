#!/usr/bin/env python3
"""Check the Arm recovery wrapper, scheduler, and physical WOTS lane routes."""
import re
import runpy
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

def main():
    src=(root/"rust/src/sha256/arm_wide.rs").read_text()
    with tempfile.TemporaryDirectory() as work:
        actual=native_routes(Path(work),src)
        if actual!=program_path.read_text():
            raise ValueError("Arm recovery hash routes changed")
    print("All Arm recovery hash routes matched.")

if __name__=="__main__":
    main()
