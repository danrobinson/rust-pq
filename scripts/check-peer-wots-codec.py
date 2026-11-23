#!/usr/bin/env python3
"""Check actual release-object WOTS parsing, byte order, and all rejected input lengths."""
from pathlib import Path
import os
import re
import runpy
import subprocess
import tempfile

locked=runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))
ROOT=locked["ROOT"]
decode=runpy.run_path(str(ROOT/"scripts/peer-shake/dispatch.py"))
SUITES=runpy.run_path(str(ROOT/"scripts/check-peer-wots.py"))["SUITES"]
TARGETS=("aarch64-apple-darwin","aarch64-unknown-linux-gnu","x86_64-unknown-linux-gnu","wasm32-unknown-unknown",
         "powerpc64-unknown-linux-gnu","i686-unknown-linux-gnu","x86_64-unknown-none")


def prepare(path):
    locked["unpack"](path,"slh-dsa","0.2.0-rc.5")
    template=(ROOT/"scripts/peer-wots/encode.rs").read_text()
    for name,(ty,n) in SUITES.items():
        k=2*n+3
        entry=template.replace("DECODE","checked_decode_"+name).replace("ENCODE","checked_encode_"+name)
        entry=entry.replace("PEER_TYPE",ty).replace("PARAM_N",str(n)).replace("PARAM_ROWS",str(k)).replace("PARAM_SIZE",str(k*n))
        locked["common"]["append"](path/"src/wots.rs",entry)


def verify(ir,name,n,bits):
    size=n*(2*n+3)
    for op in ("encode","decode"):
        entry="checked_"+op+"_"+name
        alias=re.search(r"^@"+entry+r" = [^\n]*alias (?:void|i1) \([^\n]*\), ptr @(\w+)$",ir,re.M)
        if alias:entry=alias[1]
        g=decode["blocks"](decode["body"](ir,entry))
        def copied(line,source):
            p=r"tail call void @llvm.memcpy.p0.p0.i"+str(bits)+r"\(ptr noundef nonnull align 1 dereferenceable\("+str(size)+r"\) %output, ptr noundef nonnull (?:readonly )?align 1 dereferenceable\("+str(size)+r"\) "+re.escape(source)+r", i"+str(bits)+" "+str(size)+r", i1 false\)"
            if not re.fullmatch(p,line):raise ValueError(line)
        if op=="encode":
            if list(g)!=["start"] or len(g["start"])!=2 or g["start"][-1]!="ret void":raise ValueError(entry)
            copied(g["start"][0],"%input")
        else:
            if len(g)!=3 or len(g["start"])!=2:raise ValueError(entry)
            pred=re.fullmatch(r"(%[\w.]+) = icmp eq i"+str(bits)+r" %input.1, "+str(size),g["start"][0])
            if not pred:raise ValueError(g["start"][0])
            branches=re.fullmatch(r"br i1 "+re.escape(pred[1])+r", label %([\w.]+), label %([\w.]+)",g["start"][1])
            if not branches:raise ValueError(g["start"][1])
            yes,end=branches.groups()
            if len(g[yes])!=2 or g[yes][1]!="br label %"+end or g[end]!=["ret i1 "+pred[1]]:raise ValueError(entry)
            copied(g[yes][0],"%input.0")


def main():
    os.environ["PATH"]=str(Path.home()/".cargo/bin")+os.pathsep+os.environ["PATH"]
    with tempfile.TemporaryDirectory(prefix="peer-wots-codec-") as d:
        p=Path(d)
        prepare(p)
        for t in TARGETS:
            subprocess.run(["cargo","rustc","--release","--lib","--locked","--target",t,"--","--emit=llvm-ir"],cwd=p,check=True)
            [file]=list((p/"target"/t/"release").rglob("slh_dsa-*.ll"))
            ir=file.read_text()
            for name,(_,n) in SUITES.items():verify(ir,name,n,32 if t.startswith(("wasm32","i686")) else 64)
            print(t+": checked all 24 WOTS typed serialization and parsing bodies",flush=True)


if __name__=="__main__":
    main()
