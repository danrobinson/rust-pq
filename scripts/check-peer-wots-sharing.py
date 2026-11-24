#!/usr/bin/env python3
"""Compare actual WOTS release control flow at the primitive cut across all twelve suites."""
import os
from pathlib import Path
import re
import runpy
import subprocess
import tempfile

locked=runpy.run_path(str(Path(__file__).with_name("peer-lock.py")))
ROOT=locked["ROOT"]
WOTS=ROOT/"scripts/peer-wots"
suite=runpy.run_path(str(ROOT/"scripts/check-peer-wots.py"))["SUITES"]
D=runpy.run_path(str(ROOT/"scripts/peer-shake/dispatch.py"))
TARGETS=("aarch64-apple-darwin","x86_64-unknown-linux-gnu","aarch64-unknown-linux-gnu","wasm32-unknown-unknown",
         "powerpc64-unknown-linux-gnu","i686-unknown-linux-gnu","x86_64-unknown-none")


def prepare(p):
    locked["unpack"](p,"slh-dsa","0.2.0-rc.5")
    append=locked["common"]["append"]
    append(p/"src/lib.rs",(WOTS/"oracles.rs").read_text())
    for family in ("sha2","shake"):
        file=p/"src/hashes"/(family+".rs")
        src=file.read_text()
        operands={"f":"adrs.as_ref().as_ptr(), m.as_ptr()",
                  "prf_sk":"adrs.as_ref().as_ptr(), sk_seed.as_ref().as_ptr()",
                  "t":"adrs.as_ref().as_ptr(), m.as_ptr().cast::<u8>(), m.len()"}
        for name,args in operands.items():
            op="prf" if name=="prf_sk" else name
            pat=r"(    fn "+name+r"(?:<[^>]*>)?\([^{}]*?\) -> Array<u8, Self::N> \{)"
            cut=("""
                let mut out=Array::<u8, Self::N>::default();
                unsafe { crate::traced_"""+op+"(core::ptr::from_ref(self).cast(), "+args+""", out.len(), out.as_mut_ptr()) };
                return out;""")
            src,count=re.subn(pat,lambda m:m[1]+cut,src)
            if count!=(2 if family=="sha2" else 1):raise ValueError("unrecognized hash provider")
        file.write_text(src)
    wo=p/"src/wots.rs"
    cut="""
        #[cfg(cut_wots_chain)] {
            let mut out=Array::<u8, Self::N>::default();
            unsafe { crate::traced_chain(core::ptr::from_ref(self).cast(), adrs.as_ref().as_ptr(),
                                         x.as_ptr(), i, s, out.len(), out.as_mut_ptr()) };
            return out;
        }"""
    src,count=re.subn(r"(    fn wots_chain\(.*?\) -> Array<u8, Self::N> \{)",lambda m:m[1]+cut,wo.read_text(),flags=re.S)
    if count!=1:raise ValueError("unrecognized WOTS chain")
    wo.write_text(src)
    for name,(ty,n) in suite.items():
        src=(WOTS/"roots.rs").read_text().replace("SUFFIX",name).replace("TYPE",ty)
        append(wo,src.replace("NBYTES",str(n)).replace("SIZE",str(n*(2*n+3))))


def canonical(ir, name):
    alias=re.search(r"^@"+re.escape(name)+r" = [^\n]*alias void \([^\n]+\), ptr @(whole_\w+)$",ir,re.M)
    if alias:name=alias[1]
    header=re.search(r"^define (?:dso_local )?void @"+re.escape(name)+r"\(([^\n]*)\) unnamed_addr",ir,re.M)
    if not header:raise ValueError("missing WOTS body: "+name)
    # Match function arguments by position, never by order of first use. The
    # opaque provider receiver must only be forwarded to a traced hash call.
    arguments=re.findall(r"%[\w.]+",header[1])
    if arguments[0]!="%h":raise ValueError(header[0])
    regs={v:"arg"+str(i) for i,v in enumerate(arguments)}
    body=D["body"](ir,re.escape(name))
    def metadata(m):
        tag,num=m.groups()
        if tag in ("noalias","alias.scope","inline_history"):return ""
        if tag=="noundef" and re.search(r"^!"+num+r" = !\{\}$",ir,re.M):return " [noundef]"
        raise ValueError("unrecognized semantic instruction metadata "+m[0])
    body=re.sub(r", !(\w+(?:\.\w+)*) !(\d+)",metadata,body)
    if ", !" in body:raise ValueError("uninterpreted LLVM metadata")
    graph=D["blocks"](body)
    labels={k:"B"+str(i) for i,k in enumerate(graph)}
    signature,changed=re.subn(r"align \d+ (captures\([^)]+\)) dereferenceable\(\d+\) %h,",r"valid-context \1 %h,",header[1],count=1)
    if changed!=1:raise ValueError(header[0])
    lines=[signature]
    for block,seq in graph.items():
        lines.append(labels[block]+":")
        for line in seq:
            if "%h" in re.findall(r"%[\w.]+",line):
                use=r"(@traced_(?:prf|f|t|chain)\()ptr noundef nonnull readonly align (\d+) dereferenceable\((\d+)\) %h,"
                m=re.search(use,line)
                if not m or line.count("%h,")!=1:raise ValueError("WOTS read its abstract receiver: "+line)
                # The two families have different layouts, but neither WOTS
                # algorithm accesses that storage. Their own valid &P meets
                # its respective Rust reference precondition at this call.
                line=re.sub(use,r"\1ptr valid %h,",line)
            def reg(m):
                v=m[0]
                if v[1:] in labels:return labels[v[1:]]
                return regs.setdefault(v,"v"+str(len(regs)))
            lines.append(re.sub(r"%[\w.]+",reg,line))
    return lines


def main():
    os.environ["PATH"]=str(Path.home()/".cargo/bin")+os.pathsep+os.environ["PATH"]
    with tempfile.TemporaryDirectory(prefix="peer-wots-objects-") as directory:
        p=Path(directory)
        prepare(p)
        for target in TARGETS:
            for mode in ("native","cut"):
                build=p/mode
                env=os.environ.copy()
                if mode=="cut":env["RUSTFLAGS"]=(env.get("RUSTFLAGS","")+" --cfg cut_wots_chain").strip()
                subprocess.run(["cargo","rustc","--lib","--release","--locked","--target",target,
                                "--target-dir",build,"--","--emit=llvm-ir"],env=env,cwd=p,check=True)
                [file]=list((build/target/"release").rglob("slh_dsa-*.ll"))
                ir=file.read_text()
                for bits in (128,192,256):
                    for op in ("pk","sign","recover","chain"):
                        representative=canonical(ir,f"whole_{op}_shake_{bits}f")
                        for family in ("sha2","shake"):
                            for variant in ("f","s"):
                                if canonical(ir,f"whole_{op}_{family}_{bits}{variant}")!=representative:
                                    raise ValueError(f"distinct {op} object at {bits}, {family}{variant}, {target}, {mode}")
                print(target,mode,"all four WOTS operations use three width-specialized programs across twelve suites",flush=True)


if __name__=="__main__":
    main()
