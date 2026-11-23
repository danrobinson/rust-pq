"""Bind the Rust slice flatten and fixed-array iterators used by the peer's SHAKE recipes."""
from pathlib import Path
import re
import runpy

PROOFS = Path(__file__).parent
reader = runpy.run_path(str(PROOFS / "reader.py"))
SHAPES=((16,35),(16,14),(16,33),(24,51),(24,17),(24,33),(32,67),(32,22),(32,35))


def append_roots(lib, append):
    append(lib,(PROOFS / "parts.rs").read_text())
    for n,length in SHAPES:
        src=(PROOFS / "items.rs").read_text().replace("ROOT",f"proof_rows_{n}_{length}")
        append(lib,src.replace("PARAM_N",str(n)).replace("PARAM_L",str(length)))


def inspect(text, pointer_bits=64, wasm=False):
    stream=reader["canonical"](text,"proof_peer_parts",("%msg.0","%msg.1","%0"))
    expected=(PROOFS / ("parts-wasm.ll" if wasm else "parts.ll")).read_text().strip()
    if pointer_bits==32 and not wasm:
        expected=expected.replace("[16 x i8]","[8 x i8]").replace("align 8","align 4").replace(", i64 8",", i32 4").replace("i64","i32")
    if stream!=expected:
        raise ValueError("changed nested-slice traversal or callback operands")
    for n,length in SHAPES:
        graph=reader["D"]["blocks"](reader["D"]["body"](text,f"proof_rows_{n}_{length}"))
        rows(graph,n,length,pointer_bits)


def rows(graph,n,length,bits):
    """Evaluate every iteration for the actual fixed extent, validating every callback."""
    reg=r"%[\w.]+"
    scalar=r"("+reg+r"|\d+)"
    word=f"i{bits}"
    pointers={"%rows":0}
    regs={}
    def get(v):
        return regs[v] if v.startswith("%") else int(v)
    previous,block=None,"start"
    visits=[]
    visited=set()
    for _ in range(2*length+2):
        visited.add(block)
        ops=graph[block]
        for op in ops[:-1]:
            if m:=re.fullmatch(r"("+reg+r") = getelementptr inbounds nuw i8, ptr ("+reg+r"), "+word+" "+scalar,op):
                off=pointers[m[2]]+get(m[3])
                if not 0<=off<=n*length:raise ValueError(op)
                pointers[m[1]]=off
            elif m:=re.fullmatch(r"tail call void %0\(ptr noundef nonnull readonly dereferenceable\((\d+)\) ("+reg+"), "+word+r" noundef (\d+)\) #\d+",op):
                off=pointers[m[2]]
                if int(m[1])!=n or int(m[3])!=n or off+n>n*length:raise ValueError(op)
                visits.append(off)
            elif m:=re.fullmatch(r"("+reg+") = phi "+word+r" \[ 0, %(\w+) \], \[ ("+reg+r"), %([\w.]+) \]",op):
                if previous not in (m[2],m[4]):raise ValueError(op)
                regs[m[1]]=0 if previous==m[2] else get(m[3])
            elif m:=re.fullmatch(r"("+reg+") = add nuw nsw "+word+" "+scalar+r", (\d+)",op):
                value=get(m[2])+int(m[3])
                if not 0<=value<2**(bits-1):raise ValueError(op)
                regs[m[1]]=value
            elif m:=re.fullmatch(r"("+reg+") = icmp eq "+word+" "+scalar+r", (\d+)",op):
                regs[m[1]]=get(m[2])==int(m[3])
            else:
                raise ValueError(op)
        op=ops[-1]
        if op=="ret void":
            if visits!=[i*n for i in range(length)] or visited!=set(graph):
                raise ValueError("incomplete or unordered fixed-array hash traversal")
            return
        if m:=re.fullmatch(r"br label %([\w.]+)",op):
            target=m[1]
        elif m:=re.fullmatch(r"br i1 ("+reg+r"), label %([\w.]+), label %([\w.]+)",op):
            target=m[2] if regs[m[1]] else m[3]
        else:raise ValueError(op)
        previous,block=block,target
    raise ValueError("fixed-array traversal did not terminate")
