"""Check the specialized RustCrypto read loop and its invariant for arbitrary output sizes."""
from pathlib import Path
import re
import runpy

import z3

common=runpy.run_path(str(Path(__file__).with_name("eager.py")))
D,check=common["D"],common["requires"]


def canonical(text, entry="proof_read_output", args=("%out.0","%out.1","%0")):
    code=D["body"](text,entry)
    graph=D["blocks"](code)
    rename={k:f"B{i}" for i,k in enumerate(graph)}
    values=dict(zip(args, ("out","length","produce")))
    def state(m):
        v=m[0]
        if v[1:] in rename:return rename[v[1:]]
        return values.setdefault(v,"v"+str(len(values)-3))
    lines=[]
    for name,body in graph.items():
        lines.append(rename[name]+":")
        for line in body:
            line=re.sub(r" #\d+$","",line)
            line=re.sub(r"%[\w.]+",state,line)
            lines.append(line)
    return "\n".join(lines)


def inspect(text, prove=check):
    ir=canonical(text)
    # Track the local array's known alignment; it must suffice for the store
    # to its first byte. All external source and destination bytes are align 1.
    align=int(re.search(r"alloca \[136 x i8\], align (\d+)",ir)[1])
    if align not in (1,2,4,8,16):raise ValueError(align)
    expected=(Path(__file__).with_name("reader.ll")).read_text().strip().replace("$ALIGN",str(align))
    if ir!=expected:
        raise ValueError("unexpected LLVM operations in read buffer\n"+ir)
    n,k,j=z3.Ints("output_len completed_blocks index")
    q,r=n/136,n%136
    env={"guard":[n>=0,n<=2**63-1]}
    prove(env,z3.And(n==q*136+r,r>=0,r<136,(n<136)==(q==0)), "read entry and tail arithmetic")
    step={"guard":[*env["guard"],k>=0,k<q]}
    # Every iteration starts one pointer-width-aligned rate block after its
    # predecessor. The branch exactly detects the final iteration.
    prove(step,z3.And(k*136>=0,(k+1)*136<=n,
                      ((k+1)*136==n-r)==(k+1==q),q-k>q-(k+1)), "reader induction")
    prove(step,z3.Implies(z3.And(j>=0,j<136),
                          z3.And((k*136+j)/136==k,(k*136+j)%136==j)), "producer output order")
    prove(env,z3.Implies(z3.And(j>=0,j<r),z3.And(q*136+j<n,(q*136+j)/136==q,
                     (q*136+j)%136==j)), "last partial block")
