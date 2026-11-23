"""Symbolically execute the complete LLVM eager-update CFG, including its memory effects."""
import re
import runpy
from pathlib import Path

import z3

D = runpy.run_path(str(Path(__file__).resolve().parents[1] / "peer-shake/dispatch.py"))
REG = r"%[\w.]+"
INT = z3.IntSort()
BYTE = INT  # Data bytes are opaque here; unrestricted values strengthen the copy proof.
N, P, I = z3.Ints("n pos byte_index")
STATE = z3.Function("state", INT, BYTE)
INPUT = z3.Function("message", INT, BYTE)
MAX = 2**63-1


def requires(env, goal, label):
    solver = z3.Solver()
    solver.set(timeout=30_000)
    solver.add(*env["guard"], z3.Not(goal))
    status = solver.check()
    if status != z3.unsat:
        detail = solver.model() if status == z3.sat else solver.reason_unknown()
        raise ValueError(f"{label}: {status} {detail}")


def inspect(text):
    graph = D["blocks"](D["body"](text, "proof_eager_update"))
    signature = re.search(r"^define void @proof_eager_update\(([^\n]*)\) unnamed_addr", text, re.M)
    names = re.findall(REG, signature[1])
    if len(names)!=4:
        raise ValueError(signature[0])
    registers = dict(zip(names, (("state",0), ("input",0), N, "consumer")))
    paths = set()
    visited = set()

    def execute(bb, prev, env, seen):
        if bb in seen:
            raise ValueError("unexpected loop in eager buffer")
        visited.add(bb)
        env = {**env, "regs":env["regs"].copy(), "guard":list(env["guard"]), "events":list(env["events"])}
        regs = env["regs"]

        def scalar(v, bits):
            if v.startswith("%"):
                return regs[v]
            return z3.IntVal(int(v) % (1<<bits))

        def limit(region):
            return 136 if region=="state" else N

        def load(region, at):
            return env["buf"](at) if region=="state" else INPUT(at)

        for line in graph[bb]:
            if (m:=re.fullmatch(r"("+REG+r") = (getelementptr inbounds(?: nuw)? i8), ptr ("+REG+r"), i64 ("+REG+r"|\d+)",line)):
                q,_,base,off=m.groups()
                region,ptr=regs[base]; new=ptr+scalar(off,64)
                requires(env,z3.And(0<=new,new<=limit(region)),line)
                regs[q]=region,new
            elif (m:=re.fullmatch(r"("+REG+r") = load i8, ptr ("+REG+r"), align 1",line)):
                q,p=m.groups();region,ptr=regs[p]
                requires(env,z3.And(0<=ptr,ptr<limit(region)),line)
                regs[q]=load(region,ptr)
            elif (m:=re.fullmatch(r"("+REG+r") = (zext i8|trunc(?: nuw)? i64) ("+REG+r") to i(64|8)",line)):
                q,op,v,bits=m.groups();x=regs[v]
                if "nuw" in op:
                    requires(env,x<256,line)
                regs[q]=x if bits=="64" else x%256
            elif (m:=re.fullmatch(r"("+REG+r") = (icmp(?: samesign)? (?:ult|eq)) i(8|64) ("+REG+r"|-?\d+), ("+REG+r"|-?\d+)",line)):
                q,op,bits,a,b=m.groups();a,b=scalar(a,int(bits)),scalar(b,int(bits))
                if "samesign" in op:
                    requires(env,(a<2**(int(bits)-1))==(b<2**(int(bits)-1)),line)
                regs[q]=a<b if op.endswith("ult") else a==b
            elif (m:=re.fullmatch(r"tail call void @llvm.assume\(i1 ("+REG+r")\)",line)):
                requires(env,regs[m[1]],line)
            elif (m:=re.fullmatch(r"("+REG+r") = (add|sub|mul|udiv|urem)((?: nuw| nsw)*) i(8|64) ("+REG+r"|\d+), ("+REG+r"|\d+)",line)):
                q,op,flags,bits,a,b=m.groups();bits=int(bits);a,b=scalar(a,bits),scalar(b,bits)
                x={"add":lambda:a+b, "sub":lambda:a-b, "mul":lambda:a*b, "udiv":lambda:a/b,"urem":lambda:a%b}[op]()
                if op in ("udiv","urem"):
                    requires(env,b>0,line)
                if flags:
                    bound=1<<(bits-(1 if "nsw" in flags else 0))
                    requires(env,z3.And(0<=x,x<bound),line)
                if flags or op in ("udiv","urem"):
                    regs[q]=x
                else:
                    regs[q]=x%(1<<bits)
            elif (m:=re.fullmatch(r"("+REG+r") = phi (?:i64|ptr) (.*)",line)):
                choices = re.findall(r"\[ ("+REG+r"), %([\w.]+) \]",m[2])
                if len(choices)!=2 or m[2] != ", ".join(f"[ {v}, %{b} ]" for v,b in choices):
                    raise ValueError(line)
                regs[m[1]]=regs[{b:v for v,b in choices}[prev]]
            elif (m:=re.fullmatch(r"tail call void @llvm.memcpy.p0.p0.i64\(ptr ([^,]+), ptr ([^,]+), i64 (?:range\(i64 0, -9223372036854775808\) )?("+REG+r"), i1 false\)",line)):
                dest,src,count=m.groups(); dest,d=regs[dest.split()[-1]];src,s=regs[src.split()[-1]];n=regs[count]
                if dest!="state" or src!="input":
                    raise ValueError("unexpected aliasing in "+line)
                requires(env,z3.And(0<=s,0<=d,0<=n,s+n<=N,d+n<=136),line)
                old=env["buf"]
                env["buf"]=lambda i,d=d,s=s,n=n,old=old:z3.If(z3.And(d<=i,i<d+n),INPUT(s+i-d),old(i))
            elif (m:=re.fullmatch(r"store i8 ("+REG+r"|0), ptr ("+REG+r"), align 1",line)):
                value,p=m.groups();region,d=regs[p];x=scalar(value,8)
                if region!="state":raise ValueError(line)
                requires(env,z3.And(0<=d,d<136),line)
                old=env["buf"]
                env["buf"]=lambda i,d=d,x=x,old=old:z3.If(i==d,x,old(i))
            elif (m:=re.fullmatch(r"tail call void ("+REG+r")\(ptr ([^,]+), i64 noundef (?:range\(i64 1, \d+\) )?("+REG+r"|1)\) #\d+",line)):
                callback,addr,count=m.groups(); region,d=regs[addr.split()[-1]];count=scalar(count,64)
                if regs[callback]!="consumer":raise ValueError(line)
                requires(env,z3.And(count>0,d>=0,d+136*count<=limit(region)),line)
                env["events"].append((count,d,env["buf"] if region=="state" else INPUT))
            elif (m:=re.fullmatch(r"br i1 ("+REG+r"), label %([\w.]+), label %([\w.]+)",line)):
                cond=regs[m[1]]
                for child,c in [(m[2],cond), (m[3],z3.Not(cond))]:
                    execute(child,bb,{**env,"guard":env["guard"]+[c]},seen+[bb])
                return
            elif (m:=re.fullmatch(r"br label %([\w.]+)",line)):
                execute(m[1],bb,env,seen+[bb])
                return
            elif line=="ret void":
                paths.add(tuple(seen+[bb]))
                full=lambda i:z3.If(i<P,STATE(i),INPUT(i-P))
                used=0
                for count,offset,read in env["events"]:
                    size=count*136
                    requires(env,z3.Implies(z3.And(0<=I,I<size),read(offset+I)==full(used+I)), "incorrect emitted byte")
                    used+=size
                rem=(N+P)%136
                requires(env,used==N+P-rem,"incorrect emitted length")
                requires(env,z3.And(env["buf"](135)==rem,
                              z3.Implies(z3.And(0<=I,I<rem),env["buf"](I)==full(used+I))),"incorrect buffered suffix")
                return
            else:
                raise ValueError(line)
        raise ValueError("missing terminator: "+bb)

    execute("start",None,{"regs":registers,"buf":STATE,"guard":[N>=0,N<=MAX,P>=0,P<136,STATE(135)==P],"events":[]},[])
    if set(graph)!=visited or len(paths)!=5:
        raise ValueError(f"unverified control flow: {visited}, {len(paths)} paths")
    return len(paths)
