"""Read the selected trait implementations and closure bodies from monomorphic Charon MIR."""
from pathlib import Path
import re
import runpy

low = runpy.run_path(str(Path(__file__).resolve().parents[1] / "peer-shake/lower.py"))
NAMES = ("sha3.proof_stream_api","sha3.default","digest.Update.chain","sha3.clone","sha3.update",
         "digest.ExtendableOutput.finalize_xof_into","sha3.finalize_xof","sha3.read",
         "sha3.update.call_mut","sha3.read.call_mut","sha3.block_api.update_blocks",
         "sha3.block_api.update_blocks.call_once")


def wiring(j):
    if j["has_errors"]:raise ValueError("Charon reported errors")
    ir=j["translated"]; fns=ir["fun_decls"]; tys=ir["type_decls"]
    vals={}
    def dedup(node):
        if isinstance(node,list):
            for x in node:dedup(x)
        elif isinstance(node,dict):
            if set(node)=={"Value"} and isinstance(node["Value"],list) and len(node["Value"])==2:
                k,v=node["Value"]
                if isinstance(v,list) and len(v)==2 and isinstance(v[0],dict) and set(v[0]) & {"Bool","Discriminant"}:
                    vals[k]=v[0]
            for x in node.values():dedup(x)
    dedup(j)

    def const(c):
        if "Value" in c:v=c["Value"][1][0]
        else:v=vals[c["Deduplicated"]]
        if "Bool" in v:return str(v["Bool"])
        (ty,i)=v["Discriminant"]
        if low["path"](tys[ty["id"]])!="core.option.Option":raise ValueError("unknown discriminant")
        return ["None","Some"][i]

    def place(p):
        p=p["kind"]
        if "Local" in p:return "_"+str(p["Local"])
        base,proj=p["Projection"];base=place(base)
        if proj=="Deref":return "(*"+base+")"
        (variant,index)=proj["Field"]
        return base+"."+("" if variant is None else f"v{variant}.")+str(index)

    def operand(o):
        tag,v=next(iter(o.items()))
        if tag in ("Move","Copy"):return place(v[0] if isinstance(v,list) else v)
        if tag=="Const":return const(v)
        raise ValueError(o)

    def body(b):
        out=[]
        for stmt in b["statements"]:
            k=stmt["kind"]
            if k=="Return":out.append("return _0");continue
            tag,x=next(iter(k.items()))
            if tag in ("StorageLive","StorageDead"):continue
            if tag=="Borrowck" and set(x)=={"FakeRead"}:continue
            if tag=="Drop":
                out.append("drop "+place(x["place"])+" via "+low["path"](fns[x["fn_ptr"]["kind"]["Fun"]]))
            elif tag=="Assign":
                a,b=x;op,v=next(iter(b.items()))
                if op=="Use":rhs=operand(v[0])
                elif op=="Ref":rhs="&"+place(v["place"])
                elif op=="Aggregate":
                    ty,variant,union=v[0]["Adt"]
                    if variant is not None or union is not None:raise ValueError(v)
                    name=low["path"](tys[ty["id"]]) if ty.get("builtin") is None else ty["builtin"]
                    rhs=name+"("+", ".join(map(operand,v[1]))+")"
                else:raise ValueError(op)
                out.append(place(a)+" = "+rhs)
            elif tag=="Call":
                f=x["call"]["func"]
                if "Regular" in f:
                    name=low["path"](fns[f["Regular"]["kind"]["Fun"]])
                else:
                    name="invoke "+operand(f["Dynamic"][0])
                out.append(place(x["dest"])+" = "+name+"("+", ".join(map(operand,x["call"]["args"]))+")")
            elif tag=="Loop":out.extend(["loop",*["  "+l for l in body(x)],"end"])
            elif tag=="Switch":
                sw=x["data"]
                if sw["fallback"] is not None:raise ValueError("unexpected fallback")
                out.append("match "+place(sw["scrutinee"]["Discriminant"]))
                for cond,case in sw["branches"]:out.extend([const(cond)+":", *["  "+l for l in body(x["branches"][case])]])
                out.append("end")
            elif tag in ("Break","Continue") and x==0:out.append(tag.lower())
            else:raise ValueError(tag)
        return out
    out=[]
    for name in NAMES:
        fn,=[f for f in fns if f and low["path"](f)==name]
        b=fn["body"]["Structured"];out.extend([name+" / "+str(b["locals"]["arg_count"]),*["  "+l for l in body(b["body"])],""])
    return "\n".join(out)
