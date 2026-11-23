"""Decode the optimized scalar Keccak-f[1600] loop and all 25 loop-carried lanes."""
import re

REG = r"%[A-Za-z0-9_.]+"
LABEL = r"[A-Za-z0-9_.]+"


def llvm_string(raw):
    chars = re.findall(r"\\[a-fA-F0-9]{2}|[^\\]",raw)
    if "".join(chars) != raw:
        raise ValueError("unexpected LLVM string escape")
    return bytes(int(c[1:],16) if c.startswith("\\") else ord(c) for c in chars)


def decode(text):
    function = re.search(r"^define void @proof_scalar_keccak\(ptr [^\n]*dereferenceable\(200\) ("+REG+r")\)[^\n]*\{\n(.+?)^\}",text,re.M|re.S)
    if not function:
        raise ValueError("missing scalar permutation entry")
    base, code = function.groups()
    blocks = {}
    for line in code.splitlines():
        line = re.sub(r"\s*;.*$","",line.strip())
        if not line:
            continue
        if line.endswith(":"):
            block = line[:-1]
            blocks[block]=[]
        else:
            blocks[block].append(re.sub(r", ![^\n]*$","",line))
    if len(blocks)!=3:
        raise ValueError(f"unexpected scalar permutation CFG {blocks.keys()}")
    entry,loop,exit_ = blocks
    addr = {base:0}
    words = {}
    def check(condition,detail):
        if not condition:
            raise ValueError(detail)
    for line in blocks[entry]:
        if (m:=re.fullmatch(r"("+REG+r") = getelementptr inbounds(?: nuw)? i8, ptr ("+REG+r"), i64 (\d+)",line)):
            q,p,k=m.groups();addr[q]=addr[p]+int(k)
        elif (m:=re.fullmatch(r"("+REG+r") = load i64, ptr ("+REG+r"), align 8",line)):
            q,p=m.groups();check(addr[p]%8==0,"unaligned input");words[q]=addr[p]//8
        elif line.startswith("tail call void @llvm.experimental.noalias.scope.decl(metadata "):
            continue
        elif line != "br label %"+loop:
            raise ValueError(line)
    check(blocks[entry][-1]=="br label %"+loop,"entry target")
    check(set(words.values())==set(range(25)),"missing lane load")
    regs = {}
    latches = {}
    definitions=[]
    table=offset=next_offset=condition=table_ptr=None
    def val(op):
        return regs[op] if op in regs else {"-1":"(~~~(0 : Lane))"}[op]
    advanced = False
    for line in blocks[loop]:
        if (m:=re.fullmatch(r"("+REG+r") = phi i64 \[ ("+REG+r"|0), %"+re.escape(entry)+r" \], \[ ("+REG+r"), %"+re.escape(loop)+r" \]",line)):
            q,start,latch=m.groups()
            if start=="0":
                check(offset is None,"duplicate index")
                offset,next_offset=q,latch
            else:
                lane=words[start]
                check(lane not in latches or latches[lane] == latch,"inconsistent duplicated SSA lane")
                regs[q]=f"a[{lane}]!"
                latches[lane]=latch
        elif (m:=re.fullmatch(r"("+REG+r") = (xor|and) i64 ("+REG+r"), ("+REG+r"|-1)",line)):
            q,op,l,r=m.groups()
            expr = f"~~~({val(l)})" if op=="xor" and r=="-1" else f"{val(l)} {'^^^' if op=='xor' else '&&&'} {val(r)}"
            regs[q]=f"v{len(definitions)}";definitions.append((regs[q],expr))
        elif (m:=re.fullmatch(r"("+REG+r") = tail call(?: noundef)? i64 @llvm.fshl.i64\(i64 ("+REG+r"), i64 ("+REG+r"), i64 (\d+)\)",line)):
            q,a,b,n=m.groups();check(a==b and int(n)<64,"not a rotation")
            regs[q]=f"v{len(definitions)}";definitions.append((regs[q],f"({val(a)}).rotateLeft {n}"))
        elif (m:=re.fullmatch(r"("+REG+r") = getelementptr inbounds(?: nuw)? i8, ptr (@\w+), i64 ("+REG+r")",line)):
            q,table,index=m.groups();check(index==offset,"unexpected round constant address");table_ptr=q
        elif (m:=re.fullmatch(r"("+REG+r") = add (?:nuw nsw |nuw |nsw )?i64 ("+REG+r"), 8",line)):
            check(not advanced and m.groups()==(next_offset,offset),"wrong loop advance")
            advanced = True
        elif (m:=re.fullmatch(r"("+REG+r") = load i64, ptr ("+REG+r"), align 8",line)):
            check(m[2]==table_ptr,"wrong round constant read");regs[m[1]]="rc"
        elif (m:=re.fullmatch(r"("+REG+r") = icmp eq i64 ("+REG+r"), 192",line)):
            condition,test=m.groups();check(test==next_offset,"wrong termination check")
        elif line != f"br i1 {condition}, label %{exit_}, label %{loop}":
            raise ValueError(line)
    check(blocks[loop][-1]==f"br i1 {condition}, label %{exit_}, label %{loop}","wrong branch")
    check(advanced and set(latches)==set(range(25)) and None not in (offset,next_offset,condition,table,table_ptr),"incomplete loop")
    stores={}
    for line in blocks[exit_]:
        if line=="ret void":
            continue
        if (m:=re.fullmatch(r"("+REG+r") = getelementptr inbounds(?: nuw)? i8, ptr ("+REG+r"), i64 (\d+)",line)):
            q,p,k=m.groups(); addr[q]=addr[p]+int(k)
            continue
        m=re.fullmatch(r"store i64 ("+REG+r"), ptr ("+REG+r"), align 8",line)
        check(m is not None,"unexpected store "+line)
        v,p=m.groups()
        check(addr[p]%8==0 and addr[p]//8 not in stores,"duplicate/unaligned output")
        stores[addr[p]//8]=v
    check(blocks[exit_][-1]=="ret void" and stores==latches,"stores and carried state disagree")
    m=re.search(r"^"+re.escape(table)+r' = [^\n]*constant \[192 x i8\] c"([^"]+)", align 8',text,re.M)
    check(m is not None,"missing round constants")
    endian = re.search(r'^target datalayout = "([eE])',text,re.M)[1]
    data = llvm_string(m[1])
    check(len(data)==192,"invalid table")
    keys=[int.from_bytes(data[i:i+8],"little" if endian=="e" else "big") for i in range(0,192,8)]
    return definitions,[regs[latches[i]] for i in range(25)],keys


def program(text):
    lets,output,keys=decode(text)
    code="import Spec.ShakeWords\nopen Spec.Keccak\nnamespace PeerKeccak.Soft\n\ndef round (a : State) (rc : Lane) : State :=\n"
    code+="".join(f"  let {name} := {expr}\n" for name,expr in lets)
    code+="  #["+",".join(output)+"]\n\n"
    code+="def constants : Array Lane := #[\n  "+",\n  ".join(f"0x{k:016x}" for k in keys)+"]\n"
    code+="\ndef permute (a : State) : State := constants.foldl round a\nend PeerKeccak.Soft\n"
    return code
