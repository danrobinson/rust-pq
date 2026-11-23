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


def inspect(text):
    stream=reader["canonical"](text,"proof_peer_parts",("%msg.0","%msg.1","%0"))
    if stream!=(PROOFS / "parts.ll").read_text().strip():
        raise ValueError("changed nested-slice traversal or callback operands")
    # Each selected output extent is constant; rustc emits each observed
    # endpoint callback separately. Decode every GEP and call in program order.
    for n,length in SHAPES:
        graph=reader["D"]["blocks"](reader["D"]["body"](text,f"proof_rows_{n}_{length}"))
        [ops]=graph.values()
        if ops[-1]!="ret void":
            raise ValueError("missing iterator return")
        offsets={"%rows":0}
        visits=[]
        for op in ops[:-1]:
            ptr=re.fullmatch(r"(%[\w.]+) = getelementptr inbounds nuw i8, ptr %rows, i64 (\d+)",op)
            if ptr:
                offsets[ptr[1]]=int(ptr[2])
                continue
            call=re.fullmatch(r"tail call void %0\(ptr noundef nonnull readonly dereferenceable\((\d+)\) (%[\w.]+), i64 noundef (\d+)\) #\d+",op)
            if not call or int(call[1])!=n or int(call[3])!=n:
                raise ValueError(op)
            visits.append(offsets[call[2]])
        if visits!=[i*n for i in range(length)]:
            raise ValueError("skipped, duplicated or reordered hash endpoint")
