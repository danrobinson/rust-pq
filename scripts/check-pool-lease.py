#!/usr/bin/env python3
"""Follow rustc MIR operands across closure erasure, Job publication, capture and indirect call."""
import argparse
import re
import runpy
import subprocess
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parent.parent
facade = runpy.run_path(str(root / "scripts/check-platform-facade.py"))
guard = runpy.run_path(str(root / "scripts/check-pool-guard.py"))
reg = r"(_\d+)"
one = guard["one"]

def function(mir, header):
    return one(r"(?ms)^fn " + header + r" \{([^}]*?\n(?:.*?))^\}", mir)[1]

def rhs(body, output, pattern):
    # Follow unique SSA definitions and require the full right-hand side to match.
    matches = re.findall(r"(?m)^        " + re.escape(output) + r" = ([^\n]+);$", body)
    if len(matches) != 1:
        raise ValueError(f"missing or ambiguous MIR definition for {output}")
    m = re.fullmatch(pattern + r"(?: -> \[[^\]]+\])?", matches[0])
    if not m:
        raise ValueError(f"unexpected producer of {output}: {matches[0]}")
    return m

def field_names(source, struct):
    decl = source.split("struct " + struct + " {", 1)[1].split("\n}", 1)[0]
    return re.findall(r"(?m)^    (\w+):", decl)

def pool_cell(body, ptr, field):
    address = rhs(body, ptr, rf"UnsafeCell::<Option<pool::Job>>::get\(move {reg}\)")[1]
    rhs(body, address, rf"&\(\(\*_1\)\.{field}: core::cell::UnsafeCell<core::option::Option<pool::Job>>\)")

def term(op, *args):
    return "(." + op + (" " if args else "") + " ".join(map(str, args)) + ")"

def input_arg(var, *args):
    if var not in args:
        raise ValueError(f"MIR source {var} is not in function arguments {args}")
    return term("arg", args.index(var))

def project(mir, source):
    if field_names(source, "Job") != ["data","call","scrub"]:
        raise ValueError("review changed Job layout")
    cell = field_names(source, "Pool").index("job")
    claim = function(mir, r"pool::<impl at src/pool.rs:[^\n]+>::claim\(_1: &Pool, _2: usize, _3: bool, _4: &F\) -> Option<PoolGuard<'_>>")
    write = one(rf"(?m)^        \(\*{reg}\) = move {reg};$", claim)
    pool_cell(claim, write[1], cell)
    wrapped = rhs(claim, write[2], rf"Option::<pool::Job>::Some\(move {reg}\)")[1]
    job = rhs(claim, wrapped, rf"pool::Job \{{ data: move {reg}, call: move {reg}, scrub: copy _3 \}}")
    cast = rhs(claim, job[1], rf"core::ptr::const_ptr::<impl \*const F>::cast::<\(\)>\(copy {reg}\)")[1]
    raw = rhs(claim, cast, rf"&raw const \(\*{reg}\)")[1]
    rhs(claim, job[2], r"pool::PoolGuard::<'a>::claim::trampoline::<F> as unsafe fn\(\*const \(\)\) \(PointerCoercion\(ReifyFnPointer\(Unsafe\), Implicit\)\)")
    publish = term("pair", term("erase",term("addressOf",input_arg(raw,"_4"))), term("trampoline"))

    worker = function(mir, r"worker_once\(_1: &Pool, _2: &WorkerSlot\) -> \(\)")
    # Start at the caught callback, then resolve the exact fields of the copied Job.
    closure = one(rf"(?m)^        {reg} = \{{closure@([^}}]+)\}} \{{ job__data: move {reg}, job__call: move {reg} \}};$", worker)
    site = re.escape(closure[2])
    wrapper = one(rf"(?m)^        {reg} = AssertUnwindSafe::<\{{closure@{site}\}}>\(move {closure[1]}\);$", worker)[1]
    caught = one(rf"std::panic::catch_unwind::<AssertUnwindSafe<\{{closure@{site}\}}>, \(\)>\(move {wrapper}\)",worker)
    def captured(var, ty):
        f = rhs(worker,var,rf"&\({reg}\.(\d+): {ty}\)")
        unwrap = rhs(worker,f[1],rf"Option::<pool::Job>::expect\(move {reg}, move _\d+\)")[1]
        pointer = rhs(worker,unwrap,rf"copy \(\*{reg}\)")[1]
        pool_cell(worker,pointer,cell)
        return term("localRef",term("field",term("arg",0),f[2]))
    capture = term("pair",captured(closure[3],r"\*const \(\)"),captured(closure[4],r"unsafe fn\(\*const \(\)\)"))
    callback = function(mir,rf"worker_once::\{{closure#\d+\}}\(_1: &\{{closure@{site}\}}\) -> \(\)")
    enter = one(rf" = run_worker_job\(move {reg}, move {reg}\)",callback)
    def recover(var,ty):
        ref = rhs(callback,var,rf"copy \(\*{reg}\)")[1]
        f = rhs(callback,ref,rf"no_retag copy \(\(\*{reg}\)\.(\d+): &{ty}\)")
        return term("load",term("field",input_arg(f[1],"_1"),f[2]))
    forwarded = term("pair",recover(enter[1],r"unsafe fn\(\*const \(\)\)"),recover(enter[2],r"\*const \(\)"))
    runner = function(mir,r"run_worker_job\(_1: unsafe fn\(\*const \(\)\), _2: \*const \(\)\) -> \(\)")
    call = one(rf" = copy {reg}\(copy {reg}\)",runner)
    indirect = term("pair",input_arg(call[1],"_1","_2"),input_arg(call[2],"_1","_2"))

    trampoline = function(mir,r"trampoline\(_1: \*const \(\)\) -> \(\)")
    invoke = one(rf" = <F as Fn<\(\)>>::call\(copy {reg}, const \(\)\)",trampoline)
    live = rhs(trampoline,invoke[1],rf"&\(\*{reg}\)")[1]
    obj = rhs(trampoline,live,rf"copy {reg} as \*const F \(PtrToPtr\)")[1]
    reborrow = term("call",term("shared",term("castF",input_arg(obj,"_1"))))
    return (publish,capture,forwarded,indirect,reborrow), worker, caught[0]

def certificate(prog):
    return """import Parallel.PoolWorkerLease
open ParallelPool.Lease
def actual : Program := ⟨""" + ",\n".join(prog) + """⟩
example : actual = production := rfl
theorem exact (o : Object) : invoke actual o = some (.called o) := exact_object o
"""

def worker_graph(body, caught, source):
    blocks = {int(i): " ".join(text.split()) for i,text in
              re.findall(r"    bb(\d+)(?: \(cleanup\))?: \{(.*?)\n    \}",body,re.S)}
    def locate(pattern):
        return next_unique([(i,m) for i,text in blocks.items() for m in re.finditer(pattern,text)],pattern)
    copy, _ = locate(rf"{reg} = copy \(\*{reg}\); {reg} = const \"pool job present\"; {reg} = Option::<pool::Job>::expect\(move \1, move \3\)")
    catch, call = locate(rf"{reg} = " + re.escape(caught) + r" -> \[return: bb(\d+), unwind continue\]")
    switch = int(call[2])
    branch = re.fullmatch(rf"{reg} = discriminant\({call[1]}\); switchInt\(move \1\) -> \[1: bb(\d+), 0: bb(\d+), otherwise: bb(\d+)\];",blocks[switch])
    if not branch or "as Err" not in blocks[int(branch[2])]:
        raise ValueError("catch discriminant does not identify both ok and panic paths")
    remaining = field_names(source,"Pool").index("remaining")
    counter = rf"{reg} = &\(\(\*_1\)\.{remaining}: core::sync::atomic::Atomic<usize>\); "
    field = field_names(source,"WorkerSlot").index("state")
    status = rf"{reg} = &\(\(\*_2\)\.{field}: core::sync::atomic::Atomic<u32>\); "
    def operation(base, ordering, ty, method, argument):
        return locate(base + rf"{reg} = core::sync::atomic::Ordering::{ordering}; "
                      + rf"{reg} = Atomic::<{ty}>::{method}\(move \1, const {argument}, move \2\) -> \[return: bb(\d+),")
    mark, ma = operation(counter,"Relaxed","usize","fetch_or","1_usize")
    idle, st = operation(status,"Release","u32","store","pool::IDLE_SPIN")
    decrement, dec = operation(counter,"SeqCst","usize","fetch_sub","2_usize")
    finish, _ = locate(r"^return;$")
    if not re.search(r"(?m)^const IDLE_SPIN: u32 = 0;$",source):
        raise ValueError("review worker idle encoding")
    labels = {(catch,switch):"catchReturn", (switch,int(branch[2])):"panic", (switch,int(branch[3])):"ok",
              (mark,int(ma[4])):"markFailed", (idle,int(st[4])):"idle", (decrement,int(dec[4])):"decrement"}
    edges=[]
    synthetic=max(blocks)+1
    for pc, text in blocks.items():
        origin=pc
        if pc==copy:
            edges.append((pc,"copy",synthetic))
            origin,synthetic=synthetic,synthetic+1
        if pc==finish:
            edges.append((pc,"finish",synthetic))
            synthetic+=1
        for dst in map(int,re.findall(r"\bbb(\d+)\b",text)):
            if dst not in blocks:
                raise ValueError("unknown successor")
            edges.append((origin,labels.get((pc,dst),"other"),dst))
    if len(labels)!=6 or not all(label in {a for _,a,_ in edges} for label in labels.values()):
        raise ValueError("missing worker protocol edge")
    return edges

def next_unique(matches, context):
    if len(matches)!=1:
        raise ValueError(f"expected exactly one witness for {context}, got {len(matches)}")
    return matches[0]

def worker_certificate(edges):
    transitions = {
        ("waiting","copy"):"copied", ("copied","catchReturn"):"caught",
        ("caught","ok"):"normal", ("caught","panic"):"panicked", ("panicked","markFailed"):"flagged",
        ("normal","idle"):"idle false", ("flagged","idle"):"idle true",
        ("idle false","decrement"):"retired false", ("idle true","decrement"):"retired true",
        ("retired false","finish"):"finished false", ("retired true","finish"):"finished true",
    }
    visited={(0,"waiting")}
    todo=list(visited)
    while todo:
        pc,phase=todo.pop()
        for src,action,dst in edges:
            if src!=pc:
                continue
            outcome=phase if action=="other" else transitions.get((phase,action),"bad")
            if (dst,outcome) not in visited:
                visited.add((dst,outcome))
                todo.append((dst,outcome))
    graph=",".join(f"({s},.{a},{d})" for s,a,d in edges)
    cert=",".join(f"({i},.{p})" for i,p in sorted(visited))
    return f"""
open ParallelPool.Lease.Worker
def graph : List Edge := [{graph}]
def inv : Certificate := [{cert}]
theorem checked : Worker.check graph inv = true := by decide
theorem workerExit {{pc p hist d}} (path : Walk graph pc p hist) (exit : (pc,.finish,d)∈graph) :
    ∃ panicked, hist.filter (· != .other) = .decrement :: .idle :: resultEvents panicked :=
  finish_order checked path exit
"""

def check(mir, source, scratch):
    program, worker, caught = project(mir,source)
    edges = worker_graph(worker,caught,source)
    inp = certificate(program) + worker_certificate(edges)
    facade["run"](["lake","env","lean","--stdin"],root/"lean-hw",input=inp,text=True)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain",default="nightly-2026-09-17")
    args = parser.parse_args()
    facade["run"](["lake","build","Parallel.PoolWorkerLease"],root/"lean-hw")
    with tempfile.TemporaryDirectory(prefix="pool-lease-") as temp:
        scratch=Path(temp)
        mir = scratch/"pool.mir"
        subprocess.run(["cargo","+"+args.toolchain,"rustc","--locked","--features","parallel","--lib","--",
                        "-C","panic=unwind","--emit=mir="+str(mir)],cwd=root/"rust",check=True)
        check(mir.read_text(),(root/"rust/src/pool.rs").read_text(),scratch)
    facade["audit_theorems"]("Parallel.PoolLease",["ParallelPool.Lease."+n for n in
        ("exact_object","no_address_confusion","scoped_invocation")])
    print("Lean checked the actual borrowed closure route through the erased job and indirect trampoline.")

if __name__ == "__main__":
    main()
