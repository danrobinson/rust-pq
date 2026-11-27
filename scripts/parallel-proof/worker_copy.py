"""Connect all post-join branches of the full extraction to the proved byte copy."""

import re
import textwrap


def copy_witness(generated):
    prefix = "shake.slh.parallel.sign_loop"
    caller = generated.split("def shake.slh.parallel.sign\n", 1)[1]
    branches = re.findall(
        r"(?m)^( *let o ← std\.sync\.once_lock\.OnceLock\.get sig_fors_cell\n[\s\S]*?ok \(some signature3\))",
        caller,
    )
    if not branches or len(branches) != caller.count("pool.execute"):
        raise ValueError("unmatched post-join caller branch")
    out = [
        "namespace slhdsa.WorkerEffects\nopen Aeneas Aeneas.Std Result ControlFlow\nset_option backward.isDefEq.respectTransparency false\n"
    ]
    for i, branch in enumerate(branches):
        (name,) = re.findall(re.escape(prefix) + r"(\d+) \{ start :=", branch)
        fn = prefix + name
        # Import exactly the two loops that the generated caller runs. Resolve
        # the OnceLocks against a snapshot taken after every callback returns.
        loops = re.findall(
            r"^def (" + re.escape(fn) + r"(?:_loop0)?(?:\.body)?)(\n[\s\S]*?)(?=\n\n)",
            generated,
            re.MULTILINE,
        )
        if len(loops) != 4:
            raise ValueError("missing emitted post-join copy loop")
        local = f"copyBranch{i}"

        def snapshot(s):
            return (
                s.replace(
                    "std.sync.once_lock.OnceLock.get",
                    "_root_.slhdsa.ParallelSignJoin.readCell",
                )
                .replace("std.sync.once_lock.OnceLock", "Option")
                .replace(fn, local)
            )

        for header, definition in loops:
            out.append(snapshot("def " + header + definition) + "\n")
        body = textwrap.indent(textwrap.dedent(branch), "  ")
        out.append(f"""def {local}_tail {{N : Std.Usize}} (p : params.Params)
    (r : Array Std.U8 N) (d hp : Std.Usize)
    (sig_fors_cell : Option (alloc.vec.Vec Std.U8))
    (xmss_auth_cell : Option (alloc.vec.Vec (Array Std.U8 N)))
    (wots_sigs : alloc.vec.Vec (Option (alloc.vec.Vec Std.U8))) :
    Result (Option (alloc.vec.Vec Std.U8)) := do
{snapshot(body)}

theorem {local}_loop_matches {{N : Std.Usize}} (it : core.ops.range.Range Std.Usize) (hp : Std.Usize)
    (wots : alloc.vec.Vec (Option (alloc.vec.Vec Std.U8))) (auth : alloc.vec.Vec (Array Std.U8 N))
    (signature : alloc.vec.Vec Std.U8) :
    {local} it hp wots auth signature = _root_.slhdsa.ParallelSignJoin.run_loop0 it hp wots auth signature := rfl

theorem {local}_reads_final_heap {{N : Std.Usize}} (p : _root_.slhdsa.params.Params)
    (md : Slice Std.U8) (sk seed : Array Std.U8 N) (addr : _root_.slhdsa.address.Adrs)
    (r : Array Std.U8 N) (tree : Std.U64) (leaf : Std.U32) (threads : Std.Usize)
    (h : ParallelWorkerHeap.Heap N) (on : ¬ threads < 2#usize) (width : p.hp ≠ 0#u32) :
    _root_.slhdsa.ParallelSignJoin.run (ok threads) (_root_.slhdsa.WorkerPayload.heapJoin h) p md sk seed addr r tree leaf =
    {local}_tail (stagedParams p) r (UScalar.cast .Usize p.d) (UScalar.cast .Usize p.hp)
      (h.cells .sigFors) (h.cells .xmssAuth) (_root_.slhdsa.WorkerPayload.wotsView p h) := by
  have get : _root_.slhdsa.WorkerPayload.heapJoin h p md sk seed addr r tree leaf threads =
      ok (h.cells .sigFors,h.cells .xmssAuth,_root_.slhdsa.WorkerPayload.wotsView p h) := by
    simp [_root_.slhdsa.WorkerPayload.heapJoin] <;> rfl
  have size : params.Params.sig_bytes (stagedParams p) = _root_.slhdsa.params.Params.sig_bytes p := by
    simp only [params.Params.sig_bytes,params.Params.fors_sig_bytes,params.Params.xmss_sig_bytes,
      params.Params.len,params.LEN2,_root_.slhdsa.params.Params.sig_bytes,
      _root_.slhdsa.params.Params.fors_sig_bytes,_root_.slhdsa.params.Params.xmss_sig_bytes,
      _root_.slhdsa.params.Params.len,_root_.slhdsa.params.LEN2,stagedParams]
  simp only [_root_.slhdsa.ParallelSignJoin.run,bind_ok,on,width,ite_false,get,lift,
    {local}_tail,{local}_loop_matches,size] <;> rfl
""")
    out.append("end slhdsa.WorkerEffects")
    return "\n".join(out)
