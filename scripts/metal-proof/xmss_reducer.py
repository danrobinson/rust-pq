"""Project both XMSS MSL workgroup reductions into Lean. Fully match both body
grammars and extract the child/sibling arithmetic. Active levels execute with
the snapshot at the preceding barrier; per-lane memory effects, races and hash
bytes are checked independently by the workgroup and value replays."""
import re


def project(msl, shake, body, compact):
    word, width, size = ("uint64_t", "NL", 8) if shake else ("uint32_t", "NW", 4)
    prefix = "shake_" if shake else ""
    write = "write_shake_node_bytes" if shake else "write_node_bytes"
    pair = "shake_thash_pair" if shake else "thash_pair_words"
    shape = f"""
      if(tg_id>=p.num_trees)return;
      XmssTreeDesc desc=trees[tg_id];const device {"Shake" if shake else ""}KeyMaterial &km=keys[desc.key_idx];
      uint32_t leaf_base=tg_id*p.leaves_per_tree;uint32_t half_leaves=p.leaves_per_tree>>1;
      bool has_auth=(desc.target_leaf!=0xFFFFFFFFu);
      if(has_auth && tid==0u){{uint32_t sib0=desc.target_leaf ^ SIBu;
        uint32_t sib_off=(leaf_base+sib0)*{width}; {word} node[{width}];
        for(uint i=0;i<{width};++i)node[i]=leaves[sib_off+i]; {write}<{width}>(out_sigs+desc.auth_byte_off,node);}}
      {{{word} left[{width}],right[{width}],parent[{width}];
        uint32_t l_off=(leaf_base+CHILDREN u*tid)*{width};uint32_t r_off=(leaf_base+CHILDREN u*tid+RIGHTu)*{width};
        for(uint i=0;i<{width};++i){{left[i]=leaves[l_off+i];right[i]=leaves[r_off+i];}}
        {pair}<{width}>(km,desc.layer,desc.tree,ADRS_TREE,0u,1u,tid,left,right,parent);
        for(uint i=0;i<{width};++i){{tg_nodes[tid*{width}+i]=parent[i];}}}}
      threadgroup_barrier(mem_flags::mem_threadgroup);
      uint32_t cur_cnt=half_leaves>>1;
      for(uint32_t lvl=2u;lvl<=p.hp;++lvl){{
        if(has_auth){{uint32_t sib=(desc.target_leaf>>(lvl-1u)) ^ SIBu;
          if(tid==sib){{{write}_tg<{width}>(out_sigs+desc.auth_byte_off+(lvl-1u)*{width}*{size}u,tg_nodes+tid*{width});}}}}
        {word} parent[{width}];
        if(tid<cur_cnt){{{word} left[{width}],right[{width}];for(uint i=0;i<{width};++i){{
          left[i]=tg_nodes[(CHILDREN u*tid)*{width}+i]; right[i]=tg_nodes[(CHILDREN u*tid+RIGHTu)*{width}+i];}}
          {pair}<{width}>(km,desc.layer,desc.tree,ADRS_TREE,0u,lvl,tid,left,right,parent);}}
        threadgroup_barrier(mem_flags::mem_threadgroup);
        if(tid<cur_cnt){{for(uint i=0;i<{width};++i){{tg_nodes[tid*{width}+i]=parent[i];}}}}
        threadgroup_barrier(mem_flags::mem_threadgroup);cur_cnt>>=1;
      }}
      if(tid==0u){{uint32_t out_off=tg_id*{width};for(uint i=0;i<{width};++i){{out_roots[out_off+i]=tg_nodes[i];}}}}
    """
    pattern = re.escape(compact(shape))
    for name in ("CHILDREN", "RIGHT", "SIB"):
        pattern = pattern.replace(name, rf"(?P<{name}>[0-9]+)", 1).replace(name+"u", rf"(?P={name})u")
    parsed = re.fullmatch(pattern, compact(body(msl, f"void {prefix}xmss_reduce_impl(")))
    if not parsed:
        raise ValueError(f"{prefix}xmss_reduce: unmodeled reducer phase")
    n, right, sibling = (parsed.group(key) for key in ("CHILDREN", "RIGHT", "SIB"))
    stem = ("shake" if shake else "sha2")+"Xmss"
    args = "(p : Spec.Params) (keys : MetalChainDispatch.Keys) (trees : MetalChainDispatch.Trees) (words : Nat) (mem : MetalChainDispatch.Memory)"
    return f"""
private def {stem}State {args} (row : Nat) : Nat → Nat → Spec.Bytes
  | 0, tid => MetalLeafDispatch.readNode words mem (row*2^p.hp+tid)
  | level+1, tid =>
    let prior := {stem}State p keys trees words mem row level
    let d := trees row
    if tid < 2^(p.hp-(level+1)) then
      Spec.H p (keys d.keyIdx).2 ⟨d.layer,d.tree,Spec.TREE,0,level+1,tid⟩ (prior ({n}*tid) ++ prior ({n}*tid+{right}))
    else prior tid

private theorem {stem}State_spec {args} (row level tid : Nat) :
    {stem}State p keys trees words mem row level tid = MetalXmssDispatch.state p keys trees words mem row level tid := by
  induction level generalizing tid with
  | zero => rfl
  | succ level ih =>
    simp only [{stem}State,ih,MetalXmssDispatch.state,MetalPipeline.metalXmssReduceState,MetalPipeline.tgReduceStep,
      Spec.Adrs.setTypeAndClear]

private def {stem}Root {args} (row : Nat) := {stem}State p keys trees words mem row p.hp 0
private theorem {stem}Root_spec {args} (row : Nat) :
    {stem}Root p keys trees words mem row = MetalXmssDispatch.rootVal p keys trees words mem row :=
  {stem}State_spec p keys trees words mem row _ _
private def {stem}Auth {args} (row h : Nat) :=
    {stem}State p keys trees words mem row h ((((trees row).targetLeaf.getD 0) >>> h) ^^^ {sibling})
private theorem {stem}Auth_spec {args} (row h : Nat) :
    {stem}Auth p keys trees words mem row h = MetalXmssDispatch.authVal p keys trees words mem row h :=
  {stem}State_spec p keys trees words mem row _ _
"""


def public_parts(p, g, family, words, size, phase, count, xmss_cmd):
    field = f"MetalReducerBytes.Field {g} (MetalCommandValues.framed rs).length"
    args = f"""(rootBuf : MetalChainDispatch.Execution)
    (middle : List ({field})) (otherBytes : {field} → Spec.Byte)"""
    if phase:
        tips = f"(MetalLeafDispatch.run ({count}*{p}.len) {words} {size} ({family}ChainTip {p} e) e)"
        leaf = f"({family}BufferLeaf {p} e {words} {tips})"
    else:
        leaf = f"({family}StreamLeaf {p} e {words})"
    setup = f"""let leafMem := MetalLeafDispatch.run {count} {words} {size} {leaf} {"leaf" if phase else "e"}
    let rootValue := {family}XmssRoot {p} keys trees {words} leafMem
    let authValue := {family}XmssAuth {p} keys trees {words} leafMem
    let bytesAt := MetalXmssDispatch.values (p:={p}) (rs:=requests) authValue otherBytes
    let events := MetalReducerBytes.events middle bytesAt
    let rawWithRoots := {{raw with roots := MetalXmssDispatch.rootBuffer {p} requests.length {words} {size} rootValue rootBuf}}
    let remainder := fun r => if r = MetalCommand.Region.xmssAuth then True else unconstrained r
    """
    orders = f"""rootBuf.schedule.Perm (MetalChainDispatch.grid (requests.length*{p}.d) {words}) ∧
      (∀ w : {field}, MetalCommandValues.owner {g} w.val.2.1 = .xmssAuth → w ∈ middle) ∧"""
    return args, setup, orders, f"a ≠ {xmss_cmd} →"


def public_proof(label, p, g, family, words, size, phase, count, mode, names, cmd):
    return f"""
  intro requests keys trees e leafMem rootValue authValue bytesAt events rawWithRoots remainder
    data jobs initial other pkValue source rest buffers atByte toByte out inputsInv inv accepted
  apply {label}_host_values rs {"pre leaf" if phase else "pre"} remainder rawWithRoots
    roots pkBuf events capacity memory schedule
  intro guard
  obtain ⟨alloc,{", ".join(names.split())},cover,pkOrder,rootOrder,authCovered,remaining⟩ := accepted guard
  refine ⟨alloc,{",".join(names.split())},cover,pkOrder,?_⟩
  intro a ha {"hc " if phase else ""}hl hw hf hh
  by_cases eq : a = {cmd}
  · subst a
    have nr : requests.length = rs.length := by simp [requests,MetalCommandValues.framed]
    have descriptors := MetalHostValues.layers_spec {p} requests buffers rfl
    have leafInv : inv .xmss_leaves → MetalLeafDispatch.Matches (requests.length*{p}.d*2^{p}.hp)
        {words} {size} leafMem (MetalPipeline.metalXmssLeaves {mode} {p} keys trees) := by
      rw [nr]
      exact id
    have rule := MetalXmssDispatch.command {p} (MetalPipeline.metal_all_12_params_valid _ (by decide))
      {mode} requests {words} {size} (by decide) leafMem {g} (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      authValue ({family}XmssAuth_spec {p} keys trees {words} leafMem)
      rootValue ({family}XmssRoot_spec {p} keys trees {words} leafMem)
      rootBuf rootOrder atByte toByte schedule
      (fun w => ({family}SigAddr_spec buffers {words} (by decide) w).trans (MetalWotsOutput.shader_addr descriptors w))
      middle authCovered otherBytes (MetalHostValues.initMemory {p} requests memory) capacity (nr ▸ alloc)
      {cmd} (by decide) (by decide) inv leafInv id (by trivial)
    have span : requests.length*{p}.sigBytes = rs.length*{p}.sigBytes := congrArg (· * {p}.sigBytes) nr
    simpa only [span] using rule
  · exact remaining a ha {"hc " if phase else ""}hl hw hf hh eq
"""
