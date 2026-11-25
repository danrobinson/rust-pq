"""Leaf kernel projections for Lean. Match complete MSL bodies including each
stream read and store. Cryptographic stream primitives use the independent
CBMC transcript checker in check-metal-values.py."""
import re


def kernel_body(shake, streaming):
    words, word, prefix, seed = (
        ("NL", "uint64_t", "shake_", "pk_seed") if shake else
        ("NW", "uint32_t", "", "seed_st")
    )
    source = """
        uint32_t total_leaves = p.num_trees * p.leaves_per_tree;
        if (gid >= total_leaves) return;
        uint32_t leaf_idx = gid LEAFOP p.leaves_per_tree;
        uint32_t tree_idx = gid TREEOP p.leaves_per_tree;
        XmssTreeDesc desc = trees[tree_idx];
    """
    if streaming:
        source += (
            """uint64_t pk_seed[NL], sk_seed[NL];
               for (uint i=0;i<NL;++i) {
                 pk_seed[i] = keys[desc.key_idx].pk_seed[i];
                 sk_seed[i] = keys[desc.key_idx].sk_seed[i];
               }""" if shake else
            """uint32_t seed_st[8]; uint32_t sk_seed[NW];
               for(uint i=0;i<8;++i) seed_st[i]=keys[desc.key_idx].state256[i];
               for(uint i=0;i<NW;++i) sk_seed[i]=keys[desc.key_idx].sk_seed[i];"""
        )
    else:
        source += f"uint32_t tip_base=gid*p.wots_len*{words};"
    chain = f"""{word} tip[{words}];
       {prefix}run_wots_chain<{words}>({seed},sk_seed,desc.layer,desc.tree,leaf_idx,c,STEPSu,tip);"""
    each = "for(uint32_t c=0;c<p.wots_len;++c){"
    if shake:
        source += """ShakeSponge sp;
            sp.init<NL>(keys[desc.key_idx].pk_seed,desc.layer,desc.tree,ADRS_WOTS_PK,leaf_idx);"""
        if streaming:
            source += each + chain + "for(uint i=0;i<NL;++i){sp.absorb_lane(tip[i]);}}"
        else:
            source += """uint32_t total_lanes=p.wots_len*NL;
                for(uint32_t i=0;i<total_lanes;++i){sp.absorb_lane(chain_tips[tip_base+i]);}"""
        source += "uint64_t leaf[NL];sp.finish<NL>(leaf);"
    else:
        source += "uint32_t leaf[NW];if(NW==4){"
        if not streaming:
            source += "uint32_t seed_st[8];for(uint i=0;i<8;++i)seed_st[i]=keys[desc.key_idx].state256[i];"
        source += "TlenStream256 s;s.init(seed_st,desc.layer,desc.tree,ADRS_WOTS_PK,leaf_idx,p.wots_len);"
        source += each + (chain if streaming else "uint32_t off=tip_base+c*4u;")
        for i in range(4):
            lane = f"tip[{i}]" if streaming else ("chain_tips[off]" if i == 0 else f"chain_tips[off+{i}u]")
            source += f"s.push_word({lane});"
        source += """}uint32_t out4[4];s.finish(out4);for(uint i=0;i<4u;++i)leaf[i]=out4[i];
            }else{TlenStream512 s;s.init(keys[desc.key_idx].state512,desc.layer,desc.tree,
            ADRS_WOTS_PK,leaf_idx,p.wots_len,NW*4u);"""
        source += each + (chain if streaming else "uint32_t off=tip_base+c*NW;")
        w = "tip[2*i" if streaming else "chain_tips[off+2*i"
        source += (f"for(uint i=0;i<NW/2;++i){{uint64_t v=(uint64_t({w}])<<32)|uint64_t({w}+1]);"
                   "s.push_word64(v);}}s.finish<NW>(leaf);}")
    source += f"""uint32_t out_off=gid*{words};
        for(uint i=0;i<{words};++i){{out_leaves[out_off+i]=leaf[i];}}"""
    return source


def project(msl, shake, streaming, body, compact):
    fn = ("shake_" if shake else "") + ("xmss_leaves_streaming" if streaming else "wots_tlen") + "_impl"
    pattern = re.escape(compact(kernel_body(shake, streaming)))
    pattern = pattern.replace("LEAFOP", r"([%/])").replace("TREEOP", r"([%/])")
    pattern = pattern.replace("STEPS", r"(?P<steps>[0-9]+)", 1).replace("STEPS", r"(?P=steps)")
    match = re.fullmatch(pattern, compact(body(msl, f"void {fn}(")))
    if not match:
        raise ValueError(f"{fn}: unmodeled leaf projection")
    leaf, tree = match.group(1, 2)
    family = "shake" if shake else "sha2"
    name = family + ("StreamLeaf" if streaming else "BufferLeaf")
    indexes = f"(gid {leaf} 2^p.hp) (gid {tree} 2^p.hp)"
    args = "(p : Spec.Params) (e : MetalChainDispatch.Execution)"
    groups = "words" if shake else "(if words = 4 then 1 else words / 2)"
    width = "1" if shake else "(if words = 4 then 4 else 2)"
    size = 8 if shake else 4
    if streaming:
        return f"""
private def {name} {args} (words gid : Nat) :=
  MetalLeafDispatch.nativeStream p e.keys e.trees {indexes} {match.group("steps")} {groups} {width} {size}
private theorem {name}_spec {args} (hv : p.Valid) (words : Nat)
    (geom : p.n = {groups} * {width} * {size}) (gid : Nat) :
    {name} p e words gid = MetalPipeline.metalXmssLeavesStreaming p e.keys e.trees gid :=
  MetalLeafDispatch.nativeStream_spec p hv e.keys e.trees gid _ _ _ geom
"""
    args += " (words : Nat) (mem : MetalChainDispatch.Memory)"
    f = "flatTwoPhase" if shake else "packedTwoPhase"
    groups_arg = "" if shake else f" {groups} {width}"
    geom = "" if shake else f" (geom : {groups} * {width} = words)"
    proof = ("MetalLeafDispatch.flatTwoPhase_eq _ _ _ _ _ _ _ _" if shake else
             "MetalLeafDispatch.packedTwoPhase_eq _ _ _ _ _ _ _ _ _ _ geom")
    return f"""
private def {name} {args} (gid : Nat) :=
  MetalLeafDispatch.{f} p e.keys e.trees words{groups_arg} mem gid {indexes}
private theorem {name}_spec {args}{geom} (gid : Nat) :
    {name} p e words mem gid =
      MetalLeafDispatch.twoPhase p e.keys e.trees words mem gid (gid % 2^p.hp) (gid / 2^p.hp) :=
  {proof}
"""


def public_claim(label, p, geometry, family, n, phase, leaf_cmd, chain_cmd=None):
    mode = ".twoPhase" if phase else ".streaming"
    count = f"(rs.length * {p}.d * 2^{p}.hp)"
    size = 8 if family == "shake" else 4
    words = n // size
    spec = f"(MetalPipeline.metalBatchSignInternal {mode} {p} (MetalCommandValues.framed rs)).flatten"
    names = f"{family}StreamLeaf" if not phase else f"{family}BufferLeaf"
    leaf_order = f"e.schedule.Perm (MetalChainDispatch.grid {count} {words})"
    valid = f"(MetalPipeline.metal_all_12_params_valid {p} (by decide))"
    value = f"({names} {p} e {words})"
    target = f"(MetalPipeline.metalXmssLeavesStreaming {p} keys trees)"
    scratch = f"(MetalLeafDispatch.scratch {count} {words} {size} e {value} {target} keys trees other)"
    allocation = f"rs.length * {p}.sigBytes ≤ pool.length"
    inner = ""
    if phase:
        tip = f"({family}ChainTip {p} e)"
        tip_count = f"({count} * {p}.len)"
        mem = f"(MetalLeafDispatch.run {tip_count} {words} {size} {tip} e)"
        value = f"({names} {p} e {words} {mem})"
        target = f"(MetalPipeline.metalWotsTwoPhaseLeaf {p} keys trees)"
        inner = f"(MetalLeafDispatch.leafScratch {count} {words} {size} leaf {value} {target} other)"
        scratch = f"(MetalChainDispatch.invariant {p} {tip_count} {words} {size} e {tip} keys trees {inner})"
        leaf_order = (f"e.schedule.Perm (MetalChainDispatch.grid {tip_count} {words}) ∧ "
                      f"leaf.schedule.Perm (MetalChainDispatch.grid {count} {words})")
    correct = f"(MetalCommandValues.correct {geometry} (MetalCommandValues.framed rs).length (pool.take (rs.length * {p}.sigBytes)) {spec} {scratch})"
    extra_cmd = f"a ≠ {chain_cmd} → " if phase else ""
    execution = "e leaf" if phase else "e"
    head = f"""
private theorem {label}_leaves (rs : List MetalPipeline.BatchSignReq) (pool : Spec.Bytes)
    ({execution} : MetalChainDispatch.Execution) (keys : MetalChainDispatch.Keys)
    (trees : MetalChainDispatch.Trees) (other : MetalCommand.Region → Prop)
    (accepted : rs.any (fun r => decide (r.ctx.length > 255)) = false →
      {allocation} ∧ {leaf_order} ∧
      ∀ a ∈ {label}, {extra_cmd}a ≠ {leaf_cmd} →
        (∀ r ∈ a.reads, {correct} r) → ∀ r ∈ a.writes, {correct} r) :
    MetalCommandValues.publicResult {p} rs pool =
      rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd) := by
"""
    if not phase:
        return head + f"""
  apply {label}_public rs pool {scratch}
  intro guard
  obtain ⟨allocation, schedule, remaining⟩ := accepted guard
  exact ⟨allocation, MetalLeafDispatch.insert_rule {label} {leaf_cmd} _
    (MetalLeafDispatch.streaming_rule _ (by decide) (by decide) {p} {count} {words} {size}
      e keys trees other {value} ({names}_spec {p} e {valid} {words} (by decide)) schedule {geometry} _ _ _) remaining⟩
""", scratch
    return head + f"""
  apply {label}_chains rs pool e keys trees {inner}
  intro guard
  obtain ⟨allocation, chainOrder, leafOrder, remaining⟩ := accepted guard
  refine ⟨allocation, chainOrder, ?_⟩
  intro a ha hc
  by_cases eq : a = {leaf_cmd}
  · subst a
    exact MetalLeafDispatch.twoPhase_rule _ (by decide) (by decide) {p}
      (MetalPipeline.metal_all_12_params_valid _ (by decide)) {count} {words} {size} (by decide)
      e leaf {tip} {value} keys trees other ({names}_spec {p} e {words} {mem}{" (by decide)" if family == "sha2" else ""})
      leafOrder {geometry} _ _ _
  · exact remaining a ha hc eq
""", scratch
