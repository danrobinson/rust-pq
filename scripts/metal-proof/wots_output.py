"""Source projection of both WOTS signature-output kernels into the Lean byte
scatter. SHA-word representations and individual hash transcripts are checked
at their primitive boundary by check-metal-values.py."""
import re


def project(msl, shake, body, compact, *, previous_layer_counterexample=False):
    width, word, prefix, size = ("NL", "uint64_t", "shake_", 8) if shake else ("NW", "uint32_t", "", 4)
    load = "pk_seed" if shake else "seed_st"
    keys = (
        """uint64_t pk_seed[NL], sk_seed[NL];for(uint i=0;i<NL;++i){
            pk_seed[i]=km.pk_seed[i];sk_seed[i]=km.sk_seed[i];}""" if shake else
        """uint32_t seed_st[8];uint32_t sk_seed[NW];
        for(uint i=0;i<8;++i)seed_st[i]=km.state256[i];for(uint i=0;i<NW;++i)sk_seed[i]=km.sk_seed[i];"""
    )
    writer = "write_shake_node_bytes" if shake else "write_node_bytes"
    shape = f"""
      uint32_t total_chains=p.num_layers*p.wots_len;if(gid>=total_chains)return;
      uint32_t chain=gid CHAINOP p.wots_len;uint32_t layer_global=gid ROWOP p.wots_len;
      WotsSignLayerDesc desc=layers[layer_global];const device {"Shake" if shake else ""}KeyMaterial &km=keys[desc.key_idx];
      {word} msg[{width}];
      if(desc.layer==0u){{uint32_t off=desc.sig_idx*{width};
        for(uint i=0;i<{width};++i)msg[i]=pk_fors[off+i];}}else{{
        uint32_t off=(desc.sig_idx*p.d+(desc.layer-DELTAu))*{width};
        for(uint i=0;i<{width};++i)msg[i]=xmss_roots[off+i];}}
      uint32_t steps={prefix}wots_digit_at<{width}>(msg,chain);
      {keys}
      {word} sig_val[{width}];{prefix}run_wots_chain<{width}>({load},sk_seed,desc.layer,desc.tree,
        desc.keypair,chain,steps,sig_val);
      {writer}<{width}>(out_sigs+desc.wots_byte_off+chain*{width}*{size}u,sig_val);
    """
    pattern = re.escape(compact(shape)).replace("CHAINOP", r"([/%])").replace("ROWOP", r"([/%])").replace("DELTA", r"(\d+)")
    parsed = re.fullmatch(pattern, compact(body(msl, f"void {prefix}wots_sign_impl(")))
    if not parsed:
        raise ValueError("unmodeled WOTS signature dispatch")
    chain, row, delta = parsed.groups()
    if previous_layer_counterexample:
        return f"example : (1 : Nat) - {delta} ≠ 0 := by decide\n"
    if shake:
        digit = """uint32_t len1=16u*NL;if(chain<len1){uint32_t byte_idx=chain>>1;
          uint8_t b=uint8_t(msg[byte_idx>>3]>>(8u*(byte_idx&7u)));
          return ((chain&1u)==0u)?((b>>4)&0xFu):(b&0xFu);}
          uint32_t csum=0u;for(uint i=0;i<NL;++i){uint64_t lane=msg[i];for(uint b=0;b<8u;++b){
          uint32_t byte_val=uint32_t((lane>>(8u*b))&0xFFul);
          csum+=15u-((byte_val>>4)&0xFu);csum+=15u-(byte_val&0xFu);}}"""
    else:
        digit = """uint32_t len1=8u*NW;if(chain<len1){uint32_t w=msg[chain>>3];
          uint32_t nib=chain&7u;return(w>>(28u-4u*nib))&0xFu;}
          uint32_t csum=0u;for(uint i=0;i<NW;++i){uint32_t w=msg[i];"""
        for shift in range(28, 0, -4):
            digit += f"csum+=15u-((w>>{shift})&0xFu);"
        digit += "csum+=15u-(w&0xFu);}"
    digit += "uint32_t c_idx=chain-len1;return(csum>>(8u-4u*c_idx))&0xFu;"
    store = "store_le64" if shake else "store_be32"
    stores = "".join(f"dst[{i}]=uint8_t(v{f'>>{shift}' if shift else ''});"
                     for i in range(size) for shift in [8 * (i if shake else size-1-i)])
    for marker, expected in (
        (f"uint32_t {prefix}wots_digit_at(", digit),
        (f"void {writer}(", f"for(uint i=0;i<{width};++i){{{store}(dst+{size}u*i,node[i]);}}"),
        (f"void {store}(", stores),
    ):
        if compact(body(msl, marker)) != compact(expected):
            raise ValueError(f"unmodeled WOTS value or serialization: {marker}")
    name = "shake" if shake else "sha2"
    return f"""
private def {name}SigAddr {{p count}} (inputs : MetalWotsOutput.Inputs) (words : Nat)
    (w : MetalWotsOutput.Coord p count) :=
  let id := MetalWotsOutput.gid w
  (inputs.desc (id {row} p.len)).outBase + (id {chain} p.len)*words*{size} + w.i.val
private theorem {name}SigAddr_spec {{p count}} (inputs : MetalWotsOutput.Inputs) (words : Nat)
    (width : p.n = words * {size}) (w : MetalWotsOutput.Coord p count) :
    {name}SigAddr inputs words w = MetalWotsOutput.shaderAddr inputs w := by
  simp only [{name}SigAddr, MetalWotsOutput.shaderAddr, width, Nat.mul_assoc]
private def {name}SigByte {{p count}} (inputs : MetalWotsOutput.Inputs) (w : MetalWotsOutput.Coord p count) :=
  let id := MetalWotsOutput.gid w
  let c := id {chain} p.len
  let d := inputs.desc (id {row} p.len)
  let k := inputs.keys d.key
  let m := if d.layer = 0 then inputs.fors d.sig else inputs.roots (d.sig*p.d+(d.layer-{delta}))
  MetalWotsOutput.storeByte {str(bool(shake)).lower()} (MetalChainDispatch.chainLoop p k.1 k.2 d.layer d.tree d.pair c (MetalWotsOutput.digitAt m c)) w.i.val
private theorem {name}SigByte_spec {{p count}} (inputs : MetalWotsOutput.Inputs) (w : MetalWotsOutput.Coord p count) :
    {name}SigByte inputs w = MetalWotsOutput.shaderByte inputs w := by
  simp only [{name}SigByte,MetalWotsOutput.storeByte_eq]
  rfl
"""


def public_claim(label, p, g, family, n, phase, leaf_cmd, chain_cmd, wots_cmd, leaf_scratch, *, fors_stage=None, host_cmd=None):
    words = n // (8 if family == "shake" else 4)
    mode = ".twoPhase" if phase else ".streaming"
    count = f"(rs.length * {p}.d * 2^{p}.hp)"
    leaf_execution = "e leaf" if phase else "e"
    leaf_order = f"{'leaf' if phase else 'e'}.schedule.Perm (MetalChainDispatch.grid {count} {words})"
    chain_order = f"e.schedule.Perm (MetalChainDispatch.grid ({count}*{p}.len) {words}) ∧ " if phase else ""
    names = "chainOrder leafOrder" if phase else "leafOrder"
    leaf_scratch = leaf_scratch.replace("other)", "inputsInv)")
    checks = f"a ≠ {chain_cmd} → " if phase else ""
    spec = f"(MetalPipeline.metalBatchSignInternal {mode} {p} requests).flatten"
    correct = f"(MetalCommandValues.correct {g} requests.length (out.take (rs.length*{p}.sigBytes)) {spec} inv)"
    base = "signature_store" if fors_stage is None else "fors_public_key"
    extras = setup = orders = exclude = ""
    source = "data"
    rest = "other"
    if fors_stage is not None:
        fors_cmd, split = fors_stage
        size = 8 if family == "shake" else 4
        extras = "(jobs : Nat → MetalForsPkDispatch.Job) (roots : MetalChainDispatch.Memory) (pkBuf : MetalChainDispatch.Execution)"
        setup = f"""let pkValue := {family}ForsValue {p} e.keys jobs roots {words}
    let source := {{data with fors := MetalForsPkDispatch.readPk requests.length {words} {size} pkValue pkBuf}}
    let rest := MetalForsPkDispatch.scratch {p} requests keys jobs {words} {size} roots {split} other
    """
        source, rest = "source", "rest"
        orders = f"pkBuf.schedule.Perm (MetalChainDispatch.grid requests.length {words}) ∧"
        exclude = f"a ≠ {fors_cmd} →"
    host_setup = ""
    arguments = f"""({leaf_execution} : MetalChainDispatch.Execution) (keys : MetalChainDispatch.Keys)
    (trees : MetalChainDispatch.Trees) (other : MetalCommand.Region → Prop)
    (data : MetalWotsOutput.Inputs) {extras} (capacity : Nat) (initial : Nat → Spec.Byte)"""
    if host_cmd is not None:
        base = "host_values"
        arguments = f"""({"pre leaf" if phase else "pre"} : MetalChainDispatch.Execution)
    (unconstrained : MetalCommand.Region → Prop) (raw : MetalWotsOutput.Inputs)
    (roots : MetalChainDispatch.Memory) (pkBuf : MetalChainDispatch.Execution)
    (events : List (MetalHostValues.Middle {g} (MetalCommandValues.framed rs).length))
    (capacity : Nat) (memory : Nat → Spec.Byte)"""
        host_setup = f"""let keys := MetalHostValues.keys {p} requests
    let trees := MetalHostValues.trees {p} requests
    let e := MetalHostValues.initialized (p := {p}) requests pre
    let data := {{raw with desc := MetalHostValues.layer {p} requests}}
    let jobs := MetalHostValues.job {p} requests
    let initial := MetalHostValues.afterMiddle events (MetalHostValues.initMemory {p} requests memory)
    let other := fun r => if r = MetalCommand.Region.randomizer then True else unconstrained r
    """
        exclude += f" a ≠ {host_cmd} →"
    header = f"""
private theorem {label}_{base} (rs : List MetalPipeline.BatchSignReq)
    {arguments}
    (schedule : List (MetalWotsOutput.Coord {p} (MetalCommandValues.framed rs).length)) :
    let requests := MetalCommandValues.framed rs
    {host_setup}{setup}let buffers := {{{source} with keys := e.keys}}
    let atByte := @{family}SigAddr {p} requests.length buffers {words}
    let toByte := @{family}SigByte {p} requests.length buffers
    let out := MetalWotsOutput.pool atByte toByte schedule initial capacity
    let inputsInv := MetalWotsOutput.otherScratch {p} requests buffers keys {rest}
    let inv := {leaf_scratch}
    (rs.any (fun r => decide (r.ctx.length > 255)) = false →
      rs.length*{p}.sigBytes ≤ capacity ∧ {chain_order}{leaf_order} ∧
      (schedule.map MetalWotsOutput.lane).Perm (MetalChainDispatch.grid (requests.length*{p}.d*{p}.len) {p}.n) ∧
      {orders}
      ∀ a ∈ {label}, {checks}a ≠ {leaf_cmd} → a ≠ {wots_cmd} → {exclude}
        (∀ r ∈ a.reads, {correct} r) → ∀ r ∈ a.writes, {correct} r) →
    MetalCommandValues.publicResult {p} rs out =
      rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd) := by
"""
    if host_cmd is not None:
        return header + f"""
  intro requests keys trees e data jobs initial other pkValue source rest buffers atByte toByte out inputsInv inv accepted
  apply {label}_fors_public_key rs {leaf_execution} keys trees other data jobs roots pkBuf capacity initial schedule
  intro guard
  obtain ⟨alloc,{", ".join(names.split())},cover,pkOrder,remaining⟩ := accepted guard
  refine ⟨alloc,{",".join(names.split())},cover,pkOrder,?_⟩
  intro a ha {"hc " if phase else ""}hl hw hf
  by_cases eq : a = {host_cmd}
  · subst a
    have nr : requests.length = rs.length := by simp [requests,MetalCommandValues.framed]
    have descriptors : MetalWotsOutput.Descriptors {p} requests buffers keys :=
      MetalHostValues.layers_spec {p} requests buffers rfl
    have rand := MetalHostValues.final_randomizer {p} (MetalPipeline.metal_all_12_params_valid _ (by decide))
      {mode} requests {g} (by decide) (by decide) events atByte toByte
      (fun w => ({family}SigAddr_spec buffers {words} (by decide) w).trans (MetalWotsOutput.shader_addr descriptors w))
      schedule memory capacity (nr ▸ alloc) inv (by trivial)
    have span : requests.length*{p}.sigBytes = rs.length*{p}.sigBytes := congrArg (· * {p}.sigBytes) nr
    apply MetalHostValues.host_rule {host_cmd} (by decide) {g} requests.length _ _ inv
      rfl rfl (MetalHostValues.jobs_spec {p} requests) descriptors
    simpa only [span] using rand
  · exact remaining a ha {"hc " if phase else ""}hl hw hf eq
"""
    if fors_stage is not None:
        return header + f"""
  intro requests pkValue source rest buffers atByte toByte out inputsInv inv accepted
  apply {label}_signature_store rs {leaf_execution} keys trees rest source capacity initial schedule
  intro guard
  obtain ⟨alloc,{", ".join(names.split())},cover,pkOrder,remaining⟩ := accepted guard
  refine ⟨alloc,{",".join(names.split())},cover,?_⟩
  intro a ha {"hc " if phase else ""}hl hw
  by_cases eq : a = {fors_cmd}
  · subst a
    exact MetalForsPkDispatch.local_rule {p} (MetalPipeline.metal_all_12_params_valid _ (by decide))
      requests {split} {fors_cmd} (by decide) (by decide) e.keys keys jobs roots {words} {size} (by decide)
      pkValue ({family}ForsValue_spec {p} e.keys jobs roots {words}{" (by decide)" if family == "sha2" else ""})
      pkBuf pkOrder {g} requests.length _ _ inv id id id id
  · exact remaining a ha {"hc " if phase else ""}hl hw eq
"""
    return header + f"""
  intro requests buffers atByte toByte out inputsInv inv accepted
  apply {label}_leaves rs out {leaf_execution} keys trees inputsInv
  intro guard
  obtain ⟨alloc,{", ".join(names.split())},cover,remaining⟩ := accepted guard
  have alloc' : rs.length*{p}.sigBytes ≤ out.length := by
    simpa only [out,MetalWotsOutput.pool,List.length_ofFn] using alloc
  refine ⟨alloc',{",".join(names.split())},?_⟩
  intro a ha {"hc " if phase else ""}hl
  by_cases eq : a = {wots_cmd}
  · subst a
    have nr : requests.length = rs.length := by simp [requests,MetalCommandValues.framed]
    have rule := MetalWotsOutput.wots_rule {p} (MetalPipeline.metal_all_12_params_valid _ (by decide))
      requests {mode} {wots_cmd} (by decide) (by decide) buffers keys atByte toByte
      ({family}SigAddr_spec buffers {words} (by decide)) ({family}SigByte_spec buffers)
      schedule (MetalWotsOutput.covered schedule cover) initial capacity (nr ▸ alloc) {g} (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) inv id id id id trivial
    have span : requests.length*{p}.sigBytes = rs.length*{p}.sigBytes := congrArg (· * {p}.sigBytes) nr
    simpa only [span] using rule
  · exact remaining a ha {"hc " if phase else ""}hl eq
"""
