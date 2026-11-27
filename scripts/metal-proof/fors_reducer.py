"""Close the two FORS pass contracts over published buffers and disjoint signature writes."""


def public_claim(header, label, p, g, family, words, size, phase, mode, s1, s2, cmds):
    stem = family+"Forest"
    base = f"{label}_xmss_reduce"
    header = header.replace(base, f"{label}_signing_execution")
    header = header.replace("(unconstrained : MetalCommand.Region → Prop) ", "")
    header = header.replace("(roots : MetalChainDispatch.Memory)", ("(subBuf finalBuf : MetalChainDispatch.Execution)" if s2 else "(subBuf : MetalChainDispatch.Execution)"))
    field = f"MetalReducerBytes.Field {g} (MetalCommandValues.framed rs).length"
    header = header.replace(f" (otherBytes : {field} → Spec.Byte)", "")
    roots = (f"MetalLeafDispatch.run (requests.length*{p}.k) {words} {size} "
             f"({stem}Root {p} requests {s1} {s2} {words} subMem) finalBuf" if s2 else "subMem")
    header = header.replace("(raw : MetalWotsOutput.Inputs)", "")
    parts = f"""let raw : MetalWotsOutput.Inputs := ⟨fun _ => ⟨0,0,0,0,0,0⟩,fun _ => ([],[]),fun _ => [],fun _ => []⟩
    let subValue := {stem}Sub {p} requests {s1} {s2}
    let subMem := MetalForsDispatch.subBuffer {p} requests.length {s2} {words} {size} subValue subBuf
    let roots := {roots}
    let sec := {stem}Secret {p} requests {s1}
    let auth := {stem}Auth {p} requests {s1} {s2} {words} subMem
    let leafMem :="""
    header = header.replace("let leafMem :=", parts).replace("else unconstrained r", "else True")
    inv = header.split("    let inv := ")[1].split("\n")[0]
    header = header[:header.index("    let inputsInv :=")]+header[header.index("    (rs.any"): ]
    proof_scratch = [line for line in header.splitlines() if any(
        line.strip().startswith("let "+name+" :=") for name in ("remainder", "other", "rest")
    )]
    for line in proof_scratch:
        header = header.replace(line+"\n", "")
    local_scratch = "\n".join("  "+line.strip() for line in proof_scratch)
    native = f"MetalForsDispatch.serialized (p:={p}) (rs:=requests) (g:={g}) {str(family=='shake').lower()} authValue sec auth"
    header = header.replace(f"MetalXmssDispatch.values (p:={p}) (rs:=requests) authValue otherBytes", native)
    start = header.index(f"      (∀ w : {field}")
    end = header.index(") →\n    MetalCommandValues.publicResult", start)
    order2 = (f" ∧ finalBuf.schedule.Perm (MetalChainDispatch.grid (requests.length*{p}.k) {words})" if s2 else "")
    header = header[:start]+f"""      middle.Perm (MetalReducerBytes.grid {g} requests.length) ∧
      subBuf.schedule.Perm (MetalChainDispatch.grid (requests.length*{p}.k*2^{s2}) {words}){order2}"""+header[end:]
    skipped = ",".join(cmds)
    checks = [f"h{i}" for i in range(len(cmds))]
    skipProof = ",".join(checks)
    hnames = " ".join(checks)
    orders = "tipOrder,leafOrder" if phase else "leafOrder"
    allroots = (f"MetalForsDispatch.split_words {p} requests {s1} {s2} {words} {size} (by decide) subMem subOK finalBuf finalOrder"
                if s2 else f"MetalForsDispatch.unsplit_words {p} requests {words} {size} subBuf (by simpa using subOrder)")
    rootProof = (f"""change MetalForsPkDispatch.Roots {p} requests {words} {size} (MetalLeafDispatch.run (requests.length*{p}.k) {words} {size}
      ({stem}Root {p} requests {s1} {s2} {words} subMem) finalBuf)
    rw [funext ({stem}Root_spec {p} requests {s1} {s2} {words} subMem)]
    exact {allroots}""" if s2 else
       f"""change MetalForsPkDispatch.Roots {p} requests {words} {size}
      (MetalForsDispatch.subBuffer {p} requests.length 0 {words} {size} ({stem}Sub {p} requests {s1} 0) subBuf)
    rw [funext subSpec,show ({s1}:Nat)={p}.a by decide]
    exact {allroots}""")
    kinds = ([".fors_sub_roots",".fors_roots",".forsLow",".forsHigh"] if s2 else [".fors_sub_roots",".forsLow"])
    choices = " | ".join(["rfl"]*len(kinds)+["impossible"])
    cases = []
    for kind in kinds:
        if kind in (".fors_sub_roots",".fors_roots"):
            applies = (kind == ".fors_roots") == bool(s2)
            cases.append("  · exact MetalForsDispatch.scratch_region (by simp) "+("(show inv "+kind+" from rootsOK)" if applies else "(by trivial)"))
        else:
            cases.append(f"  · simpa only [span] using bytesOk {kind} (by simp) (by trivial)")
    proof = header+f"""
  intro requests keys trees e raw subValue subMem roots sec auth leafMem rootValue authValue
  rw [MetalForsDispatch.serialized_eq (p:={p}) (rs:=requests) (g:={g}) {str(family=="shake").lower()} authValue sec auth]
  let otherBytes := @MetalForsDispatch.values {g} requests.length sec auth
  intro bytesAt events
    rawWithRoots data jobs initial pkValue source buffers atByte toByte out accepted
{local_scratch}
  let inputsInv := MetalWotsOutput.otherScratch {p} requests buffers keys rest
  let inv := {inv}
  apply {base} rs {"pre leaf" if phase else "pre"} (fun _ => True) raw roots pkBuf rootBuf middle otherBytes capacity memory schedule
  intro guard
  obtain ⟨alloc,{orders},cover,pkOrder,rootOrder,midOrder,subOrder{",finalOrder" if s2 else ""}⟩ := accepted guard
  have hv := MetalPipeline.metal_all_12_params_valid {p} (by decide)
  have subSpec := {stem}Sub_spec {p} requests {s1} {s2}
  have subOK := MetalForsDispatch.sub_read {p} hv requests {s1} {s2} {words} {size} (by decide)
    (by decide) subValue subSpec subBuf subOrder
  have rootsOK : MetalForsPkDispatch.Roots {p} requests {words} {size} roots := by
    {rootProof}
  have nr : requests.length = rs.length := by simp [requests,MetalCommandValues.framed]
  have span := congrArg (· * {p}.sigBytes) nr
  have descriptors := MetalHostValues.layers_spec {p} requests buffers rfl
  have bytesOk := MetalForsDispatch.signature_region {p} hv {mode} requests {g} (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) {words} subMem subOK
    sec auth ({stem}Secret_spec {p} requests {s1}) ({stem}Auth_spec {p} requests {s1} {s2} {words} subMem) authValue middle midOrder atByte toByte schedule
    (fun w => ({family}SigAddr_spec buffers {words} (by decide) w).trans (MetalWotsOutput.shader_addr descriptors w))
    (MetalHostValues.initMemory {p} requests memory) capacity (nr ▸ alloc) inv
  refine ⟨alloc,{orders},cover,pkOrder,rootOrder,fun b _ => MetalReducerBytes.complete _ midOrder b,?_⟩
  intro a ha {hnames} _ r hr
  have classified := MetalForsDispatch.residual_outputs (trace:={label}) (excluded:=[{skipped}])
    (outputs:=[{",".join(kinds)}]) (by decide) ha (by simp [{skipProof}]) hr
  simp only [List.mem_cons,List.not_mem_nil] at classified
  rcases classified with {choices}
"""+'\n'.join(cases)+"""
  · exact False.elim impossible
"""
    return proof + canonical(header, label, p, g, words, phase, s2)


def canonical(header, label, p, g, words, phase, s2):
    """Exhibit a completed execution for every batch with no run hypotheses."""
    stem = f"{label}_signing_execution"
    model = header.split("    let keys :=", 1)[1].split("    (rs.any", 1)[0]
    model = "    let keys :="+model
    model = model.rstrip()
    count = f"(rs.length*{p}.d*2^{p}.hp)"
    inputs = [("pre", f"({count}*{p}.len)" if phase else count)]
    if phase:
        inputs.append(("leaf", count))
    inputs.append(("subBuf", f"(requests.length*{p}.k*2^{s2})"))
    if s2:
        inputs.append(("finalBuf", f"(requests.length*{p}.k)"))
    inputs.extend([("pkBuf","requests.length"),("rootBuf",f"(requests.length*{p}.d)")])
    buffers = "\n".join(f"    let {name} := MetalSigningSchedule.execution {rows} {words} initial" for name,rows in inputs)
    names = " ".join(name for name, _ in inputs)
    perms = ["le_rfl"]+["List.Perm.refl _"]*(1+int(phase))
    perms += [f"MetalSigningSchedule.wots_order {p} requests.length (by decide) (by decide)"]
    perms += ["List.Perm.refl _"]*(4+bool(s2))
    setup = f"""    let requests := MetalCommandValues.framed rs
{buffers}
    let middle := MetalReducerBytes.grid {g} requests.length
    let capacity := rs.length*{p}.sigBytes
    let schedule := MetalSigningSchedule.wots {p} requests.length (by decide) (by decide)
{model}"""
    args = "(rs : List MetalPipeline.BatchSignReq) (initial : MetalChainDispatch.Memory) (memory : Nat → Spec.Byte)"
    return f"""
private def {label}_pool {args} : Spec.Bytes :=
{setup}
    out
private theorem {label}_canonical_fips {args} :
{setup}
    MetalCommandValues.publicResult {p} rs out = rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd) := by
  intro requests {names} middle capacity schedule
  apply {stem} rs {names} middle capacity memory schedule
  exact fun _ => ⟨{",".join(perms)}⟩
"""


def project(shader, shake, body, compact):
    """Read the actual workgroup operand indices. The token pins also cover
    sections that lower to the previously checked primitive, barrier and byte
    store contracts. reducer_values.py independently replays those full bodies."""
    import hashlib
    import re
    prefix, word = ("shake_", "NL") if shake else ("", "NW")
    bodies = [compact(body(shader, f"void {prefix}fors_pass{i}_impl(")) for i in (1, 2)]
    pins = (
        ("30581752742d187b256811717bdeb520e4562b47cb6a6b6c1ac522168d2f1a05",
         "ef053ae7d2f0830d785e96ff3d0f78b7fe7b469f82384aa7cffc1467b0e62786"),
        ("e2b9dd79c93ae6e250e9ca76f1aa643f8c38cbe06c4e11e9ae17ef77a67d96d5",
         "a8e83f15aa051aabb98bd616d204a002d84808f0951bcf5d6def2679000279f3"),
    )[bool(shake)]
    for code, pin in zip(bodies, pins):
        if hashlib.sha256(code.encode()).hexdigest() != pin:
            raise ValueError("unreviewed FORS reducer body")
    low, high = bodies

    def capture(src, pattern):
        matches = re.findall(pattern, src)
        if len(matches) != 1:
            raise ValueError("unrecognized FORS reducer operand: "+pattern)
        return matches[0]

    def children(src):
        l = capture(src, rf"left\[i\]=tg_nodes\[\((\d+)u\*tid\)\*{word}\+i\]")
        r, d = capture(src, rf"right\[i\]=tg_nodes\[\((\d+)u\*tid\+(\d+)u\)\*{word}\+i\]")
        return l, r, d

    sibling = capture(low, r"sib_in_tree=\(target>>\(lvl-1u\)\)\^(\d+)u;")
    upper = capture(high, r"sib=\(target>>\(lvl-1u\)\)\^(\d+)u;")
    stride = capture(low, r"leaf0_in_tree=\(st_local<<p.s1\)\+\((\d+)u\*tid\);")
    right = capture(low, r"leaf1_in_tree=leaf0_in_tree\+(\d+)u;")
    lo, lor, lod = children(low)
    hi, hir, hid = children(high)
    name = ("shake" if shake else "sha2")+"Forest"
    args = "(p : Spec.Params) (rs : List MetalPipeline.BatchSignReq)"
    local = "(p : Spec.Params) (s1 : Nat) (x : MetalWotsOutput.Context) (t st : Nat)"
    upperArgs = args+" (s1 s2 words : Nat) (mem : MetalChainDispatch.Memory)"
    return f"""
private def {name}Low {local} : Nat → Nat → Spec.Bytes
  | 0,i =>
    let index := (t <<< p.a)+(st <<< s1)+i
    let a := MetalForsPkDispatch.treeAddress x
    Spec.F p x.pk {{a with word2:=0,word3:=index}} (Spec.forsSkGen p x.sk x.pk a index)
  | h+1,i =>
    let prev := {name}Low p s1 x t st h
    if i < 2^(s1-(h+1)) then
      let idx := (t <<< (p.a-(h+1)))+(st <<< (s1-(h+1)))+i
      Spec.H p x.pk {{MetalForsPkDispatch.treeAddress x with word2:=h+1,word3:=idx}}
        (prev ({lo}*i) ++ prev ({lor}*i+{lod}))
    else prev i
private theorem {name}Low_spec {local} (h i : Nat) :
    {name}Low p s1 x t st h i = MetalPipeline.metalForsPass1State p s1 x.sk x.pk (MetalForsPkDispatch.treeAddress x) t st h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp only [{name}Low,ih,MetalPipeline.metalForsPass1State,MetalPipeline.tgReduceStep]
private def {name}Sub {args} (s1 s2 gid : Nat) :=
  let row := gid/2^s2
  {name}Low p s1 (MetalForsDispatch.fetched p rs (row/p.k)) (row%p.k) (gid%2^s2) s1 0
private theorem {name}Sub_spec {args} (s1 s2 gid : Nat) :
    {name}Sub p rs s1 s2 gid = MetalForsDispatch.subValue p rs s1 s2 gid := by
  simp only [{name}Sub,MetalForsDispatch.fetched_spec,{name}Low_spec]; rfl
private def {name}High {upperArgs} (row : Nat) : Nat → Nat → Spec.Bytes
  | 0,i => MetalLeafDispatch.readNode words mem (row*2^s2+i)
  | h+1,i =>
    let x := MetalForsDispatch.fetched p rs (row/p.k)
    let lvl := s1+(h+1)
    let prev := {name}High p rs s1 s2 words mem row h
    if i < 2^(s2-(h+1)) then
      let idx := ((row%p.k) <<< (p.a-lvl))+i
      Spec.H p x.pk {{MetalForsPkDispatch.treeAddress x with word2:=lvl,word3:=idx}}
        (prev ({hi}*i) ++ prev ({hir}*i+{hid}))
    else prev i
private theorem {name}High_spec {upperArgs} (row h i : Nat) :
    {name}High p rs s1 s2 words mem row h i = MetalForsDispatch.second p rs s1 s2 words mem row h i := by
  induction h generalizing i with
  | zero => rfl
  | succ h ih => simp only [{name}High,MetalForsDispatch.fetched_spec,ih,MetalForsDispatch.second,MetalPipeline.metalForsPass2State,MetalPipeline.tgReduceStep]
private def {name}Root {upperArgs} (row : Nat) := {name}High p rs s1 s2 words mem row s2 0
private theorem {name}Root_spec {upperArgs} (row : Nat) :
    {name}Root p rs s1 s2 words mem row = MetalForsDispatch.rootVal p rs s1 s2 words mem row :=
  {name}High_spec p rs s1 s2 words mem row s2 0
private def {name}Secret {args} (s1 sig t : Nat) :=
  let x := MetalForsDispatch.fetched p rs sig
  let target := MetalReducerBytes.target p rs[sig]! t
  let leaf := ((target >>> s1) <<< s1)+{stride}*((target%2^s1)/{stride})
  let idx := (t <<< p.a)+leaf
  if leaf=target then Spec.forsSkGen p x.sk x.pk (MetalForsPkDispatch.treeAddress x) idx
  else Spec.forsSkGen p x.sk x.pk (MetalForsPkDispatch.treeAddress x) (idx+{right})
private theorem {name}Secret_spec {args} (s1 sig t : Nat) :
    {name}Secret p rs s1 sig t = MetalForsDispatch.secretVal p rs s1 sig t := by
  simp only [{name}Secret,MetalForsDispatch.fetched_spec]; rfl
private def {name}Auth {upperArgs} (sig t h : Nat) :=
  let x := MetalForsDispatch.fetched p rs sig
  let target := MetalReducerBytes.target p rs[sig]! t
  let st := target >>> s1
  let tid := (target%2^s1)/{stride}
  let left := {stride}*tid
  if h<s1 then
    if h=0 then
      if (st <<< s1)+left=target then {name}Low p s1 x t st 0 (left+{right})
      else {name}Low p s1 x t st 0 left
    else {name}Low p s1 x t st h (((target >>> h) ^^^ {sibling}) &&& ((1 <<< (s1-h))-1))
  else {name}High p rs s1 s2 words mem (sig*p.k+t) (h-s1) ((target >>> h) ^^^ {upper})
private theorem {name}Auth_spec {upperArgs} (sig t h : Nat) :
    {name}Auth p rs s1 s2 words mem sig t h = MetalForsDispatch.authVal p rs s1 s2 words mem sig t h := by
  simp only [{name}Auth,MetalForsDispatch.fetched_spec,{name}Low_spec,{name}High_spec]; rfl
"""
