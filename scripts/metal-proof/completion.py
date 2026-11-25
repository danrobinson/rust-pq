"""Bind the public result and XMSS mode selector to the generated executions."""


def project(lib, compact, body, rows):
    import re
    selector = compact(body(lib, "fn use_two_phase<"))
    pattern = (
        r"letlimit=self.two_phase_leaf_limit.unwrap_or\(match\(family,N\)\{"
        r"\(HashFamily::Sha2,16\)=>(\d+),\(HashFamily::Sha2,_\)=>(\d+),"
        r"\(HashFamily::Shake,_\)=>(\d+),\}\);total_leaves<limit"
    )
    match = re.fullmatch(pattern, selector)
    if not match:
        raise ValueError("unreviewed public XMSS mode selection")
    keygen = compact(body(lib, "fn keygen_internal_batch_family<"))
    sign = compact(body(lib, "fn sign_internal_batch_family<"))
    for source, signing in ((keygen,False),(sign,True)):
        total = "total_xmss_leaves" if signing else "total_leaves"
        leafGeometry = ("let total_trees=num_sigs*d;let total_xmss_leaves=total_trees*leaves_per_tree;"
                        if signing else "let total_leaves=count*leaves_per_tree;")
        if compact(leafGeometry) not in source or f"self.use_two_phase::<N>(family,{total})" not in source:
            raise ValueError("unexpected public mode count")
    statements = []
    for row, family, n, *_ in rows:
        name = row.replace("-","_")
        label, p = "gpu_"+name, "Spec."+name
        limit = match[3] if family=="shake" else match[1] if n==16 else match[2]
        statements.append(f"""
private theorem {label}_sign_success (rs : List MetalPipeline.BatchSignReq) (overrideLimit : Option Nat)
    (initial : MetalChainDispatch.Memory) (memory : Nat → Spec.Byte) (exit : MetalCompletion.Exit)
    (out : Option (List Spec.Bytes)) :
    let two := rs.length*{p}.d*2^{p}.hp < overrideLimit.getD {limit}
    let pool := fun () => if two then {label}_1_pool rs initial memory else {label}_0_pool rs initial memory
    MetalCompletion.sign {p} rs exit pool = .ok out →
      out = rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd) := by
  intro two pool ok
  apply (MetalCompletion.sign_success {p} rs exit pool out ok).trans
  by_cases h : two
  · simpa only [pool,ite_eq_left h,{label}_1_pool] using {label}_1_canonical_fips rs initial memory
  · simpa only [pool,ite_eq_right h,{label}_0_pool] using {label}_0_canonical_fips rs initial memory

private theorem {label}_keygen_success (batch : MetalKeygenDispatch.Batch) (overrideLimit : Option Nat)
    (initial : MetalChainDispatch.Memory) (exit : MetalCompletion.Exit) (out : List (Spec.Bytes × Spec.Bytes)) :
    let two := batch.length*2^{p}.hp < overrideLimit.getD {limit}
    let read := fun () => if two then {label}_1_kg_batch batch initial else {label}_0_kg_batch batch initial
    MetalCompletion.keygen batch exit read = .ok out →
      out = batch.map (fun (sk,prf,pk) => Spec.slhKeygenInternal {p} sk prf pk) := by
  intro two read ok
  have bytes : read () = batch.map (fun (sk,prf,pk) => Spec.slhKeygenInternal {p} sk prf pk) := by
    by_cases h : two
    · simpa only [read,ite_eq_left h] using {label}_1_kg_canonical_fips batch initial
    · simpa only [read,ite_eq_right h] using {label}_0_kg_canonical_fips batch initial
  exact (MetalCompletion.keygen_success batch exit read (fun eq => by rw [bytes,eq]; rfl) out ok).trans bytes
""")
    return "\n".join(statements)
