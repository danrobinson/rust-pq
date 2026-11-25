"""Bind the public result and XMSS mode selector to the generated executions."""


def project(lib, compact, body, rows, internal):
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
        statements.append(internal(label, p, limit))
    return "\n".join(statements)


def resources(bridge, gpu, compact, body):
    """Match each fallible Objective-C resource construction and its Rust
    NonNull conversion. Translate the null guards from each matched body."""
    import re

    def checked(marker, grammar):
        actual = compact(body(bridge, marker))
        # Diagnostic text has no control-flow or handle effect.
        actual = re.sub(r"write_err\([^;]*\);", "diagnostic;", actual)
        if actual != compact(grammar):
            raise ValueError("changed Metal resource creation in "+marker)
        return actual

    ctx = checked("SlhMetalCtx *slh_metal_ctx_create", """
      @autoreleasepool{
       id<MTLDevice>device=MTLCreateSystemDefaultDevice();if(!device){diagnostic;return NULL;}
       id<MTLCommandQueue>queue=[device newCommandQueue];if(!queue){diagnostic;return NULL;}
       NSString*source=[[NSString alloc]initWithBytes:shader_src length:shader_len encoding:NSUTF8StringEncoding];
       if(!source){diagnostic;return NULL;} MTLCompileOptions*opts=[[MTLCompileOptions alloc]init];NSError*error=nil;
       id<MTLLibrary>library=[device newLibraryWithSource:source options:opts error:&error];
       if(!library){diagnostic;return NULL;}SlhMetalCtxObj*obj=[[SlhMetalCtxObj alloc]init];
       obj.device=device;obj.queue=queue;obj.library=library;return(__bridge_retained SlhMetalCtx*)obj;}""")
    pipe = checked("SlhMetalPipeline *slh_metal_pipeline_create", """
      if(!ctx||!fn_name){diagnostic;return NULL;}@autoreleasepool{
       SlhMetalCtxObj*obj=(__bridge SlhMetalCtxObj*)ctx;NSString*name=[NSString stringWithUTF8String:fn_name];
       id<MTLFunction>fn=[obj.library newFunctionWithName:name];if(!fn){diagnostic;return NULL;}NSError*error=nil;
       id<MTLComputePipelineState>state=[obj.device newComputePipelineStateWithFunction:fn error:&error];
       if(!state){diagnostic;return NULL;}SlhMetalPipelineObj*p=[[SlhMetalPipelineObj alloc]init];p.state=state;
       return(__bridge_retained SlhMetalPipeline*)p;}""")
    buf = checked("SlhMetalBuffer *slh_metal_buffer_alloc", """
      if(!ctx){return NULL;} @autoreleasepool{SlhMetalCtxObj*obj=(__bridge SlhMetalCtxObj*)ctx;
       size_t alloc_len=(len==0)?16:len;id<MTLBuffer>buf=[obj.device newBufferWithLength:alloc_len options:MTLResourceStorageModeShared];
       if(!buf){return NULL;}SlhMetalBufferObj*b=[[SlhMetalBufferObj alloc]init];b.buffer=buf;b.requestedLen=len;
       return(__bridge_retained SlhMetalBuffer*)b;}""")
    cmd = compact(body(bridge,"SlhMetalCmd *slh_metal_cmd_begin"))
    for mark, expected in (
        ("pub fn new(shader_src", "let mut err=[0 as c_char;1024];let raw=unsafe{slh_metal_ctx_create(shader_src.as_ptr() as *const c_char,shader_src.len(),err.as_mut_ptr(),err.len(),)};NonNull::new(raw).map(|raw|Self{raw}).ok_or_else(||MetalError(read_err_buf(&err)))"),
        ("pub fn pipeline(", "let c_name=CString::new(fn_name).map_err(|e|MetalError(e.to_string()))?;let mut err=[0 as c_char;512];let raw=unsafe{slh_metal_pipeline_create(self.raw.as_ptr(),c_name.as_ptr(),err.as_mut_ptr(),err.len(),)};NonNull::new(raw).map(|raw|MetalPipeline{raw}).ok_or_else(||MetalError(read_err_buf(&err)))"),
        ("pub fn alloc_buffer(", 'let raw=unsafe{slh_metal_buffer_alloc(self.raw.as_ptr(),len)};NonNull::new(raw).map(|raw|MetalBuffer{raw,zeroize_on_drop:false,}).ok_or_else(||MetalError(format!("failed to allocate Metal shared buffer ({len} bytes)")))'),
    ):
        if compact(body(gpu,mark)) != compact(expected):
            raise ValueError("changed Metal non-null result conversion in "+mark)

    def guards(src, names):
        flags = []
        for test in re.findall(r"if\((!\w+(?:\|\|!\w+)*)\)\{(?:diagnostic;)?returnNULL;\}",src):
            flags.extend(names[token[1:]] for token in test.split("||"))
        return " && ".join(flags+["wrapper"])

    ctxFlags = guards(ctx,{k:k for k in ("device","queue","source","library")})
    pipeFlags = guards(pipe,dict(ctx="ctx",fn_name="fnName",fn="function",state="state"))
    bufFlags = guards(buf,dict(ctx="ctx",buf="allocation"))
    cmdFlags = guards(cmd,dict(ctx="ctx",cmdBuf="command",encoder="encoder"))
    return f"""
private def gpu_setup_context (device queue source library wrapper : Bool) := {ctxFlags}
private def gpu_setup_pipeline (ctx fnName function state wrapper : Bool) := {pipeFlags}
private def gpu_setup_buffer (ctx allocation wrapper : Bool) := {bufFlags}
private def gpu_setup_command (ctx command encoder wrapper : Bool) := {cmdFlags}

private theorem gpu_resource_completion
    (device queue source library contextWrapper command encoder commandWrapper completed : Bool)
    (pipelines : List (Bool × Bool × Bool × Bool)) (allocs : List (Bool × Bool))
    (read : Unit → α) (value : α) :
    let ctx := gpu_setup_context device queue source library contextWrapper
    let ready := pipelines.all (fun x => gpu_setup_pipeline ctx x.1 x.2.1 x.2.2.1 x.2.2.2) &&
      allocs.all (fun x => gpu_setup_buffer ctx x.1 x.2)
    let exit := if ready && gpu_setup_command ctx command encoder commandWrapper then
      MetalCompletion.Exit.submitted completed else .setupFailure
    MetalCompletion.afterWait exit read = .ok value ↔
      device=true ∧ queue=true ∧ source=true ∧ library=true ∧ contextWrapper=true ∧
      (∀ x ∈ pipelines, x.1=true ∧ x.2.1=true ∧ x.2.2.1=true ∧ x.2.2.2=true) ∧
      (∀ x ∈ allocs, x.1=true ∧ x.2=true) ∧ command=true ∧ encoder=true ∧ commandWrapper=true ∧
      completed=true ∧ value=read () := by
  intro ctx ready exit
  have fromExit : exit=.submitted true ↔ (ready && gpu_setup_command ctx command encoder commandWrapper)=true ∧ completed=true := by
    unfold exit
    split <;> rename_i cond <;> simp [cond]
  rw [MetalCompletion.wait_success,fromExit]
  have valid : ctx=true ↔ device=true ∧ queue=true ∧ source=true ∧ library=true ∧ contextWrapper=true := by
    simp only [ctx,gpu_setup_context,Bool.and_eq_true,and_assoc]
  by_cases on : ctx=true
  · have ⟨d,q,s,l,w⟩ := valid.mp on
    simp only [d,q,s,l,w,true_and,ready,gpu_setup_pipeline,gpu_setup_buffer,gpu_setup_command,on,
      Bool.true_and,Bool.and_eq_true,List.all_eq_true,and_assoc]
  · have off : ctx=false := Bool.eq_false_iff.mpr on
    simp only [gpu_setup_command,off,Bool.false_and,Bool.and_false,Bool.false_eq_true,false_and,false_iff]
    tauto
"""
