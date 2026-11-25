"""Check Metal host resource lifetimes and feed the extracted encoder traces to Lean."""

from collections import Counter
import re
import runpy
from pathlib import Path

completion = runpy.run_path(str(Path(__file__).parent / "metal-proof/completion.py"))
keygen_output = runpy.run_path(str(Path(__file__).parent / "metal-proof/keygen_output.py"))
fors_reducer = runpy.run_path(str(Path(__file__).parent / "metal-proof/fors_reducer.py"))
xmss_reducer = runpy.run_path(str(Path(__file__).parent / "metal-proof/xmss_reducer.py"))
fors_pk = runpy.run_path(str(Path(__file__).parent / "metal-proof/fors_pk.py"))
wots_output = runpy.run_path(str(Path(__file__).parent / "metal-proof/wots_output.py"))
leaf_dispatch = runpy.run_path(str(Path(__file__).parent / "metal-proof/leaf_dispatch.py"))


def compact(s):
    return re.sub(r"/\*.*?\*/|//[^\n]*|\s+", "", s, flags=re.S)


def body(source, marker):
    start = source.index("{", source.index(marker))
    depth = 1
    for pos in range(start + 1, len(source)):
        depth += (source[pos] == "{") - (source[pos] == "}")
        if not depth:
            return source[start + 1 : pos]
    raise ValueError(f"unterminated {marker}")


def verify_lifetime(lib, gpu, bridge):
    def exact(source, marker, expected):
        if body(source, marker) != compact(expected):
            raise ValueError(f"unreviewed completion or cleanup path in {marker}")

    lib, gpu, bridge = map(compact, (lib, gpu, bridge))
    ffi = "slh_metal_cmd_commit_and_wait(raw.as_ptr(),err.as_mut_ptr(),err.len())"
    exact(
        gpu,
        "fncommit_and_wait(mutself)",
        f"""
        let raw=self.raw.take().ok_or_else(||MetalError("command already committed".to_string()))?;
        let mut err=[0 as c_char;512]; let rc=unsafe{{{ffi}}};
        if rc==0{{Ok(())}}else{{Err(MetalError(read_err_buf(&err)))}}""",
    )
    exact(
        gpu,
        "implDropforMetalCommand",
        f"""
        fn drop(&mut self) {{if let Some(raw)=self.raw.take(){{
        let mut err=[0 as c_char;16];unsafe{{let _={ffi};}}}}}}""",
    )
    exact(
        bridge,
        "intslh_metal_cmd_commit_and_wait",
        """
        if(!cmd){write_err(err_buf,err_cap,@"null command buffer");return -1;}
        @autoreleasepool{SlhMetalCmdObj*obj=(__bridge_transfer SlhMetalCmdObj*)cmd;
        [obj.encoder endEncoding];[obj.cmdBuf commit];[obj.cmdBuf waitUntilCompleted];
        if([obj.cmdBuf status]!=MTLCommandBufferStatusCompleted){NSError*err=[obj.cmdBuf error];
        write_err(err_buf,err_cap,err?[err localizedDescription]:@"Metal command buffer failed");return -1;}
        return 0;}""",
    )
    exact(
        gpu,
        "fnbegin_cmd(&self,",
        """
        let raw=unsafe{slh_metal_cmd_begin(self.raw.as_ptr(),concurrent)};
        NonNull::new(raw).map(|raw|MetalCommand{raw:Some(raw)})
        .ok_or_else(||MetalError("failed to create Metal command buffer".to_string()))""",
    )
    exact(
        gpu,
        "fnbarrier(&mutself)",
        """
        if let Some(raw)=self.raw {unsafe{slh_metal_cmd_barrier(raw.as_ptr())};}""",
    )
    exact(
        bridge,
        "voidslh_metal_cmd_barrier",
        """
        if(!cmd){return;}@autoreleasepool{SlhMetalCmdObj*obj=(__bridge SlhMetalCmdObj*)cmd;
        if(obj.concurrent){[obj.encoder memoryBarrierWithScope:MTLBarrierScopeBuffers];}}""",
    )
    begin = body(bridge, "SlhMetalCmd*slh_metal_cmd_begin")
    for part in (
        "concurrent?[cmdBufcomputeCommandEncoderWithDispatchType:MTLDispatchTypeConcurrent]:[cmdBufcomputeCommandEncoder]",
        "cmd.cmdBuf=cmdBuf;cmd.encoder=encoder;cmd.concurrent=concurrent;",
    ):
        if part not in begin:
            raise ValueError("unexpected encoder type or command ownership")
    exact(
        lib,
        "implDropforScratchUse",
        "fn drop(&mut self){if let Some(keys)=&mut self.0.keys{keys.zeroize_contents();}}",
    )
    exact(
        lib,
        "fnensure<'a>(",
        """
        let need_alloc=match slot{Some(buf)=>buf.len()<min_bytes,None=>true,};
        if need_alloc{let cap=min_bytes.max(64);
        let buf=if secret{ctx.alloc_secret_buffer(cap)?}else{ctx.alloc_buffer(cap)?};
        *slot=Some(buf);}Ok(slot.as_mut().unwrap())""",
    )
    exact(
        gpu,
        "fnalloc_secret_buffer(",
        """
        let mut buf=self.alloc_buffer(len)?;buf.zeroize_on_drop=true;Ok(buf)""",
    )
    exact(
        gpu,
        "implDropforMetalBuffer",
        """
        fn drop(&mut self){if self.zeroize_on_drop{self.zeroize_contents();}
        unsafe{slh_metal_buffer_destroy(self.raw.as_ptr())};}""",
    )
    exact(gpu, "fnzeroize_contents", "self.as_mut_slice().zeroize();")


def public_signing(lib):
    """Match the entire accepted/rejected message wrapper, the actual primitive
    calls, and the final slice loop. Return only after these stages match."""
    src = compact(lib)
    def exact(name, expected):
        if body(src, name) != compact(expected):
            raise ValueError("GPU signer public framing or routing changed in " + name)

    exact("fnwith_context(", """
      let mut mp=Vec::with_capacity(2+ctx.len()+m.len());mp.push(0u8);
      mp.push(ctx.len() as u8);mp.extend_from_slice(ctx);mp.extend_from_slice(m);mp""")
    exact("fnsign_batch_family<", """
      if requests.iter().any(|r|r.ctx.len()>255){return Ok(None);}
      let framed:Vec<Vec<u8>>=requests.iter().map(|r|with_context(r.msg,r.ctx)).collect();
      let internal_reqs:Vec<SignInternalReq<'_,N>>=requests.iter().zip(framed.iter())
        .map(|(r,mp)|SignInternalReq{msg:mp.as_slice(),sk:r.sk,addrnd:r.addrnd,}).collect();
      self.sign_internal_batch_family::<N>(family,p,&internal_reqs).map(Some)""")
    for prefix, family in (("", "Sha2"), ("shake_", "Shake")):
        exact("pubfn"+prefix+"sign_batch<",f"self.sign_batch_family::<N>(HashFamily::{family}, p, requests)")
        exact("pubfn"+prefix+"sign<", """
          if ctx.len()>255{return Ok(None);}let mp=with_context(m,ctx);
          self."""+prefix+"sign_internal::<N>(p,&mp,sk,addrnd).map(Some)")
        exact("pubfn"+prefix+"sign_internal<", "let mut sigs=self."+prefix+
              "sign_internal_batch::<N>(p,&[SignInternalReq{msg:m,sk,addrnd,}],)?;Ok(sigs.pop().unwrap())")
        exact("pubfn"+prefix+"sign_internal_batch<",
              f"self.sign_internal_batch_family::<N>(HashFamily::{family},p,requests)")
        exact("pubfn"+prefix+"sign_deterministic<", "if ctx.len()>255{return Ok(None);}"
              "let pk_seed=block::<N>(sk,2);self."+prefix+"sign::<N>(p,m,ctx,sk,&pk_seed)")
        for method, args in (("sign_batch_same_key", ",addrnds"),("sign_deterministic_batch_same_key", "")):
            exact("pubfn"+prefix+method+"<",
                  f"self.{method}_family::<N>(HashFamily::{family},p,sk,messages,ctx{args})")
    exact("fnsign_batch_same_key_family<","""assert_eq!(messages.len(),addrnds.len());
      if ctx.len()>255{return Ok(None);}let reqs:Vec<SignReq<'_,N>>=messages.iter().zip(addrnds.iter())
      .map(|(&msg,&addrnd)|SignReq{msg,ctx,sk,addrnd,}).collect();self.sign_batch_family::<N>(family,p,&reqs)""")
    exact("fnsign_deterministic_batch_same_key_family<","""if ctx.len()>255{return Ok(None);}
      let pk_seed=block::<N>(sk,2);let reqs:Vec<SignReq<'_,N>>=messages.iter()
      .map(|&msg|SignReq{msg,ctx,sk,addrnd:&pk_seed,}).collect();self.sign_batch_family::<N>(family,p,&reqs)""")
    macro=body(src,"macro_rules!metal_set")
    for method,slot,args in (
        ("sign_internal","sg_int","m,sk,addrnd"),("sign","sg","m,ctx,sk,addrnd"),
        ("sign_deterministic","sg_det","m,ctx,sk"),("sign_batch_same_key","sg_batch","sk,messages,ctx,addrnds"),
        ("sign_deterministic_batch_same_key","sg_det_batch","sk,messages,ctx")):
        if body(macro,"pubfn"+method+"(")!=f"gpu.${slot}::<N>(&PARAMS,{args})":
            raise ValueError("per-set public signer forwarding changed")
    calls=re.findall(r"metal_set!\(([^)]*)\);",src)
    publicNames=set()
    for call in calls:
        name,module,*methods=call.split(",")
        prefix="shake_" if name.startswith("shake_") else ""
        expected=[prefix+m for m in ("keygen_internal","keygen","sign_internal","sign",
                  "sign_deterministic","sign_batch_same_key","sign_deterministic_batch_same_key")]
        if name!=module or methods!=expected or name in publicNames:
            raise ValueError("per-set parameter or backend binding changed: "+name)
        publicNames.add(name)
    if publicNames!={f"{f}_{s}" for f in ("shake","sha2") for s in ("128s","128f","192s","192f","256s","256f")}:
        raise ValueError("incomplete per-set Metal signing API")
    for name, bodyText in {
        "fnshake_prf_msg<": """let mut input=Vec::with_capacity(2*N+msg.len());
            input.extend_from_slice(sk_prf);input.extend_from_slice(opt_rand);input.extend_from_slice(msg);
            let mut out=[0u8;N];shake256(&input,&mut out);out""",
        "fnshake_h_msg<": """let mut input=Vec::with_capacity(3*N+msg.len());input.extend_from_slice(r);
            input.extend_from_slice(pk_seed);input.extend_from_slice(pk_root);input.extend_from_slice(msg);
            let mut out=vec![0u8;p.m];shake256(&input,&mut out);out""",
        "fnbuild_key_material<": """let seed=seed_ctx::<N>(pk_seed);let mut sk_words=[0u32;8];
            for i in 0..(N/4){sk_words[i]=u32::from_be_bytes([sk_seed[4*i],sk_seed[4*i+1],
            sk_seed[4*i+2],sk_seed[4*i+3],]);}KeyMaterial{sk_seed:sk_words,state256:seed.state,
            state512:seed.state512,}""",
        "fnbuild_shake_key_material<": """let mut sk_lanes=[0u64;4];let mut pk_lanes=[0u64;4];
            for i in 0..(N/8){sk_lanes[i]=u64::from_le_bytes(sk_seed[8*i..8*i+8].try_into().unwrap());
            pk_lanes[i]=u64::from_le_bytes(pk_seed[8*i..8*i+8].try_into().unwrap());}
            ShakeKeyMaterial{sk_seed:sk_lanes,pk_seed:pk_lanes,}""",
    }.items():
        exact(name, bodyText)
    internal = body(src, "fnsign_internal_batch_family<")
    if not internal.endswith(compact("""cmd.commit_and_wait()?;
        let sig_slice=pool.out_sigs.as_ref().unwrap().as_slice();let mut out=Vec::with_capacity(num_sigs);
        for sig_idx in 0..num_sigs{let off=sig_idx*sig_bytes;out.push(sig_slice[off..off+sig_bytes].to_vec());}
        Ok(out)""")):
        raise ValueError("GPU signer result slicing changed")
    if not internal.startswith(compact("""validate_geometry::<N>(p)?;let num_sigs=requests.len();
        if num_sigs==0{return Ok(Vec::new());}""")):
        raise ValueError("GPU signer empty-batch behavior changed")
    for imports in ("slhdsa::hash::{h_msg,prf_msg,seed_ctx}", "slhdsa::shake256::shake256",
                    "slhdsa::util::{base_2b,block,to_int}"):
        if "use"+imports+";" not in src:
            raise ValueError("GPU host primitive binding changed")
    req = body(internal, "for(sig_idx,req)inrequests.iter().enumerate()")
    expected = compact("""assert_eq!(req.sk.len(),4*N);
        let sk_seed:&[u8;N]=req.sk[..N].try_into().unwrap();let sk_prf=block::<N>(req.sk,1);
        let pk_seed:&[u8;N]=req.sk[2*N..3*N].try_into().unwrap();let pk_root=block::<N>(req.sk,3);
        let key_idx=match unique_seeds.iter().position(|(ss,ps)|ss==&sk_seed&&ps==&pk_seed){
          Some(idx)=>idx as u32,None=>{unique_seeds.push((sk_seed,pk_seed));(unique_seeds.len()-1)as u32}};
        let (r,digest)=match family{""")
    for prefix,family in (("","Sha2"), ("shake_","Shake")):
        expected += compact(f"""HashFamily::{family}=>{{let r={prefix}prf_msg::<N>(&sk_prf,req.addrnd,req.msg);
            let digest={prefix}h_msg::<N>(p,&r,pk_seed,&pk_root,req.msg);(r,digest)}}""")
    if req.split("letidx_tree=",1)[0] != expected+"};":
        raise ValueError("GPU host key selection or digest computation changed")


def scopes(source, pos):
    """Enclosing Rust blocks at one operation, excluding the function braces."""
    stack, start = [], 0
    for match in re.finditer(r"[{};]", source[:pos]):
        if match[0] == "{":
            stack.append(source[start : match.start()].strip(","))
        elif match[0] == "}":
            stack.pop()
        start = match.end()
    return stack


def check_descriptors(pre, signing):
    """Bind the descriptor constructors and each inline parameter value used
    by the checked kernels. The digest primitives supply valid input indices."""

    def one(fragment):
        if pre.count(compact(fragment)) != 1:
            raise ValueError("descriptor or parameter mismatch: " + fragment[:75])

    n = "total_trees" if signing else "count"
    hp = "hp," if signing else "hp:p.hp,"
    one(
        f"let xmss_params=XmssParams{{num_trees:{n} as u32,{hp}leaves_per_tree:leaves_per_tree as u32,wots_len:wots_len as u32,}};"
    )
    if not signing:
        one("let leaves_per_tree=1usize<<p.hp;")
        one("let total_leaves=count*leaves_per_tree;let wots_len=p.len();")
        return
    one("""let pipes=self.pipelines::<N>(family)?;let sig_bytes=p.sig_bytes();
        let fors_sig_bytes=p.fors_sig_bytes();let xmss_sig_bytes=p.xmss_sig_bytes();
        let wots_len=p.len();let d=p.d as usize;let hp=p.hp;let leaves_per_tree=1usize<<hp;""")
    one("let total_trees=num_sigs*d;let total_xmss_leaves=total_trees*leaves_per_tree;")
    one("let s1=if p.a<=8{p.a}else{7};let s2=p.a-s1;let subtrees_per_tree=1u32<<s2;")
    one(
        "let fors_params=ForsParams{num_sigs:num_sigs as u32,k:p.k,a:p.a,s1,s2,subtrees_per_tree,};"
    )
    one(
        "let wots_sign_params=WotsSignParams{num_layers:total_trees as u32,d:p.d,wots_len:wots_len as u32,};"
    )
    req = body(pre, "for(sig_idx,req)inrequests.iter().enumerate()")
    constructor = compact("""let idx_tree=digest_tree(p,&digest);let idx_leaf=digest_leaf(p,&digest);
        let md=&digest[0..p.md_bytes()];let fors_idx_vec=base_2b(md,p.a,p.k as usize);
        let sig_byte_off=(sig_idx*sig_bytes) as u32;
        let mut fjob=ForsJobDesc{idx_tree,key_idx,idx_leaf,sig_byte_off,_pad:0,indices:[0u32;36],};
        for(i,&idx)in fors_idx_vec.iter().enumerate(){fjob.indices[i]=idx;}
        fors_jobs_host.push(fjob);r_values.push(r);let mut tree=idx_tree;let mut leaf=idx_leaf;
        for j in 0..d { let layer_sig_off=sig_byte_off+(N+fors_sig_bytes+j*xmss_sig_bytes)as u32;
        let auth_byte_off=layer_sig_off+(wots_len*N)as u32;
        xmss_trees_host.push(XmssTreeDesc{tree,key_idx,layer:j as u32,target_leaf:leaf,auth_byte_off,});
        wots_layers_host.push(WotsSignLayerDesc{tree,key_idx,layer:j as u32,keypair:leaf,sig_idx:sig_idx as u32,
        wots_byte_off:layer_sig_off,_pad:0,});leaf=(tree&((1u64<<hp)-1))as u32;tree>>=hp;}""")
    if not req.endswith(constructor) or scopes(req, len(req) - len(constructor)):
        raise ValueError("signature descriptor construction or byte offset changed")
    one("""let key_idx=match unique_seeds.iter().position(|(ss,ps)|ss==&sk_seed&&ps==&pk_seed){
        Some(idx)=>idx as u32,None=>{unique_seeds.push((sk_seed,pk_seed));(unique_seeds.len()-1)as u32}};""")


def allocations(init, signing):
    scopes_by_role = {"chain_tips": ["ifuse_two_phase"], "fors_roots": ["ifs2>0"]}
    sizes = (
        {
            "xmss_trees": "total_trees*std::mem::size_of::<XmssTreeDesc>()",
            "fors_jobs": "num_sigs*std::mem::size_of::<ForsJobDesc>()",
            "wots_layers": "total_trees*std::mem::size_of::<WotsSignLayerDesc>()",
            "chain_tips": "total_xmss_leaves*wots_len*N",
            "xmss_leaves": "total_xmss_leaves*N",
            "xmss_roots": "total_trees*N",
            "fors_sub_roots": "num_sigs*(p.kasusize)*(subtrees_per_treeasusize)*N",
            "fors_roots": "num_sigs*(p.kasusize)*N",
            "pk_fors": "num_sigs*N",
            "out_sigs": "num_sigs*sig_bytes",
        }
        if signing
        else {
            "xmss_trees": "trees_bytes",
            "chain_tips": "tips_bytes",
            "xmss_leaves": "leaves_bytes",
            "xmss_roots": "roots_bytes",
            "out_sigs": "16",
        }
    )
    pattern = (
        r"ScratchPool::ensure\(&self.ctx,&mutpool\.(\w+),([^;]+?),(true|false),?\)\?;"
    )
    seen = []
    for site in re.finditer(pattern, init):
        name, size, secret = site.groups()
        path = [scope for scope in scopes(init, site.start()) if scope]
        if name == "keys":
            if path not in (
                ["matchfamily", "HashFamily::Sha2=>"],
                ["matchfamily", "HashFamily::Shake=>"],
            ):
                raise ValueError("conditional key allocation")
            typ = (
                "KeyMaterial"
                if path[-1] == "HashFamily::Sha2=>"
                else "ShakeKeyMaterial"
            )
            expected = (
                f"num_keys*std::mem::size_of::<{typ}>()" if signing else "keys_bytes"
            )
            if (
                not signing
                and f"letkeys_bytes=count*std::mem::size_of::<{typ}>();letkeys_buf="
                not in init[: site.start()]
            ):
                raise ValueError("incorrect key allocation extent")
        else:
            expected = sizes[name]
            if path != scopes_by_role.get(name, []):
                raise ValueError(f"{name}: unexpected allocation condition")
        if size != expected or (secret == "true") != (name == "keys"):
            raise ValueError(f"{name}: incorrect allocation extent or secrecy")
        seen.append(name)
    if Counter(seen) != Counter(["keys", "keys", *sizes]) or len(seen) != init.count(
        "ScratchPool::ensure("
    ):
        raise ValueError("unrecognized scratch buffer allocation")
    if not signing:
        for fragment in (
            "lettrees_bytes=count*std::mem::size_of::<XmssTreeDesc>();",
            "letleaves_bytes=total_leaves*N;",
            "letroots_bytes=count*N;",
            "lettips_bytes=total_leaves*wots_len*N;",
        ):
            if init.count(fragment) != 1:
                raise ValueError("incorrect keygen scratch allocation extent")


def geometry_sources(lib, params, sets):
    params = compact(params)
    for formula, value in {
        "len": "2*self.n+LEN2",
        "xmss_sig_bytes": "(self.len()+self.hpasusize)*self.n",
        "fors_sig_bytes": "(self.k*(1+self.a))asusize*self.n",
        "sig_bytes": "self.n+self.fors_sig_bytes()+self.dasusize*self.xmss_sig_bytes()",
        "md_bytes": "((self.k*self.a+7)/8)asusize",
        "tree_bits": "self.h-self.hp",
        "tree_bytes": "((self.h-self.hp+7)/8)asusize",
        "leaf_bytes": "((self.hp+7)/8)asusize",
    }.items():
        if body(params, f"fn{formula}(&self)") != value:
            raise ValueError(f"production parameter calculation {formula} changed")
    if "constLEN2:usize=3;" not in params:
        raise ValueError("WOTS checksum width changed")
    for name, family, n, h, d, hp, a, k, m in sets:
        row = "SHA2_" + name.split("-")[1].upper()
        fields = f"n:{n},h:{h},d:{d},hp:{hp},a:{a},k:{k},m:{m}"
        if body(params, f"const{row}:Params=Params") != fields:
            raise ValueError(f"{name}: production geometry differs from trace")
    for proc, expected in {
        "digest_tree": "letlo=p.md_bytes();to_int(&digest[lo..lo+p.tree_bytes()])&(u64::MAX>>(64-p.tree_bits()))",
        "digest_leaf": "letlo=p.md_bytes()+p.tree_bytes();(to_int(&digest[lo..lo+p.leaf_bytes()])&((1u64<<p.hp)-1))asu32",
    }.items():
        if body(compact(lib), f"fn{proc}(") != expected:
            raise ValueError(f"{proc}: index prefix or mask changed")


def host_access(lib, signing, shake):
    op = "sign" if signing else "keygen"
    fn = body(compact(lib), f"fn{op}_internal_batch_family<")
    guard = "letmutlocked=self.pool.lock().unwrap();letcleanup=ScratchUse(&mutlocked);letpool=&mut*cleanup.0;"
    begin = f"letmutcmd=self.ctx.begin_cmd({str(signing).lower()})?;"
    wait = "cmd.commit_and_wait()?;"
    for token in (guard, begin, wait):
        if fn.count(token) != 1 or scopes(fn, fn.index(token)):
            raise ValueError(f"{op}: expected unconditional {token}")
    pre, commands = fn.split(begin)
    check_descriptors(pre, signing)
    setup, init = pre.split(guard)
    commands, post = commands.split(wait)
    allocations(init, signing)
    if re.search(
        r"\.as_(?:mut_)?slice(?:_of)?\b|\.zeroize_contents\(|(?:drop|forget)\((?:cleanup|cmd|locked)\)",
        commands,
    ):
        raise ValueError(f"{op}: CPU access while command is outstanding")
    if re.search(r"pool\.(?:keys|xmss_|out_sigs)|\.as_mut_slice", setup) or any(
        x in init + commands + post
        for x in ("drop(cleanup)", "forget(cleanup)", "drop(locked)", "forget(locked)")
    ):
        raise ValueError(f"{op}: pool ownership bypass")
    bindings = re.findall(
        r"let(\w+)=ScratchPool::ensure\(&self.ctx,&mutpool\.(\w+),", init
    )
    expected = [("keys_buf", "keys")] * 2 + [("trees_buf", "xmss_trees")]
    if signing:
        expected += [
            ("fjobs_buf", "fors_jobs"),
            ("wlayers_buf", "wots_layers"),
            ("out_sigs_buf", "out_sigs"),
        ]
    if Counter(bindings) != Counter(expected):
        raise ValueError(f"{op}: CPU initialization bound to wrong allocation")
    family = "Shake" if shake else "Sha2"
    count = "num_keys" if signing else "count"
    key_type = "ShakeKeyMaterial" if shake else "KeyMaterial"
    make = "build_shake_key_material" if shake else "build_key_material"
    keys = (
        "for(i,(sk_seed,pk_seed))inunique_seeds.iter().enumerate()"
        if signing
        else "for(i,(sk_seed,_sk_prf,pk_seed))inbatch.iter().enumerate()"
    )
    key_write = (
        f"letkm_slice=keys_buf.as_mut_slice_of::<{key_type}>({count});"
        f"{keys}{{km_slice[i]={make}::<N>(sk_seed,pk_seed);}}"
    )

    def located(source, marker, nested):
        if source.count(marker) != 1 or scopes(source, source.index(marker)) != nested:
            raise ValueError(
                f"{op}/{family}: missing or conditional host access {marker}"
            )

    leaves = "total_xmss_leaves" if signing else "total_leaves"
    located(commands, f"lettotal_chains=({leaves}*wots_len)asu32;", ["ifuse_two_phase"])
    if signing:
        located(commands, "lettotal_wots_chains=(total_trees*wots_len)asu32;", [])
        located(setup, "ifuse_two_phase{check_grid(num_sigs,d*leaves_per_tree*wots_len*words)?;}", [])
        located(setup, "letwords=N/iffamily==HashFamily::Shake{8}else{4};", [])
    located(init, key_write, ["matchfamily", f"HashFamily::{family}=>"])
    ready = ["keys", "xmss_trees"]
    if signing:
        for buf, typ, n, values in (
            ("trees_buf", "XmssTreeDesc", "total_trees", "xmss_trees_host"),
            ("fjobs_buf", "ForsJobDesc", "num_sigs", "fors_jobs_host"),
            ("wlayers_buf", "WotsSignLayerDesc", "total_trees", "wots_layers_host"),
        ):
            located(
                init,
                f"{buf}.as_mut_slice_of::<{typ}>({n}).copy_from_slice(&{values});",
                [""],
            )
        located(
            init,
            "letsig_slice=out_sigs_buf.as_mut_slice();for(sig_idx,r)inr_values.iter().enumerate(){"
            "letoff=sig_idx*sig_bytes;sig_slice[off..off+N].copy_from_slice(r);}",
            [""],
        )
        located(post, "letsig_slice=pool.out_sigs.as_ref().unwrap().as_slice();", [])
        ready.extend(["fors_jobs", "wots_layers", "randomizer"])
    else:
        located(
            init,
            "lettd_slice=trees_buf.as_mut_slice_of::<XmssTreeDesc>(count);"
            "for(i,td)intd_slice.iter_mut().enumerate(){*td=XmssTreeDesc{tree:0,key_idx:iasu32,"
            "layer:p.d-1,target_leaf:u32::MAX,auth_byte_off:0,};}",
            [""],
        )
        suffix = "lanes" if shake else "words"
        t = "u64" if shake else "u32"
        n = "nl" if shake else "nw"
        located(
            post,
            f"letroots_{suffix}=pool.xmss_roots.as_ref().unwrap().as_slice_of::<{t}>(count*{n});",
            ["matchfamily", f"HashFamily::{family}=>"],
        )
    # No other CPU buffer views in these functions.
    views = r"\.as_(?:mut_)?slice(?:_of)?(?=::<|\()"
    if len(re.findall(views, init)) != (6 if signing else 3) or len(
        re.findall(views, post)
    ) != (1 if signing else 2):
        raise ValueError(f"{op}: unmodeled host resource access")
    return ready


def shader_access(msl, prefix, roles):
    """Infer all buffer access directions from the interface; bind every use
    of a writable device pointer to a store or a signature fragment writer."""
    shader = re.sub(r"/\*.*?\*/|//[^\n]*", "", msl, flags=re.S)
    ret = {}
    for kernel, args in re.findall(
        r"kernel void (\w+)_##SUFFIX\s*\((.*?)\)\s*\\?\s*\{", shader, re.S
    ):
        name = kernel.removeprefix(prefix)
        impl = compact(body(shader, f"void {kernel}_impl("))
        reads, writes = [], []
        for const, param in re.findall(
            r"(const\s+)?device\s+\w+\s*\*\s*(\w+)\s*\[\[buffer", args
        ):
            role = roles[param]
            if const:
                reads.append(role)
                continue
            if param != "out_sigs":
                uses = re.findall(rf"\b{param}\b", body(shader, f"void {kernel}_impl("))
                stores = re.findall(rf"{param}\[out_off\+i\]=\w+\[i\];", impl)
                if len(uses) != 1 or len(stores) != 1:
                    raise ValueError(f"{kernel}: unreviewed use of writable {param}")
                writes.append(role)
                continue
            offsets = re.findall(
                r"write_(?:shake_)?node_bytes(?:_tg)?<N[WL]>\(out_sigs\+([^,]+),", impl
            )
            width = "NL*8u" if prefix else "NW*4u"
            sites = {
                "xmss_reduce": [
                    "desc.auth_byte_off",
                    "desc.auth_byte_off+(lvl-1u)*" + width,
                ],
                "fors_pass1": ["fors_tree_sig_off", "fors_tree_sig_off+n_bytes"] * 2
                + ["fors_tree_sig_off+lvl*n_bytes"],
                "fors_pass2": ["fors_tree_sig_off+lvl1*n_bytes"] * 2
                + ["fors_tree_sig_off+lvl*n_bytes"],
                "wots_sign": ["desc.wots_byte_off+chain*" + width],
            }
            if offsets != sites.get(name) or impl.count("out_sigs") != len(offsets):
                raise ValueError(f"{kernel}: signature access region changed")
            writes.append(
                {
                    "xmss_reduce": "xmssAuth",
                    "fors_pass1": "forsLow",
                    "fors_pass2": "forsHigh",
                    "wots_sign": "wots",
                }[name]
            )
        ret[name] = reads, writes
    return ret


def region_list(regions):
    return "[" + ",".join("." + r for r in regions) + "]"


def chain_projection(msl, shake, *, negative=False):
    """Translate the integer expressions of one whole chain-tip kernel. The
    accepted store, uniform, and key-load grammar is deliberately closed."""
    prefix, width, word, seed = (
        ("shake_", "NL", "uint64_t", "pk_seed") if shake
        else ("", "NW", "uint32_t", "seed_st")
    )
    loads = (
        """uint64_t pk_seed[NL], sk_seed[NL];
           for (uint i = 0; i < NL; ++i) {
             pk_seed[i] = keys[desc.key_idx].pk_seed[i]; sk_seed[i] = keys[desc.key_idx].sk_seed[i];
           }""" if shake else
        """uint32_t seed_st[8]; uint32_t sk_seed[NW];
           for (uint i = 0; i < 8; ++i) seed_st[i] = keys[desc.key_idx].state256[i];
           for (uint i = 0; i < NW; ++i) sk_seed[i] = keys[desc.key_idx].sk_seed[i];"""
    )
    primitive = (
        """uint64_t ad0, ad1, ad2, ad3;
           adrs_full_lanes(layer, tree, ADRS_WOTS_PRF, keypair, chain, 0u, ad0, ad1, ad2, ad3);
           shake_thash_short<NL>(pk_seed, ad0, ad1, ad2, ad3, sk_seed, val);
           if (steps == 0u) return;
           ad2 &= 0xFFFFFFFF00000000ul;
           uint64_t ad3_base = uint64_t(bswap32(chain));
           for (uint32_t s = 0u; s < steps; ++s) {
               uint64_t ad3_s = ad3_base | (uint64_t(bswap32(s)) << 32);
               shake_thash_short<NL>(pk_seed, ad0, ad1, ad2, ad3_s, val, val);
           }""" if shake else
        """uint32_t w0, w1, w2, w3, w4, w5_hi;
           adrs_to_w256(layer, tree, ADRS_WOTS_PRF, keypair, chain, 0u, w0, w1, w2, w3, w4, w5_hi);
           thash_short_words<NW>(seed_st, w0, w1, w2, w3, w4, 0u, sk_seed, val);
           if (steps == 0u) { return; }
           w2 &= 0xFF00FFFFu;
           for (uint32_t s = 0u; s < steps; ++s) {
               thash_short_words<NW>(seed_st, w0, w1, w2, w3, w4, s << 16, val, val);
           }"""
    )
    if compact(body(msl, f"void {prefix}run_wots_chain(")) != compact(primitive):
        raise ValueError(f"{prefix}run_wots_chain: unmodeled primitive loop")
    template = f"""
        uint32_t total_chains = p.num_trees * p.leaves_per_tree * p.wots_len;
        if (gid >= total_chains) return;
        uint32_t chain = gid OP0 p.wots_len;
        uint32_t leaf_global = gid OP1 p.wots_len;
        uint32_t leaf_idx = leaf_global OP2 p.leaves_per_tree;
        uint32_t tree_idx = leaf_global OP3 p.leaves_per_tree;
        XmssTreeDesc desc = trees[tree_idx]; {loads}
        {word} tip[{width}];
        {prefix}run_wots_chain<{width}>({seed}, sk_seed, desc.layer, desc.tree, leaf_idx, chain, STEPSu, tip);
        uint32_t out_off = gid * {width};
        for (uint i = 0; i < {width}; ++i) {{out_chain_tips[out_off + i] = tip[i];}}
    """
    pattern = re.escape(compact(template))
    for i in range(4):
        pattern = pattern.replace(f"OP{i}", r"([/%])")
    pattern = pattern.replace("STEPS", r"([0-9]+)")
    parsed = re.fullmatch(pattern, compact(body(msl, f"void {prefix}wots_chains_impl(")))
    if not parsed:
        raise ValueError(f"{prefix}wots_chains: unmodeled statement or memory access")
    chain, leaf_global, leaf, tree, steps = parsed.groups()
    name = "shakeChainTip" if shake else "sha2ChainTip"
    if negative:
        name += "Mutated"
    goal = f"{name} p e gid = MetalPipeline.metalWotsChainsKernel p e.keys e.trees gid"
    proof = f"simp only [{name}, MetalChainDispatch.chainLoop_spec]\n  rfl"
    if negative:
        # Concrete address counterexample avoids reducing the cryptographic
        # functions merely to distinguish two different chain addresses.
        goal, proof = f"{name}Index 38 35 ≠ 3", "decide"
    binders = "" if negative else "(p : Spec.Params) (e : MetalChainDispatch.Execution) (gid : Nat)"
    return f"""
private def {name}Index (gid len : Nat) := gid {chain} len

private def {name} (p : Spec.Params) (e : MetalChainDispatch.Execution) (gid : Nat) : Spec.Bytes :=
  let chain := {name}Index gid p.len
  let leafGlobal := gid {leaf_global} p.len
  let leafIdx := leafGlobal {leaf} (2 ^ p.hp)
  let treeIdx := leafGlobal {tree} (2 ^ p.hp)
  let desc := e.trees treeIdx
  let key := e.keys desc.keyIdx
  MetalChainDispatch.chainLoop p key.1 key.2 desc.layer desc.tree leafIdx chain {steps}

private theorem {name}_spec {binders} :
    {goal} := by
  {proof}
"""


def chain_public_claim(label, cmd, p, g, n, word_size, tip):
    count = f"(rs.length * {p}.d * (2 ^ {p}.hp) * {p}.len)"
    spec = f"(MetalPipeline.metalBatchSignInternal .twoPhase {p} (MetalCommandValues.framed rs)).flatten"
    scratch = f"(MetalChainDispatch.invariant {p} {count} {n//word_size} {word_size} e ({tip} {p} e) keys trees other)"
    correct = f"(MetalCommandValues.correct {g} (MetalCommandValues.framed rs).length (pool.take (rs.length * {p}.sigBytes)) {spec} {scratch})"
    return f"""
private theorem {label}_chains (rs : List MetalPipeline.BatchSignReq) (pool : Spec.Bytes)
    (e : MetalChainDispatch.Execution) (keys : MetalChainDispatch.Keys)
    (trees : MetalChainDispatch.Trees) (other : MetalCommand.Region → Prop)
    (accepted : rs.any (fun r => decide (r.ctx.length > 255)) = false →
      rs.length * {p}.sigBytes ≤ pool.length ∧
      e.schedule.Perm (MetalChainDispatch.grid {count} {n//word_size}) ∧
      ∀ a ∈ {label}, a ≠ {cmd} → (∀ r ∈ a.reads, {correct} r) → ∀ r ∈ a.writes, {correct} r) :
    MetalCommandValues.publicResult {p} rs pool =
      rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd) := by
  apply {label}_public rs pool {scratch}
  intro guard
  obtain ⟨allocation, schedule, remaining⟩ := accepted guard
  exact ⟨allocation, MetalChainDispatch.local_of_dispatch {label} {cmd} (by decide) (by decide)
    {p} {count} {n//word_size} {word_size} e keys trees other ({tip} {p} e)
    (fun gid _ => {tip}_spec {p} e gid) (MetalChainDispatch.covers_grid schedule)
    {g} _ _ _ remaining⟩
"""


def claims(
    lib,
    gpu,
    bridge,
    sha2,
    shake,
    traces,
    roles,
    *,
    unsafe_case=lambda sign, phase, split: False,
    rows=(),
):
    verify_lifetime(lib, gpu, bridge)
    statements = []
    for is_shake, msl in enumerate((sha2, shake)):
        accesses = shader_access(msl, "shake_" if is_shake else "", roles)
        for (sign, phase, split), events in traces.items():
            ready = host_access(lib, sign, is_shake)
            trace = [(0, [], ready)]
            for name, epoch in events:
                reads, writes = accesses[name]
                if not sign and name == "xmss_reduce":
                    writes = [r for r in writes if r != "xmssAuth"]
                if not split and name == "fors_pk":
                    reads = [
                        "fors_sub_roots" if r == "fors_roots" else r for r in reads
                    ]
                trace.append((epoch + 1, reads, writes))
            output = (
                ["randomizer", "forsLow", "xmssAuth", "wots"]
                if sign
                else ["xmss_roots"]
            )
            if sign and split:
                output.append("forsHigh")
            trace.append((trace[-1][0] + 1, output, []))
            entries = ",".join(
                f"⟨{i},{region_list(r)},{region_list(w)}⟩" for i, r, w in trace
            )
            expected = "false" if unsafe_case(sign, phase, split) else "true"
            statements.append(
                f"example : MetalCommand.safe [{entries}] = {expected} := by decide"
            )
            if not sign and not split and expected=="true":
                for rowName, family, n, *_ in rows:
                    if (family == "shake") == bool(is_shake):
                        stem = f"gpu_{rowName.replace('-', '_')}_{int(phase)}_kg"
                        statements.append(keygen_output["claims"](stem,"Spec."+rowName.replace("-","_"),family,n,phase,entries))
            if sign and expected=="true":
                splitBool = str(bool(split)).lower()
                i,r,w=trace[-1]
                reader = f"(⟨{i},{region_list(r)},{region_list(w)}⟩ : MetalCommand.Access)"
                # Kernel-check the link for each actual trace with arbitrary
                # batch cardinality and descriptor geometry of this split.
                statements.append(
                    f"example (g : MetalSignatureLayout.Geometry) "
                    f"(hi : {splitBool} = false → g.s2 = 0) (count : Nat) "
                    f"(b : MetalSignatureLayout.Byte g count) : "
                    f"∃ a ∈ ([{entries}] : List MetalCommand.Access), "
                    f"MetalCommandValues.owner g b.2.1 ∈ a.writes := "
                    f"MetalCommandValues.published (by decide) g {splitBool} hi {reader} "
                    f"(by decide) (by decide) b"
                )
                # Instantiate the public arbitrary-batch statement for every
                # production parameter row that uses this exact command trace.
                for rowName,family,n,_,d,hp,a,k,_ in rows:
                    if (family=="shake") != bool(is_shake) or (a>8) != bool(split):
                        continue
                    s1=a if a<=8 else 7
                    g=f"(⟨{n},{k},{s1},{a-s1},{d},{2*n+3},{hp}⟩ : MetalSignatureLayout.Geometry)"
                    p="Spec."+rowName.replace("-","_")
                    mode=(".twoPhase" if phase else ".streaming")
                    label="gpu_"+rowName.replace("-","_")+"_"+str(int(phase))
                    statements += [f"private def {label} : List MetalCommand.Access := [{entries}]", f"""
private theorem {label}_public (rs : List MetalPipeline.BatchSignReq) (pool : Spec.Bytes) (scratch : MetalCommand.Region → Prop)
  (accepted : rs.any (fun r => decide (r.ctx.length > 255)) = false →
    rs.length * {p}.sigBytes ≤ pool.length ∧
    MetalCommandValues.Local {label} (MetalCommandValues.correct {g} (MetalCommandValues.framed rs).length
       (pool.take (rs.length * {p}.sigBytes))
       (MetalPipeline.metalBatchSignInternal {mode} {p} (MetalCommandValues.framed rs)).flatten scratch)) :
  MetalCommandValues.publicResult {p} rs pool =
    rs.mapM (fun r => Spec.slhSign {p} r.msg r.ctx r.sk r.addrnd) :=
  MetalCommandValues.public_pooled_batch (trace := {label}) (by decide)
    {p} (MetalPipeline.metal_all_12_params_valid _ (by decide)) {mode}
    {g} (by decide) rs pool scratch (fun guard =>
      ⟨(accepted guard).1, fun b =>
        MetalCommandValues.published (trace := {label}) (by decide) {g} {splitBool}
          (by decide) {reader} (by decide) (by decide) b, (accepted guard).2⟩)
"""]
                    def producer(region):
                        epoch, inputs, outputs = next(entry for entry in trace if region in entry[2])
                        return f"(⟨{epoch},{region_list(inputs)},{region_list(outputs)}⟩ : MetalCommand.Access)"
                    source_cmd = producer("chain_tips") if phase else None
                    if phase:
                        statements.append(chain_public_claim(
                            label, source_cmd, p, g, n, 8 if is_shake else 4,
                            "shakeChainTip" if is_shake else "sha2ChainTip",
                        ))
                    leaves_claim, leaf_scratch = leaf_dispatch["public_claim"](
                        label, p, g, family, n, phase, producer("xmss_leaves"), source_cmd,
                    )
                    statements.append(leaves_claim)
                    fp = (producer("pk_fors"), splitBool)
                    host = producer("randomizer")
                    for fors_stage, host_cmd, xmss_stage in (
                        (None, None, None), (fp, None, None), (fp, host, None),
                        (fp, host, (xmss_reducer, producer("xmss_roots"))),
                    ):
                        statements.append(wots_output["public_claim"](
                            label, p, g, family, n, phase, producer("xmss_leaves"),
                            source_cmd, producer("wots"), leaf_scratch, fors_stage=fors_stage, host_cmd=host_cmd, xmss_stage=xmss_stage,
                        ))
                    statements.append(wots_output["public_claim"](
                        label, p, g, family, n, phase, producer("xmss_leaves"), source_cmd, producer("wots"), leaf_scratch,
                        fors_stage=fp, host_cmd=host, xmss_stage=(xmss_reducer, producer("xmss_roots")),
                        forest=(fors_reducer, s1, a-s1),
                    ))
    return "\n".join(statements)


def verify(lib, gpu, bridge, sha2, shake, bindings, rows=()):
    args = [lib, gpu, bridge, sha2, shake]
    traces = bindings["check_stages"](lib)
    roles = bindings["SHADER_ROLES"]
    public_signing(lib)
    keygen_output["host"](lib, compact, body)
    for before, after in (
        ("pk.extend_from_slice(pk_root);","pk.extend_from_slice(pk_seed);"),
        ("&lanes[i].to_le_bytes()","&lanes[i].to_be_bytes()"),
        ("roots_words[i * nw..(i + 1) * nw]","roots_words[0..nw]"),
    ):
        try:
            keygen_output["host"](lib.replace(before,after), compact, body)
        except ValueError as error:
            if "changed keygen" not in str(error):
                raise
        else:
            raise ValueError("accepted keygen host value mutation")
    for before, after in (
        ("requests.iter().any(|r| r.ctx.len() > 255)", "requests.iter().any(|r| r.ctx.len() >= 255)"),
        ("mp.push(0u8);", "mp.push(1u8);"),
        ("out.push(sig_slice[off..off + sig_bytes].to_vec());",
         "out.insert(0, sig_slice[off..off + sig_bytes].to_vec());"),
        ("input.extend_from_slice(opt_rand);", "input.extend_from_slice(sk_prf);"),
    ):
        if lib.count(before)!=1:
            raise ValueError("ambiguous public wrapper mutation: " + before)
        try:
            public_signing(lib.replace(before,after))
        except ValueError:
            continue
        raise ValueError("public wrapper mutation accepted: " + before)
    projections = []
    for is_shake, shader in enumerate((sha2, shake)):
        projections.append(chain_projection(shader, is_shake))
        forest = fors_reducer["project"]
        projections.append(forest(shader, is_shake, body, compact))
        for before, after in (
            ("leaf1_word3 = leaf0_word3 + 1u", "leaf1_word3 = leaf0_word3 + 2u"),
            ("sib1 = (target >> p.s1) ^ 1u", "sib1 = (target >> p.s1) ^ 0u"),
        ):
            try:
                forest(shader.replace(before, after), is_shake, body, compact)
            except ValueError as error:
                if "unreviewed FORS reducer body" not in str(error):
                    raise
            else:
                raise ValueError("accepted a modified FORS reducer operand")
        xp = xmss_reducer["project"]
        projections.append(xp(shader, is_shake, body, compact))
        mutant = shader.replace("cur_cnt >>= 1;", "cur_cnt >>= 2;")
        try:
            xp(mutant, is_shake, body, compact)
        except ValueError as error:
            if "unmodeled reducer phase" not in str(error):
                raise
        else:
            raise ValueError("accepted wrong XMSS reduction depth")
        fp = fors_pk["project"]
        projections.append(fp(shader, is_shake, body, compact, leaf_dispatch["kernel_body"]))
        base = "sig_idx * p.k * " + ("NL" if is_shake else "NW")
        try:
            fp(shader.replace(base, "sig_idx * p.k"), is_shake, body, compact, leaf_dispatch["kernel_body"])
        except ValueError as error:
            if "unmodeled" not in str(error):
                raise
        else:
            raise ValueError("accepted FORS roots with wrong batch stride")
        projects = wots_output["project"]
        projections.append(projects(shader, is_shake, body, compact))
        projections.append(projects(shader.replace("(desc.layer - 1u)", "(desc.layer - 0u)"),
            is_shake, body, compact, previous_layer_counterexample=True))
        corrupted = shader.replace("uint32_t c_idx = chain - len1;", "uint32_t c_idx = chain;")
        try:
            projects(corrupted, is_shake, body, compact)
        except ValueError as error:
            if "unmodeled WOTS value or serialization" not in str(error):
                raise
        else:
            raise ValueError("accepted shifted WOTS checksum index")
        for streaming in (False, True):
            project = leaf_dispatch["project"]
            projections.append(project(shader, is_shake, streaming, body, compact))
            # Corrupt a leaf output and a hash-stream input independently.
            order_site = {
                (False, False): ("s.push_word(chain_tips[off + 2u]);", "s.push_word(chain_tips[off + 1u]);"),
                (False, True): ("s.push_word(tip[2]);", "s.push_word(tip[1]);"),
                (True, False): ("sp.absorb_lane(chain_tips[tip_base + i]);", "sp.absorb_lane(chain_tips[tip_base]);"),
                (True, True): ("sp.absorb_lane(tip[i]);", "sp.absorb_lane(tip[0]);"),
            }[bool(is_shake), streaming]
            for before, after in (
                ("out_leaves[out_off + i] = leaf[i];", "out_leaves[out_off + i] = leaf[0];"),
                order_site,
            ):
                try:
                    project(shader.replace(before, after), is_shake, streaming, body, compact)
                except ValueError as error:
                    if "unmodeled leaf projection" not in str(error):
                        raise
                else:
                    raise ValueError(f"accepted incorrect XMSS leaf operation: {after}")
        # Valid MSL division in place of modulo still translates; Lean's
        # concrete counterexample must differ. A changed output store must fail parsing.
        projections.append(chain_projection(shader.replace(
            "uint32_t chain = gid % p.wots_len;", "uint32_t chain = gid / p.wots_len;"
        ), is_shake, negative=True))
        try:
            chain_projection(shader.replace("out_chain_tips[out_off + i] = tip[i];",
                "out_chain_tips[out_off + i] = tip[0];"), is_shake)
        except ValueError as error:
            if "unmodeled statement or memory access" not in str(error):
                raise
        else:
            raise ValueError("accepted broadcast rather than per-word chain-tip store")
    positive = "\n".join(projections) + claims(*args, traces, roles, rows=rows)
    positive += completion["project"](lib, compact, body, rows)
    # A missing wait, premature result view or omitted host producer must fail
    # against the actual source, independent of the positive trace assertions.
    cases = [
        (1, "if rc == 0 {", "if rc != 0 {", "cleanup path"),
        (2, "[obj.cmdBuf status] != MTLCommandBufferStatusCompleted", "[obj.cmdBuf status] == MTLCommandBufferStatusCompleted", "cleanup path"),
        (2, "[obj.cmdBuf waitUntilCompleted];", "", "cleanup path"),
        (2, "[obj.cmdBuf commit];", "return -1; [obj.cmdBuf commit];", "cleanup path"),
        (
            1,
            "let _ = slh_metal_cmd_commit_and_wait",
            "let _ = skip_wait",
            "cleanup path",
        ),
        (0, "sig_slice[off..off + N].copy_from_slice(r);", "", "host access"),
        (0, "let total_chains = (total_xmss_leaves * wots_len) as u32;",
            "let total_chains = (total_xmss_leaves * wots_len - 1) as u32;", "host access"),
        (
            0,
            "let auth_byte_off = layer_sig_off +",
            "let auth_byte_off = sig_byte_off +",
            "descriptor construction",
        ),
        (
            0,
            "num_layers: total_trees as u32,",
            "num_layers: num_sigs as u32,",
            "parameter mismatch",
        ),
        (
            0,
            "cmd.commit_and_wait()?;",
            "let _early = pool.xmss_roots.as_ref().unwrap().as_slice();cmd.commit_and_wait()?;",
            "outstanding",
        ),
        (
            0,
            "total_xmss_leaves * wots_len * N,",
            "total_xmss_leaves * N,",
            "allocation extent",
        ),
        (
            4,
            "out_sigs + desc.wots_byte_off",
            "out_sigs + desc.auth_byte_off",
            "access region",
        ),
    ]
    for index, old, new, error in cases:
        mutated = args.copy()
        if not mutated[index].count(old):
            raise ValueError(f"missing mutation target {old}")
        mutated[index] = mutated[index].replace(old, new, 1)
        try:
            claims(*mutated, traces, roles)
        except ValueError as caught:
            if error not in str(caught):
                raise
        else:
            raise AssertionError(f"accepted mutation to {old}")
    # Removing either dependency barrier yields decoded, well-formed Rust
    # control flow, but puts an actual producer and consumer in the same epoch.
    bad_graphs = []
    for marker, replacement, affected in [
        ("cmd.barrier();", "", lambda sign, phase, split: sign),
        (
            "if need_stage3_barrier {",
            "if false {",
            lambda sign, phase, split: sign and (phase or split),
        ),
    ]:
        mutant = lib.replace(marker, replacement, 1)
        bad = bindings["check_stages"](mutant, require_dependencies=False)
        bad_graphs.append(
            claims(mutant, gpu, bridge, sha2, shake, bad, roles, unsafe_case=affected)
        )
    return "\n".join([positive, *bad_graphs])
