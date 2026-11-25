"""Check Metal host resource lifetimes and feed the extracted encoder traces to Lean."""

from collections import Counter
import re


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
    return "\n".join(statements)


def verify(lib, gpu, bridge, sha2, shake, bindings):
    args = [lib, gpu, bridge, sha2, shake]
    traces = bindings["check_stages"](lib)
    roles = bindings["SHADER_ROLES"]
    positive = claims(*args, traces, roles)
    # A missing wait, premature result view or omitted host producer must fail
    # against the actual source, independent of the positive trace assertions.
    cases = [
        (2, "[obj.cmdBuf waitUntilCompleted];", "", "cleanup path"),
        (2, "[obj.cmdBuf commit];", "return -1; [obj.cmdBuf commit];", "cleanup path"),
        (
            1,
            "let _ = slh_metal_cmd_commit_and_wait",
            "let _ = skip_wait",
            "cleanup path",
        ),
        (0, "sig_slice[off..off + N].copy_from_slice(r);", "", "host access"),
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
