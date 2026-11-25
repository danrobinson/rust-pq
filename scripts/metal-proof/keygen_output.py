"""Compose the keygen command trace with host root decoding and key packing."""
from pathlib import Path


def host(lib, compact, body):
    keygen = compact(body(lib, "fn keygen_internal_batch_family<"))
    if not keygen.startswith(compact("validate_geometry::<N>(p)?;let count=batch.len();if count==0{return Ok(Vec::new());}")):
        raise ValueError("changed keygen empty-batch or validation order")
    macro = body(lib,"macro_rules! metal_set")
    typed = "let (sk,pk)=gpu.$kg_int::<N>(&PARAMS,sk_seed,sk_prf,pk_seed)?;Ok((sk.try_into().unwrap(),pk.try_into().unwrap()))"
    if compact(body(macro,"pub fn keygen_internal(")) != compact(typed) or compact(body(macro,"pub fn keygen(")) != compact("gpu.$kg::<N>(&PARAMS,seeds,sk,pk)"):
        raise ValueError("changed keygen typed public API")
    tail = "let mut out = Vec::with_capacity(count); match family {"
    for family, width, size, item, stem in (
        ("Sha2","nw",4,"words","u32"),("Shake","nl",8,"lanes","u64"),
    ):
        tail += f"""HashFamily::{family} => {{
            let {width} = N/{size}; let roots_{item}=pool.xmss_roots.as_ref().unwrap().as_slice_of::<{stem}>(count*{width});
            for(i,(sk_seed,sk_prf,pk_seed)) in batch.iter().enumerate(){{
              let pk_root={item}_to_bytes::<N>(&roots_{item}[i*{width}..(i+1)*{width}]);
              out.push(pack_keypair(sk_seed,sk_prf,pk_seed,&pk_root)); }} }} """
        decode = f"""let mut out=[0u8;N]; for i in 0..(N/{size}){{
           out[{size}*i..{size}*i+{size}].copy_from_slice(&{item}[i].to_{'le' if size==8 else 'be'}_bytes()); }} out"""
        if compact(body(lib, f"fn {item}_to_bytes<")) != compact(decode):
            raise ValueError("changed keygen root endianness")
    tail += "} Ok(out)"
    if not keygen.endswith(compact("cmd.commit_and_wait()?;"+tail)):
        raise ValueError("changed keygen root readback")
    wrapper = """assert_eq!(seeds.len(),3*N); assert_eq!(sk.len(),4*N); assert_eq!(pk.len(),2*N);
        let sk_seed=block::<N>(seeds,0);let sk_prf=block::<N>(seeds,1);let pk_seed=block::<N>(seeds,2);
        let mut res=self.keygen_internal_batch_family::<N>(family,p,&[(sk_seed,sk_prf,pk_seed)])?;
        let(sk_out,pk_out)=res.pop().unwrap();sk.copy_from_slice(&sk_out);pk.copy_from_slice(&pk_out);Ok(())"""
    if compact(body(lib,"fn keygen_family<")) != compact(wrapper):
        raise ValueError("changed keygen singleton seed or result copy")
    block = body((Path(__file__).resolve().parents[2]/"rust/src/util.rs").read_text(), "fn block<")
    if compact(block) != compact("let mut out=[0u8;N];out.copy_from_slice(&s[i*N..i*N+N]);out"):
        raise ValueError("changed keygen seed block indexing")
    for prefix, family in (("","Sha2"),("shake_","Shake")):
        single = f"let mut res=self.{prefix}keygen_internal_batch::<N>(p,&[(*sk_seed,*sk_prf,*pk_seed)])?;Ok(res.pop().unwrap())"
        for public, fragment in (
            ("keygen_internal", single),
            ("keygen_internal_batch", f"self.keygen_internal_batch_family::<N>(HashFamily::{family},p,batch)"),
            ("keygen", f"self.keygen_family::<N>(HashFamily::{family},p,seeds,sk,pk)"),
        ):
            if compact(body(lib,"pub fn "+prefix+public+"<")) != compact(fragment):
                raise ValueError("changed keygen family dispatch or singleton return")
    pack = """let mut sk=Vec::with_capacity(4*N); sk.extend_from_slice(sk_seed);sk.extend_from_slice(sk_prf);
        sk.extend_from_slice(pk_seed);sk.extend_from_slice(pk_root);let mut pk=Vec::with_capacity(2*N);
        pk.extend_from_slice(pk_seed);pk.extend_from_slice(pk_root);(sk,pk)"""
    if compact(body(lib,"fn pack_keypair<")) != compact(pack):
        raise ValueError("changed keygen public packing")


def claims(label, p, family, n, phase, entries):
    size = 8 if family=="shake" else 4
    words = n//size
    mode = ".twoPhase" if phase else ".streaming"
    leafValue = f"{family}BufferLeaf {p} e {words} mem" if phase else f"{family}StreamLeaf {p} e {words}"
    tip = f"MetalLeafDispatch.run (count*{p}.len) {words} {size} ({family}ChainTip {p} e) e" if phase else "pre.initial"
    order1 = f"(chainOrder : pre.schedule.Perm (MetalChainDispatch.grid ((batch.length*2^{p}.hp)*{p}.len) {words}))" if phase else ""
    leafExec = "next" if phase else "pre"
    proof = (f"""
    have tips := MetalLeafDispatch.matches_run (count*{p}.len) {words} {size} ({family}ChainTip {p} e)
      (MetalPipeline.metalWotsChainsKernel {p} e.keys e.trees) e (MetalChainDispatch.covers_grid chainOrder)
      (fun g _ => {family}ChainTip_spec {p} e g)
    intro gid hg
    rw [{family}BufferLeaf_spec {p} e {words} tip{" (by decide)" if family=="sha2" else ""}]
    exact MetalLeafDispatch.twoPhase_spec {p} hv e.keys e.trees count {words} {size} (by decide) tip tips gid hg
""" if phase else f"""
    intro gid _
    exact {family}StreamLeaf_spec {p} e hv {words} (by decide) gid
""")
    model_args = f"(batch : MetalKeygenDispatch.Batch) (pre {'next ' if phase else ''}buf : MetalChainDispatch.Execution) (start : MetalKeygenDispatch.State)"
    equation = f"batch.map (fun (sk,prf,pk) => Spec.slhKeygenInternal {p} sk prf pk)"
    model = f"""    let e := {{pre with keys := MetalKeygenDispatch.keys batch, trees := MetalKeygenDispatch.trees {p}}}
    let count := batch.length*2^{p}.hp
    let tip := {tip}
    let leaf := fun ({"mem" if phase else "_mem"} : MetalChainDispatch.Memory) => MetalLeafDispatch.run count {words} {size} ({leafValue}) {leafExec}
    let root := fun mem => MetalLeafDispatch.run batch.length {words} {size} ({family}XmssRoot {p} e.keys e.trees {words} mem) buf
    MetalKeygenDispatch.replay {label} tip leaf root (MetalKeygenDispatch.pack batch {str(family=="shake").lower()} {p}.n {words}) start"""
    main = f"""
private def {label} : List MetalCommand.Access := [{entries}]
private def {label}_model {model_args} :=
{model}
private theorem {label}_keygen_execution {model_args}
    {order1}
    (leafOrder : {leafExec}.schedule.Perm (MetalChainDispatch.grid (batch.length*2^{p}.hp) {words}))
    (rootOrder : buf.schedule.Perm (MetalChainDispatch.grid batch.length {words})) :
{model} = {equation} := by
  intro e count tip leaf root
  have ops : {label}.filterMap MetalKeygenDispatch.op = [.host,{".tips," if phase else ""}.leaves,.roots,.read] := by decide
  rw [MetalKeygenDispatch.replay,ops]
  let mem := leaf {"tip" if phase else "start.tips"}
  have hv := MetalPipeline.metal_all_12_params_valid {p} (by decide)
  have leafOk : MetalLeafDispatch.Matches count {words} {size} mem (MetalPipeline.metalXmssLeaves {mode} {p} e.keys e.trees) := by
    apply MetalLeafDispatch.matches_run _ _ _ _ _ _ (MetalChainDispatch.covers_grid leafOrder)
{proof}
  apply MetalKeygenDispatch.pack_spec {p} hv batch _ {words} {size} (by decide) _ _ buf rootOrder
  intro s
  exact ({family}XmssRoot_spec {p} e.keys e.trees {words} mem s).trans
    (MetalKeygenDispatch.root_value {p} hv {mode} batch {words} {size} (by decide) mem leafOk s)
"""
    count = f"(batch.length*2^{p}.hp)"
    scheduled = f"(MetalSigningSchedule.execution {count} {words} initial)"
    if phase:
        scheduled = f"(MetalSigningSchedule.execution ({count}*{p}.len) {words} initial) "+scheduled
    scheduled += f" (MetalSigningSchedule.execution batch.length {words} initial)"
    return main+f"""
private def {label}_batch (batch : MetalKeygenDispatch.Batch) (initial : MetalChainDispatch.Memory) :=
  {label}_model batch {scheduled} ⟨initial,initial,initial,[]⟩

private theorem {label}_canonical_fips (batch : MetalKeygenDispatch.Batch) (initial : MetalChainDispatch.Memory) :
    {label}_batch batch initial = {equation} :=
  {label}_keygen_execution batch {scheduled} _ {"(List.Perm.refl _) " if phase else ""}(List.Perm.refl _) (List.Perm.refl _)

private theorem {label}_public_keygen (seeds : Spec.Bytes) (initial : MetalChainDispatch.Memory) :
    ({label}_batch [(Spec.block {p} seeds 0,Spec.block {p} seeds 1,Spec.block {p} seeds 2)] initial).head? =
      some (Spec.slhKeygenInternal {p} (Spec.block {p} seeds 0) (Spec.block {p} seeds 1) (Spec.block {p} seeds 2)) := by
  rw [{label}_canonical_fips]
  rfl
"""
