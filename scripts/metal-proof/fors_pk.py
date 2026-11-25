"""Project FORS public-key compression using the same native-word stream
grammar as the two-phase WOTS leaf consumer, with its own descriptor and ADRS."""


def project(msl, shake, body, compact, leaf_body):
    prefix, words = ("shake_", "NL") if shake else ("", "NW")
    # Both shaders instantiate the same compression stream code. Translate
    # the independent FORS seed selector, domain, tree geometry and output.
    leaf = compact(leaf_body(shake, False)).split("uint32_ttip_base=", 1)[1]
    header = """if(sig_idx>=p.num_sigs)return;constdeviceForsJobDesc&job=jobs[sig_idx];
               constdeviceKEY&km=keys[job.key_idx];uint32_troot_base=""".replace("KEY", ("Shake" if shake else "")+"KeyMaterial")
    template = compact(header) + leaf
    for old, new in [
        ("gid*p.wots_len", "sig_idx*p.k"), ("p.wots_len", "p.k"),
        ("keys[desc.key_idx].", "km."), ("desc.layer,desc.tree,ADRS_WOTS_PK,leaf_idx", "0u,job.idx_tree,ADRS_FORS_ROOTS,job.idx_leaf"),
        ("gid*", "sig_idx*"), ("tip_base", "root_base"), ("chain_tips", "fors_roots"),
        ("out_leaves", "out_pk_fors"), ("leaf[", "pk["), ("(leaf)", "(pk)"),
    ]:
        template = template.replace(old, new)
    if not shake:
        template = template.replace("for(uinti=0;i<NW/2;++i)", "for(uintj=0;j<NW/2;++j)").replace("off+2*i", "off+2*j")
        template = template.replace("for(uint32_tc=0;c<p.k;++c)", "for(uint32_ti=0;i<p.k;++i)").replace("root_base+c*", "root_base+i*")
    if template != compact(body(msl, f"void {prefix}fors_pk_impl(")):
        raise ValueError(f"unmodeled {prefix}fors_pk stream, descriptor or publication")
    name = ("shake" if shake else "sha2") + "ForsValue"
    args = "(p : Spec.Params) (keys : MetalChainDispatch.Keys) (jobs : Nat → MetalForsPkDispatch.Job) (roots : MetalChainDispatch.Memory) (words : Nat)"
    packs = "(if words = 4 then 1 else words / 2) (if words = 4 then 4 else 2)"
    model = f"packed p.k words {packs}" if not shake else "flat p.k words"
    geom = "" if shake else "(geom : (if words = 4 then 1 else words/2)*(if words = 4 then 4 else 2) = words)"
    theorem = "flat_eq _ _ _ _" if shake else "packed_eq _ _ _ _ _ _ geom"
    return f"""
private def {name} {args} (sig : Nat) :=
  MetalForsPkDispatch.hash p keys jobs sig (MetalForsPkDispatch.{model} roots sig)
private theorem {name}_spec {args} {geom} (sig : Nat) :
    {name} p keys jobs roots words sig =
      MetalForsPkDispatch.hash p keys jobs sig (MetalForsPkDispatch.payload p.k words roots sig) :=
  congrArg (MetalForsPkDispatch.hash p keys jobs sig) (MetalForsPkDispatch.{theorem})
"""
