"""Lift both cached signers' concrete scheduling and assembly to the byte-token model."""

import re
from textwrap import dedent

from build import function


def item(source, name, indent):
    pattern = rf"^{' ' * indent}(?:pub\(super\) )?fn {name}(?:<|\()"
    matches = list(re.finditer(pattern, source, re.MULTILINE))
    if len(matches) != 1:
        raise ValueError(f"expected one {name} at depth {indent}")
    start = matches[0].start()
    end = source.index("\n" + " " * indent + "}", start) + indent + 2
    return dedent(source[start:end])


def compact(source):
    return re.sub(r"//[^\n]*|\s+", "", source)


def scheduler(source):
    text = compact(source)
    claim = ("letactive_workers=workers.min(jobs.len().max(1));"
             "letnext=AtomicUsize::new(0);letfill=||loop{"
             "letid=next.fetch_add(1,Ordering::Relaxed);"
             "letSome(job)=jobs.get(id)else{break};match*job{")
    join = "crate::pool::execute(active_workers,true,&fill);"
    if text.count(claim) != 1 or text.count(join) != 1:
        raise ValueError("cached worker ticket or join changed")
    before, work = text.split(claim)
    work, after = work.split(join)
    # OnceLock writes are the only slot accesses before the pool joins.
    if (".get(" in work or re.search(r"\b(id|jobs|next|workers)\b", source.split("match *job {")[1].split("crate::pool::execute")[0])
            or ".set(" in before + after or ".fetch_add(" in before + work + after):
        raise ValueError("cached work depends on ticket order or slot publication")


def generate(cache, family):
    sha2, shake = cache.split("\nmod shake_ops {")
    source = sha2.split("\nmod sha2_ops {")[1] if family == "sha2" else shake
    sign = item(source, "sign_parallel", 4)
    scheduler(sign)
    seed = "&seed" if family == "sha2" else "pk_seed"
    dispatch = (f'#[cfg(all(feature="parallel",not(target_os="none")))]'
                f'ifletSome(sig)=sign_parallel(p,md,sk_seed,{seed},fors_adrs,r,'
                'idx_tree,idx_leaf,top_tree,layer_d2_hit,){returnsig;}')
    if compact(item(source, "sign_from_digest", 4)).count(dispatch) != 1:
        raise ValueError("cached sign_from_digest no longer dispatches these arguments")
    sign = sign.replace("fn sign_parallel", "pub(super) fn sign_parallel", 1)
    sign = sign.replace("md: &[u8]", "md: &[Token]").replace("mut tree: u64", "mut tree: Word")
    sign = sign.replace("mut leaf: u32", "mut leaf: Word")
    sign = sign.replace("(tree & ((1u64 << p.hp) - 1)) as u32", "(tree & ((1u64 << p.hp) - 1)).low32()")
    sign = sign.replace("node_idx: u32", "node_idx: Word").replace("idx: u32", "idx: Word")
    # job count + at most one final ticket per worker must fit even on a 32-bit target.
    sign = sign.replace("let next = AtomicUsize::new(0);",
                        "assert!(2u64 * jobs.len().max(1) as u64 <= u32::MAX as u64);\nlet next = AtomicUsize::new(0);")
    if family == "shake":
        # Replay both sides of the actual architecture condition on any host.
        condition = (r'any\(\s*all\(target_arch = "aarch64", target_endian = "little"\),'
                     r'\s*all\(target_arch = "x86_64", target_feature = "sse2"\)\s*\)')
        sign, hits = re.subn(condition, "proof_simd", sign)
        if hits != 4:
            raise ValueError("cached SHAKE architecture gates changed")
    defs = sign
    if family == "shake":
        defs += "\nmod simd { use super::*; use crate::shake256::parallel::WIDTH; pub(super) use crate::batch::available;\n"
        for name in ("fors_group_secrets", "fors_group_level"):
            defs += item(source, name, 8).replace("selections: &[u32]", "selections: &[Word]") + "\n"
        defs += "}"
    return defs.replace("[u8; N]", "[Token; N]").replace("Vec<u8>", "Vec<Token>")


def harness(template, cache):
    for name in ("sha2", "shake"):
        template = template.replace("// PRODUCTION_" + name.upper(), generate(cache, name))
    source = cache.split("\nmod shake_ops {")[1]
    scalar = item(source, "fors_sk_gen", 4) + "\n" + item(source, "fors_node_portable", 4).replace(
        "fn fors_node_portable", "pub(super) fn scalar_step", 1)
    grouped = item(source, "fors_secrets", 8) + "\n" + item(source, "fors_nodes", 8).replace(
        "fn fors_nodes", "pub(super) fn group_step", 1)
    steps = (scalar + "\n" + grouped).replace("[u8; N]", "[Token; N]").replace(
        "[u32; WIDTH]", "[Word; WIDTH]").replace("idx: u32", "idx: Word").replace("i: u32", "i: Word")
    template = template.replace("// PRODUCTION_STEPS", steps)
    packing = "\n".join(item(source, name, 8) for name in ("word", "header", "put", "read", "short", "pair"))
    packing = (packing.replace("u8", "Token").replace("u64", "LaneWord")
               .replace("0LaneWord", "LaneWord::zero()").replace("0Token", "Token::constant(0)")
               .replace("[0x1f; WIDTH]", "[LaneWord::domain(); WIDTH]"))
    template = template.replace("// PRODUCTION_PACKING", packing)
    layout = function(cache, "level_offset") + "\n" + function(cache, "append_auth_path")
    template = template.replace("// PRODUCTION_LAYOUT", layout.replace("[u8; N]", "[Token; N]").replace("Vec<u8>", "Vec<Token>"))
    return template.replace("// PRODUCTION_ROOT", function(cache, "tree_root").replace("[u8; N]", "[Token; N]"))
