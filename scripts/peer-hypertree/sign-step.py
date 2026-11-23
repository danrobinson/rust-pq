"""Expose the first layer and a single arbitrary later iteration unchanged."""

import re


def expose(source):
    start = source.index("    fn ht_sign(")
    end = source.index("    fn ht_verify(", start)
    method = source[start:end]
    start_body = method.index("let mut adrs = WotsHash::default();")
    loop = "for j in 1..Self::D::U32 {"
    head, rest = method[start_body:].split(loop)
    match = re.fullmatch(
        r"(.*?)\n        \}\n\s*//[^\n]*\n\s*HypertreeSig\(sig.iter\(\).cloned\(\).map\(Option::unwrap\).collect\(\)\)\s*\}\s*",
        rest,
        re.S,
    )
    if not match:
        raise ValueError("unrecognized end of ht_sign")
    children = (
        """#[cfg(kani)]
    fn proof_first(&self,m:&Array<u8,Self::N>,sk_seed:&SkSeed<Self::N>,idx_tree:u64,idx_leaf:u32)
      -> (Array<Option<XmssSig<Self>>,Self::D>,Array<u8,Self::N>) {
    """
        + head
        + """
      (sig,root)
    }
    #[cfg(kani)]
    fn proof_later(&self, mut root:Array<u8,Self::N>,sk_seed:&SkSeed<Self::N>,
       mut idx_tree:u64,j:u32,mut adrs:WotsHash, sig:&mut Array<Option<XmssSig<Self>>,Self::D>)
       -> (Array<u8,Self::N>,u64,u32) {
       let idx_leaf: u32;
    """
        + match[1]
        + """
       (root,idx_tree,idx_leaf)
    }
    """
    )
    return source[:end] + children + source[end:]
