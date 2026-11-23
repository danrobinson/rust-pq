"""Translate the pinned RustCrypto caller dataflow into Lean.

Only the method calls, immutable bindings and constructors used by these
upstream methods are accepted. The typed hash-suite context carries its seed.
"""

import argparse
import re
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
UPSTREAM = runpy.run_path(str(HERE / "extract-peer-sha2-suite.py"))
CARGO = runpy.run_path(str(HERE / "check-peer-digest.py"))
body, compact, require = (UPSTREAM[n] for n in ("body", "compact", "require"))


def upstream(tar, pkg, path, name):
    source = UPSTREAM["extract_body"](tar, pkg, path + ".rs")
    return compact(body(source, rf"\bfn {name}\b"))


def atom(s):
    s = s.removeprefix("&")
    fields = {
        "self.sk_seed": "k.seed",
        "self.sk_prf": "k.prf",
        "self.verifying_key.pk_seed": "k.publicSeed",
        "self.verifying_key.pk_root": "k.root",
        "self.pk_seed": "k.seed",
        "self.pk_root": "k.root",
        "signature.randomizer": "signature.r",
        "signature.fors_sig": "signature.fors",
        "signature.ht_sig": "signature.tree",
    }
    if s in fields:
        return fields[s]
    if not re.fullmatch(r"[a-z_][a-z_0-9]*", s):
        raise ValueError(f"unexpected Rust argument {s}")
    return s


def expression(s):
    if s == "opt_rand.unwrap_or(&self.verifying_key.pk_seed.0).try_into().unwrap()":
        return "opt_rand.getD k.publicSeed"
    if s.endswith(".then_some(()).ok_or(Error::new())"):
        return expression(s.removesuffix(".then_some(()).ok_or(Error::new())"))
    m = re.fullmatch(r"([\w:.<>]+)\(([^()]*)\)", s)
    if m is None:
        return atom(s)
    fun = m[1]
    args = [atom(x) for x in m[2].split(",")]
    if fun == "P::new_from_pk_seed" and len(args) == 1:
        return args[0]
    if fun in ("P::prf_msg", "P::h_msg", "split_digest::<P>", "ForsTree::new"):
        name, n = {
            "P::prf_msg": ("c.prfMsg", 3),
            "P::h_msg": ("c.hMsg", 4),
            "split_digest::<P>": ("splitResult p", 1),
            "ForsTree::new": ("forsAddress", 2),
        }[fun]
        require(len(args) == n, fun)
        return " ".join((name, *args))
    receiver, method = fun.split(".")
    seed = atom(receiver)
    if method == "fors_sign" and len(args) == 3:
        md, sk, adrs = args
        return f"c.forsSign {md} {sk} {seed} {adrs}"
    if method == "fors_pk_from_sig" and len(args) == 3:
        sig, md, adrs = args
        return f"c.forsRecover {sig} {md} {seed} {adrs}"
    if method == "ht_sign" and len(args) == 4:
        msg, sk, tree, leaf = args
        return f"PeerCall.ht (c.xmss p) p {msg} {sk} {seed} {tree} {leaf}"
    if method == "ht_verify" and len(args) == 5:
        msg, sig, tree, leaf, root = args
        return f"htVerifyWith (c.xmss p) p {msg} {sig} {seed} {tree} {leaf} {root}"
    raise ValueError(fun)


def straight(src, sign):
    *bindings, tail = src.split(";")
    lines = []
    for st in bindings:
        m = re.fullmatch(r"let(\([\w,]+\)|\w+)=(.+)", st)
        require(m, st)
        name = m[1]
        if name.startswith("("):
            name = name.replace(",", ", ")
        lines.append(f"  let {name} := {expression(m[2])}")
    if sign:
        m = re.fullmatch(r"Signature\{(\w+),(\w+),(\w+),\}", tail)
        require(
            m and set(m.groups()) == {"randomizer", "fors_sig", "ht_sig"},
            "signature constructor",
        )
        lines.append("  ⟨randomizer, fors_sig, ht_sig⟩")
    else:
        lines.append("  " + expression(tail))
    return lines


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("output", type=Path)
    args = p.parse_args()
    graph = CARGO["metadata"](CARGO["ROOT"] / "bench/Cargo.toml")
    (peer,) = [
        pkg
        for pkg in graph["packages"]
        if pkg["name"] == "slh-dsa" and pkg["version"] == "0.2.0-rc.5"
    ]
    with UPSTREAM["checked_archive"](
        peer, (CARGO["ROOT"] / "bench/Cargo.lock").read_text()
    ) as tar:

        def method(file, name):
            return upstream(tar, peer, file, name)

        def exact(file, name, expected):
            require(
                method(file, name) == compact(expected), f"unsupported {file}::{name}"
            )

        exact(
            "util",
            "split_digest",
            """
          #[allow(deprecated)] let m=Array::from_slice(&digest[..P::MD::USIZE]);
          let idx_tree_size=(P::H::USIZE-P::HPrime::USIZE).div_ceil(8);let idx_leaf_size=P::HPrime::USIZE.div_ceil(8);
          let mut idx_tree_bytes=[0u8;8];let mut idx_leaf_bytes=[0u8;4];
          idx_tree_bytes[8-idx_tree_size..].copy_from_slice(&digest[P::MD::USIZE..P::MD::USIZE+idx_tree_size]);
          idx_leaf_bytes[4-idx_leaf_size..].copy_from_slice(&digest[P::MD::USIZE+idx_tree_size..P::MD::USIZE+idx_tree_size+idx_leaf_size],);
          let mask:u64=1u64.checked_shl(P::H::U32-P::HPrime::U32).unwrap_or(0).wrapping_sub(1);
          let idx_tree=u64::from_be_bytes(idx_tree_bytes)&mask;
          let idx_leaf=u32::from_be_bytes(idx_leaf_bytes)&((1<<P::HPrime::USIZE)-1);(m,idx_tree,idx_leaf)
        """,
        )
        for family, prefix in (("sha2", "Sha2_"), ("shake", "Shake")):
            source = UPSTREAM["extract_body"](tar, peer, "hashes/" + family + ".rs")
            names = ["128s", "128f", "192s", "192f", "256s", "256f"]
            for name, (n, h, d, hp, a, k) in zip(
                names,
                [
                    (16, 63, 7, 9, 12, 14),
                    (16, 66, 22, 3, 6, 33),
                    (24, 63, 7, 9, 14, 17),
                    (24, 66, 22, 3, 8, 33),
                    (32, 64, 8, 8, 14, 22),
                    (32, 68, 17, 4, 9, 35),
                ],
            ):
                ty = prefix + name
                for trait, fields in [
                    ("XmssParams", f"type HPrime=U<{hp}>;"),
                    ("HypertreeParams", f"type D=U<{d}>;type H=U<{h}>;"),
                    (
                        "ForsParams",
                        f"type K=U<{k}>;type A=U<{a}>;type MD=U<{(k * a + 7) // 8}>;",
                    ),
                ]:
                    actual = compact(body(source, rf"impl {trait} for {ty}\b"))
                    for x, y in [(a, k), (k, a)]:
                        actual = actual.replace(
                            f"U<{{({x}*{y}usize).div_ceil(8)}}>",
                            f"U<{(a * k + 7) // 8}>",
                        )
                    require(
                        actual == compact(fields),
                        f"unexpected defaults or dimensions: {ty}::{trait}",
                    )

        def scoped(file, impl, name, expected):
            source = UPSTREAM["extract_body"](tar, peer, file + ".rs")
            actual = compact(body(body(source, impl), rf"\bfn {name}\b"))
            require(actual == compact(expected), f"unsupported {file}::{impl}::{name}")

        for file, ty in [
            ("signing_key", "SkSeed"),
            ("signing_key", "SkPrf"),
            ("verifying_key", "PkSeed"),
        ]:
            scoped(
                file,
                rf"impl<N: ArraySize> From<&\[u8\]> for {ty}<N>",
                "from",
                "#[allow(deprecated)] Self(Array::clone_from_slice(slice))",
            )
            scoped(
                file,
                rf"impl<N: ArraySize> {ty}<N>",
                "new",
                "let mut bytes=Array::<u8,N>::default();rng.fill_bytes(bytes.as_mut_slice());Self(bytes)",
            )
        scoped(
            "signing_key",
            r"impl<P: ParameterSet> SigningKey<P>",
            "new",
            "let sk_seed=SkSeed::new(rng);let sk_prf=SkPrf::new(rng);let pk_seed=PkSeed::new(rng);Self::from_seed(sk_seed,sk_prf,pk_seed)",
        )
        scoped(
            "address",
            r"impl ForsTree(?=\s*\{)",
            "new",
            """
            ForsTree{layer_adrs:0.into(),tree_adrs_low:tree_adrs_low.into(),tree_adrs_high:0.into(),
            type_const:ForsTree::TYPE_CONST.into(),key_pair_adrs:key_pair_adrs.into(),tree_height:0.into(),tree_index:0.into(),}
        """,
        )
        scoped(
            "address",
            r"impl Default for WotsHash",
            "default",
            """
            WotsHash{layer_adrs:0.into(),tree_adrs_low:0.into(),tree_adrs_high:0.into(),type_const:0.into(),
            key_pair_adrs:0.into(),chain_adrs:0.into(),hash_adrs:0.into(),}
        """,
        )
        exact(
            "signing_key",
            "to_bytes",
            """
           let mut bytes=Array::<u8,P::SkLen>::default();bytes[..P::N::USIZE].copy_from_slice(&self.sk_seed.0);
           bytes[P::N::USIZE..2*P::N::USIZE].copy_from_slice(&self.sk_prf.0);
           bytes[2*P::N::USIZE..].copy_from_slice(&self.verifying_key.to_bytes());bytes
        """,
        )
        exact(
            "verifying_key",
            "to_bytes",
            """
           let mut bytes=Array::<u8,P::VkLen>::default();debug_assert!(P::N::USIZE*2==P::VkLen::USIZE);
           bytes[..P::N::USIZE].copy_from_slice(&self.pk_seed.0);bytes[P::N::USIZE..].copy_from_slice(&self.pk_root);bytes
        """,
        )
        exact(
            "signature_encoding",
            "to_bytes",
            """
           let mut bytes=Array::<u8,P::SigLen>::default();let r_size=P::N::USIZE;let fors_size=ForsSignature::<P>::SIZE;
           bytes[..r_size].copy_from_slice(&self.randomizer);self.fors_sig.write_to(&mut bytes[r_size..r_size+fors_size]);
           self.ht_sig.write_to(&mut bytes[r_size+fors_size..]);bytes
        """,
        )
        exact("address", "tree_adrs", """
            HashTree { layer_adrs:self.layer_adrs, tree_adrs_low:self.tree_adrs_low,
            tree_adrs_high:self.tree_adrs_high, type_const:HashTree::TYPE_CONST.into(),
            padding:0.into(), tree_height:0.into(), tree_index:0.into(), }
        """)
        exact("xmss", "xmss_node", """
            debug_assert!(height<=Self::HPrime::U32);
            debug_assert!(node<(1<<(Self::HPrime::U32-height)));
            if height==0 {let mut adrs=adrs.clone(); adrs.key_pair_adrs.set(node);
            self.wots_pk_gen(sk_seed,&adrs)} else {
            let lnode=self.xmss_node(sk_seed,2*node,height-1,adrs);
            let rnode=self.xmss_node(sk_seed,2*node+1,height-1,adrs);
            let mut adrs=adrs.tree_adrs(); adrs.tree_height.set(height);
            adrs.tree_index.set(node);self.h(&adrs,&lnode,&rnode)}
        """)
        exact("xmss", "xmss_sign", """
            let mut adrs=adrs.clone(); adrs.key_pair_adrs.set(idx);
            let sig=self.wots_sign(m,sk_seed,&adrs);
            let mut auth=Array::<Array<u8,Self::N>,Self::HPrime>::default();
            let mut idx=idx;for j in 0..Self::HPrime::U32{
            let node=self.xmss_node(sk_seed,idx^1,j,&adrs);idx>>=1;auth[j as usize]=node;}
            XmssSig{sig,auth}
        """)
        exact("xmss", "xmss_pk_from_sig", """
            let mut adrs=adrs.clone(); adrs.key_pair_adrs.set(idx);
            let mut node=self.wots_pk_from_sig(&sig.sig,m,&adrs);
            let mut adrs=adrs.tree_adrs();let mut idx=idx;let mut rem;
            for j in 0..Self::HPrime::U32{adrs.tree_height.set(j+1);
            (idx,rem)=(idx>>1,idx&1);adrs.tree_index.set(idx);
            if rem==0{node=self.h(&adrs,&node,&sig.auth[j as usize]);}
            else{node=self.h(&adrs,&sig.auth[j as usize],&node);}}
            node
        """)
        exact(
            "hypertree",
            "ht_sign",
            """
          let mut adrs=WotsHash::default(); adrs.tree_adrs_low.set(idx_tree); let mut sig=Array::<_,Self::D>::default();
          sig[0]=Some(self.xmss_sign(m,sk_seed,idx_leaf,&adrs));let mut root=self.xmss_pk_from_sig(idx_leaf,sig[0].as_ref().unwrap(),m,&adrs);
          for j in 1..Self::D::U32{
            idx_leaf=(idx_tree&((1<<Self::HPrime::U32)-1)).try_into().expect("H' is less than 32");idx_tree>>=Self::HPrime::U64;
            adrs.layer_adrs.set(j);adrs.tree_adrs_low.set(idx_tree);
            sig[j as usize]=Some(self.xmss_sign(&root,sk_seed,idx_leaf,&adrs));
            if j!=Self::D::U32-1{root=self.xmss_pk_from_sig(idx_leaf,sig[j as usize].as_ref().unwrap(),&root,&adrs,);}}
          HypertreeSig(sig.iter().cloned().map(Option::unwrap).collect())
        """,
        )
        exact(
            "hypertree",
            "ht_verify",
            """
          let mut adrs=WotsHash::default(); adrs.tree_adrs_low.set(idx_tree);
          let mut root=self.xmss_pk_from_sig(idx_leaf,&sig.0[0],m,&adrs);
          for j in 1..Self::D::U32{
            idx_leaf=(idx_tree&((1<<Self::HPrime::U32)-1)).try_into().expect("H' is less than 32");
            idx_tree>>=Self::HPrime::U64; adrs.layer_adrs.set(j); adrs.tree_adrs_low.set(idx_tree);
            root=self.xmss_pk_from_sig(idx_leaf,&sig.0[j as usize],&root,&adrs);}
          &root==pk_root
        """,
        )
        exact("signing_key", "try_sign", "self.try_multipart_sign(&[msg])")
        exact(
            "signing_key",
            "try_multipart_sign",
            "self.raw_try_sign_with_context(msg,&[],None)",
        )
        exact(
            "signing_key",
            "try_sign_with_rng",
            "self.try_multipart_sign_with_rng(rng,&[msg])",
        )
        exact(
            "signing_key",
            "try_multipart_sign_with_rng",
            """
          let mut randomizer=Array::<u8,P::N>::default();
          rng.try_fill_bytes(randomizer.as_mut_slice()).map_err(|_|signature::Error::new())?;
          self.raw_try_sign_with_context(msg,&[],Some(&randomizer))
        """,
        )
        exact("verifying_key", "verify", "self.multipart_verify(&[msg],signature)")
        exact(
            "verifying_key",
            "multipart_verify",
            "self.raw_try_verify_with_context(msg,&[],signature)",
        )
        sign = straight(method("signing_key", "raw_slh_sign_internal"), True)
        verify = straight(method("verifying_key", "raw_slh_verify_internal"), False)
        exact(
            "signing_key",
            "from_seed",
            """
          let mut adrs=WotsHash::default();adrs.layer_adrs.set(P::D::U32-1);let xmss=P::new_from_pk_seed(&pk_seed);
          let pk_root=xmss.xmss_node(&sk_seed,0,P::HPrime::U32,&adrs);let verifying_key=VerifyingKey{pk_seed,pk_root};
          SigningKey{sk_seed,sk_prf,verifying_key,}
        """,
        )
        exact(
            "signing_key",
            "slh_keygen_internal",
            "let sk_seed=SkSeed::from(sk_seed);let sk_prf=SkPrf::from(sk_prf);let pk_seed=PkSeed::from(pk_seed);Self::from_seed(sk_seed,sk_prf,pk_seed)",
        )
        exact(
            "signing_key",
            "slh_sign_internal",
            "self.raw_slh_sign_internal(&[msg],opt_rand)",
        )
        exact(
            "verifying_key",
            "slh_verify_internal",
            "self.raw_slh_verify_internal(&[msg],signature)",
        )
        for file, op, last in [
            ("signing_key", "sign", "opt_rand"),
            ("verifying_key", "verify", "signature"),
        ]:
            exact(
                file,
                f"try_{op}_with_context",
                f"self.raw_try_{op}_with_context(&[msg],ctx,{last})",
            )
            call = f"self.raw_slh_{op}_internal(&ctx_msg,{last})"
            exact(
                file,
                f"raw_try_{op}_with_context",
                f"""
                let ctx_len=u8::try_from(ctx.len()).map_err(|_|Error::new())?;let ctx_len_bytes=ctx_len.to_be_bytes();
                let ctx_msg=[&[&[0],&ctx_len_bytes,ctx],msg];{f"Ok({call})" if op == "sign" else call}
            """,
            )
    args.output.write_text(
        "\n".join(
            [
                "-- Generated from the locked peer by scripts/extract-peer-callers.py.",
                "import PeerEquality.CallerTypes",
                "",
                "namespace slhdsa.PeerCall",
                "open Spec",
                "",
                "def keygen (c : Children) (p : Params) (sk prf pk : Bytes) : Key :=",
                "  let root := (c.xmss p).node sk 0 p.hp pk (layer (p.d-1) 0)",
                "  ⟨sk,prf,pk,root⟩",
                "",
                "def rawSign (c : Children) (p : Params) (k : Key) (msg : Parts) (opt_rand : Option Bytes) : Signature :=",
                *sign,
                "",
                "def rawVerify (c : Children) (p : Params) (k : PublicKey) (msg : Parts) (signature : Signature) : Bool :=",
                *verify,
                "",
                "def signCtx (c : Children) (p : Params) (k : Key) (msg : List Bytes) (ctx : Bytes) (rand : Option Bytes) : Option Signature :=",
                "  if ctx.length ≤ 255 then some (rawSign c p k (contextParts ctx msg) rand) else none",
                "",
                "def verifyCtx (c : Children) (p : Params) (k : PublicKey) (msg : List Bytes) (ctx : Bytes) (s : Signature) : Bool :=",
                "  if ctx.length ≤ 255 then rawVerify c p k (contextParts ctx msg) s else false",
                "",
                "end slhdsa.PeerCall",
                "",
            ]
        )
    )


if __name__ == "__main__":
    main()
