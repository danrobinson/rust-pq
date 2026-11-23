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
            "split_digest::<P>": ("c.split", 1),
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
        return f"PeerCall.ht c.xmss p {msg} {sk} {seed} {tree} {leaf}"
    if method == "ht_verify" and len(args) == 5:
        msg, sig, tree, leaf, root = args
        return f"c.htVerify {msg} {sig} {seed} {tree} {leaf} {root}"
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
                "  let root := c.xmss.node sk 0 p.hp pk (layer (p.d-1) 0)",
                "  ⟨sk,prf,pk,root⟩",
                "",
                "def rawSign (c : Children) (p : Params) (k : Key) (msg : Parts) (opt_rand : Option Bytes) : Signature :=",
                *sign,
                "",
                "def rawVerify (c : Children) (k : PublicKey) (msg : Parts) (signature : Signature) : Bool :=",
                *verify,
                "",
                "def signCtx (c : Children) (p : Params) (k : Key) (msg : List Bytes) (ctx : Bytes) (rand : Option Bytes) : Option Signature :=",
                "  if ctx.length ≤ 255 then some (rawSign c p k (contextParts ctx msg) rand) else none",
                "",
                "def verifyCtx (c : Children) (k : PublicKey) (msg : List Bytes) (ctx : Bytes) (s : Signature) : Bool :=",
                "  if ctx.length ≤ 255 then rawVerify c k (contextParts ctx msg) s else false",
                "",
                "end slhdsa.PeerCall",
                "",
            ]
        )
    )


if __name__ == "__main__":
    main()
