"""Translate the pinned peer's SLH SHA-2 byte-stream operations to Lean.

The accepted language is deliberately restricted to the actual method bodies:
digest creation, cloning and update, slice truncation, and the two message
iterators. Reject unrecognized syntax and preserve the order of every update.
Read the checksummed crates.io archive rather than an editable registry tree.
"""

import argparse
import hashlib
import json
import re
import subprocess
import tarfile
from pathlib import Path


def require(ok, why):
    if not ok:
        raise ValueError(why)


def compact(s):
    return re.sub(r"\s+", "", re.sub(r"//[^\n]*", "", s))


def body(s, pattern):
    (match,) = re.finditer(pattern, s)
    start = s.index("{", match.end())
    depth = 1
    for j in range(start + 1, len(s)):
        depth += (s[j] == "{") - (s[j] == "}")
        if depth == 0:
            return s[start + 1 : j]
    raise ValueError("unclosed Rust body")


def checked_archive(package, lock):
    version = package["version"]
    name = package["name"]
    manifests = Path(package["manifest_path"])
    archive = (
        manifests.parents[3]
        / "cache"
        / manifests.parent.parent.name
        / f"{name}-{version}.crate"
    )
    (expected,) = [
        re.search(r'checksum = "([a-f0-9]+)"', entry)[1]
        for entry in lock.split("[[package]]")[1:]
        if entry.startswith(f'\nname = "{name}"\nversion = "{version}"\n')
        and package["source"] in entry
    ]
    require(
        hashlib.sha256(archive.read_bytes()).hexdigest() == expected,
        f"upstream checksum {name}",
    )
    return tarfile.open(archive)


def extract_body(archive, pkg, relative):
    return (
        archive.extractfile(f"{pkg['name']}-{pkg['version']}/src/{relative}")
        .read()
        .decode()
    )


def match(pattern, text):
    m = re.fullmatch(pattern, text)
    require(m, text[:160])
    return m


def translate(which, source):
    name = lambda n: which + n
    sources = {
        n: compact(body(source, rf"\bfn {n}\b"))
        for n in ("new_from_pk_seed", "prf_sk", "f", "h", "t", "h_msg", "prf_msg")
    }
    cache_text = sources["new_from_pk_seed"]
    cache_text = match(
        r"Self\{_n:core::marker::PhantomData,_m:core::marker::PhantomData,(.*)\}",
        cache_text,
    )[1]
    cache = {}
    fields = re.findall(
        r"(cached_hasher(?:_256|_512)?):Sha(256|512)::new_with_prefix\(pk_seed\.as_ref\(\)\)\.chain_update\(Array::<u8,Diff<U(64|128),N>>::default\(\)\),",
        cache_text,
    )
    expected = "".join(
        f"{field}:Sha{bits}::new_with_prefix(pk_seed.as_ref()).chain_update(Array::<u8,Diff<U{width},N>>::default()),"
        for field, bits, width in fields
    )
    require(fields and expected == cache_text, "cache initialization")
    result = []
    for field, bits, width in fields:
        cache[field] = bits
        result += [
            f"def {name(field)} (n : Nat) (seed : Bytes) : Bytes :=",
            f"  seed ++ List.replicate ({width} - n) 0#8",
            "",
        ]
    args = {
        "sk_seed": "secret",
        "adrs.compressed()": "compressed addr",
        "m": "m",
        "m1": "m1",
        "m2": "m2",
    }
    trunc = "Array::clone_from_slice(&hash[..Self::N::USIZE])"
    for op, params in [("prf_sk", "secret"), ("f", "m"), ("h", "m1 m2"), ("t", "")]:
        s = sources[op]
        if op == "t":
            m = match(
                r"letmuthasher=self\.(\w+)\.clone\(\)\.chain_update\(adrs\.compressed\(\)\);m\.iter\(\)\.for_each\(\|x\|hasher\.update\(x\.as_slice\(\)\)\);lethash=hasher\.finalize\(\);"
                + re.escape(trunc),
                s,
            )
            field = m[1]
            tape = f"absorb ({name(field)} n seed ++ compressed addr) rows"
            params = " (rows : List Bytes)"
        else:
            m = match(
                r"lethash=self\.(\w+)\.clone\(\)((?:\.chain_update\((?:adrs\.compressed\(\)|\w+)\))+?)\.finalize\(\);"
                + re.escape(trunc),
                s,
            )
            field = m[1]
            events = re.findall(r"\.chain_update\((adrs\.compressed\(\)|\w+)\)", m[2])
            tape = " ++ ".join([name(field) + " n seed", *[args[x] for x in events]])
            params = " (" + params + " : Bytes)"
        result += [
            f"def {name(op)} (n : Nat) (seed addr : Bytes){params} (algs : Algorithms := nativeAlgorithms) : Bytes :=",
            f"  (algs.sha{cache[field]} ({tape})).take n",
            "",
        ]
    flat = lambda var: (
        f"msg.iter().copied().flatten().for_each(|msg_part|{var}.update(msg_part.as_ref()));"
    )
    h = sources["h_msg"]
    m = match(
        r"letmuth=Sha(256|512)::new\(\);((?:h\.update\(\w+\);)+)"
        + re.escape(flat("h"))
        + r"letresult=Array\(h\.finalize\(\)\.into\(\)\);letseed=(\w+)\.clone\(\)\.concat\((\w+)\.0\.clone\(\)\)\.concat\(result\);mgf1::<Sha(256|512),Self::M>\(&seed\)",
        h,
    )
    names = {"rand": "r", "pk_seed": "seed", "pk_root": "root"}
    prefix = " ++ ".join(names[x] for x in re.findall(r"h\.update\((\w+)\);", m[2]))
    result += [
        f"def {name('hmsg')} (len : Nat) (r seed root : Bytes) (msg : List (List Bytes)) (algs : Algorithms := nativeAlgorithms) : Bytes :=",
        f"  let inner := algs.sha{m[1]} (absorb ({prefix}) msg.flatten)",
        f"  mgf algs.sha{m[5]} {int(m[5]) // 8} ({names[m[3]]} ++ {names[m[4]]} ++ inner) len",
        "",
    ]
    hm = match(
        r"letmutmac=Hmac::<Sha(256|512)>::new_from_slice\(sk_prf\.as_ref\(\)\)\.unwrap\(\);mac\.update\(opt_rand\.as_slice\(\)\);"
        + re.escape(flat("mac"))
        + r"letresult=mac\.finalize\(\)\.into_bytes\(\);Array::clone_from_slice\(&result\[\.\.Self::N::USIZE\]\)",
        sources["prf_msg"],
    )
    result += [
        f"def {name('prfmsg')} (n : Nat) (key rand : Bytes) (msg : List (List Bytes)) (algs : Algorithms := nativeAlgorithms) : Bytes :=",
        f"  (mac algs.sha{hm[1]} {64 if hm[1] == '256' else 128} key (absorb rand msg.flatten)).take n",
        "",
    ]
    return result


def verify_adapters(packages, lock, suite):
    """Recognize the library routines interpreted by Streams and Digest."""

    def src(name, path):
        version = {
            "sha2": "0.11.1",
            "hmac": "0.13.0",
            "block-buffer": "0.12.1",
            "digest": "0.11.3",
        }[name]
        (package,) = [
            p for p in packages if p["name"] == name and p["version"] == version
        ]
        with checked_archive(package, lock) as tar:
            return extract_body(tar, package, path)

    def method(source, name, expected):
        actual = compact(body(source, rf"\bfn {name}\b"))
        require(actual == compact(expected), f"adapter changed: {name}")

    method(
        suite,
        "mgf1",
        """
        let mut result = Array::<u8, L>::default();
        result.chunks_mut(<H as Digest>::output_size()).enumerate().for_each(|(counter,chunk)| {
            let counter: u32 = counter.try_into().expect("L should be less than (2^32 * Digest::output_size) bytes");
            let mut hasher=H::new(); hasher.update(seed); hasher.update(counter.to_be_bytes());
            let result=hasher.finalize(); chunk.copy_from_slice(&result[..chunk.len()]);
        }); result
    """,
    )
    digest = body(src("digest", "digest.rs"), r"\bDigest for D\b")
    for name, expected in {
        "new": "Self::default()",
        "new_with_prefix": "let mut h=Self::default();h.update(data.as_ref());h",
        "update": "Update::update(self,data.as_ref());",
        "chain_update": "Update::update(&mut self,data.as_ref());self",
        "finalize": "FixedOutput::finalize_fixed(self)",
    }.items():
        method(digest, name, expected)
    mac = body(src("digest", "mac.rs"), r"Mac for T\b")
    method(mac, "update", "Update::update(self,data);")
    method(mac, "finalize", "CtOutput::new(self.finalize_fixed())")
    ct = body(src("digest", "mac.rs"), r"impl<T: OutputSizeUser> CtOutput<T>")
    method(ct, "new", "Self{bytes}")
    method(ct, "into_bytes", "self.bytes.clone()")
    fixed = src("digest", "buffer_macros/fixed.rs")
    for name, expected in {
        "update": "let Self{core,buffer}=self;buffer.digest_blocks(data,|blocks|{$crate::block_api::UpdateCore::update_blocks(core,blocks)});",
        "finalize_into": "let Self{core,buffer}=&mut self;$crate::block_api::FixedOutputCore::finalize_fixed_core(core,buffer,out);",
        "clone": "Self{core:Clone::clone(&self.core),buffer:Clone::clone(&self.buffer),}",
        "default": "Self{core:Default::default(),buffer:Default::default(),}",
        "new_from_slice": "<$core_ty as $crate::KeyInit>::new_from_slice(key).map(|core|Self{core,buffer:Default::default()})",
    }.items():
        method(fixed, name, expected)
    wrapper = src("digest", "block_api/ct_variable.rs")
    method(wrapper, "clone", "Self{inner:self.inner.clone(),_out:PhantomData,}")
    method(
        wrapper,
        "default",
        "Self{inner:T::new(OutSize::USIZE).unwrap(),_out:PhantomData,}",
    )
    method(wrapper, "update_blocks", "self.inner.update_blocks(blocks);")
    method(
        wrapper,
        "finalize_fixed_core",
        """
        let mut full_res=Default::default(); self.inner.finalize_variable_core(buffer,&mut full_res);
        let n=out.len();let m=full_res.len()-n;match T::TRUNC_SIDE{
        TruncSide::Left=>out.copy_from_slice(&full_res[..n]),TruncSide::Right=>out.copy_from_slice(&full_res[m..]),}
    """,
    )
    method(
        src("digest", "lib.rs"),
        "finalize_fixed",
        "let mut out=Default::default();self.finalize_into(&mut out);out",
    )
    utils = src("hmac", "utils.rs")
    require(
        "constIPAD:u8=0x36;" in compact(utils)
        and "constOPAD:u8=0x5C;" in compact(utils),
        "HMAC constants",
    )
    method(
        utils,
        "get_der_key",
        """
        let mut der_key = Block::<D>::default();
        if key.len() <= der_key.len() { der_key[..key.len()].copy_from_slice(key); }
        else { let hash = D::digest(key); if hash.len() <= der_key.len() {
            der_key[..hash.len()].copy_from_slice(&hash);
        } else { let n = der_key.len(); der_key.copy_from_slice(&hash[..n]); } }
        der_key
    """,
    )
    hmac = src("hmac", "block_api.rs").split("pub struct HmacResetCore")[0]
    require(
        "pubstructHmac<D:EagerHash>(block_api::HmacCore<D>);"
        in compact(src("hmac", "lib.rs")),
        "HMAC type",
    )
    method(
        hmac,
        "new_from_slice",
        """
        let mut buf=get_der_key::<D>(key);
        buf.iter_mut().for_each(|b: &mut u8| *b ^= IPAD);
        let mut digest=D::Core::default(); digest.update_blocks(slice::from_ref(&buf));
        buf.iter_mut().for_each(|b: &mut u8| *b ^= IPAD ^ OPAD);
        let mut opad_digest=D::Core::default(); opad_digest.update_blocks(slice::from_ref(&buf));
        Ok(Self{opad_digest,digest,})
    """,
    )
    method(hmac, "update_blocks", "self.digest.update_blocks(blocks);")
    method(
        hmac,
        "finalize_fixed_core",
        """
        let mut hash=Output::<D::Core>::default(); self.digest.finalize_fixed_core(buffer,&mut hash);
        buffer.reset(); let h=&mut self.opad_digest; buffer.digest_blocks(&hash,|b|h.update_blocks(b));
        h.finalize_fixed_core(buffer,out);
    """,
    )
    block = src("block-buffer", "lib.rs")
    eager = (
        src("block-buffer", "sealed.rs")
        .split("impl Sealed for super::Eager {")[1]
        .split("impl Sealed")[0]
    )
    method(
        eager,
        "get_pos",
        """
        let pos=unsafe{let buf_ptr=buf.as_ptr().cast::<u8>();let last_byte_ptr=buf_ptr.add(N::USIZE-1);
        ptr::read(last_byte_ptr)};pos as usize
    """,
    )
    method(
        eager,
        "set_pos",
        """
        debug_assert!(u8::try_from(val).is_ok());unsafe{let buf_ptr=buf.as_mut_ptr().cast::<u8>();
        let last_byte_ptr=buf_ptr.add(N::USIZE-1);ptr::write(last_byte_ptr,val as u8);}
    """,
    )
    method(
        block,
        "default",
        """
        let mut buffer=MaybeUninit::uninit();let mut pos=Default::default();
        K::set_pos(&mut buffer,&mut pos,0);Self{buffer,pos}
    """,
    )
    method(block, "clone", "unsafe{ptr::read(self)}")
    method(
        block,
        "set_pos_unchecked",
        "debug_assert!(K::invariant(pos,BS::USIZE));K::set_pos(&mut self.buffer,&mut self.pos,pos);",
    )
    method(
        block,
        "set_data_unchecked",
        """
        unsafe{self.set_pos_unchecked(buf.len());let dst_ptr:*mut u8=self.buffer.as_mut_ptr().cast();
        ptr::copy_nonoverlapping(buf.as_ptr(),dst_ptr,buf.len());}
    """,
    )
    method(
        block,
        "get_pos",
        """
        let pos=K::get_pos(&self.buffer,&self.pos);
        if !K::invariant(pos,BS::USIZE){debug_assert!(false);unsafe{core::hint::unreachable_unchecked();}}pos
    """,
    )
    method(block, "reset", "unsafe{self.set_pos_unchecked(0);}")
    guard = body(block, r"Drop for ResetGuard<'_, BS, K>")
    method(guard, "drop", "self.0.reset();")
    method(eager, "invariant", "pos < block_size")
    method(eager, "split_blocks", "Array::slice_as_chunks(data)")
    method(
        block,
        "digest_blocks",
        """
        let pos=self.get_pos();let rem=self.size()-pos;let n=input.len();
        if K::invariant(n,rem){unsafe{let buf_ptr=self.buffer.as_mut_ptr().cast::<u8>().add(pos);
            ptr::copy_nonoverlapping(input.as_ptr(),buf_ptr,input.len());self.set_pos_unchecked(pos+input.len());}return;}
        if pos!=0{let(left,right)=input.split_at(rem);input=right;let g=ResetGuard(self);let buf=&mut g.0.buffer;
            let block=unsafe{let buf_ptr=buf.as_mut_ptr().cast::<u8>().add(pos);
            ptr::copy_nonoverlapping(left.as_ptr(),buf_ptr,left.len());buf.assume_init_ref()};compress(slice::from_ref(block));}
        let(blocks,leftover)=K::split_blocks(input);if !blocks.is_empty(){compress(blocks);}
        unsafe{self.set_data_unchecked(leftover);}
    """,
    )
    for width in (64, 128):
        method(
            block,
            f"len{width}_padding_be",
            "self.digest_pad(0x80, &data_len.to_be_bytes(), compress);",
        )
    method(
        block,
        "digest_pad",
        """
        let pos=self.get_pos(); let size=self.size(); let pad_len=size-pos-1;
        let suffix_dst_pos=size.checked_sub(suffix.len()).expect("suffix must be smaller than buffer block size");
        let g=ResetGuard(self); let buf=unsafe { let p:*mut u8=g.0.buffer.as_mut_ptr().cast::<u8>().add(pos);
        ptr::write(p,delim);ptr::write_bytes(p.add(1),0,pad_len);g.0.buffer.assume_init_mut()};
        if pad_len<suffix.len(){compress(buf);buf.fill(0);}
        buf[suffix_dst_pos..].copy_from_slice(suffix);compress(buf);
    """,
    )
    block_api = src("sha2", "block_api.rs")
    constants = compact(src("sha2", "consts.rs"))
    initial = []
    for bits, width, variants, cast in [
        (256, 64, (224, 256), ""),
        (512, 128, (224, 256, 384, 512), "as u128"),
    ]:
        require(
            f"pubstructSha{bits}(CtOutWrapper<block_api::Sha{bits}VarCore,U{bits // 8}>);"
            in compact(src("sha2", "lib.rs")),
            "SHA fixed output wrapper",
        )
        sha = block_api.split(f"pub struct Sha{bits}VarCore", 1)[1].split(
            "/// Core block-level", 1
        )[0]
        require(
            f"typeBlockSize=U{width};" in compact(sha)
            and "typeBufferKind=Eager;" in compact(sha),
            "SHA buffer selection",
        )
        cases = "".join(f"{v // 8}=>consts::H{bits}_{v}," for v in variants)
        method(
            sha,
            "new",
            "let state=match output_size{"
            + cases
            + "_=>return Err(InvalidOutputSize),};let block_len=0;Ok(Self{state,block_len})",
        )
        method(
            sha,
            "update_blocks",
            f"self.block_len+=blocks.len() as u{width};let blocks=Array::cast_slice_to_core(blocks);compress{bits}(&mut self.state,blocks);",
        )
        method(
            sha,
            "finalize_variable_core",
            f"""
            let bs=Self::BlockSize::U64 {cast}; let bit_len=8*(buffer.get_pos() as u{width}+bs*self.block_len);
            buffer.len{width}_padding_be(bit_len,|b|compress{bits}(&mut self.state,&[b.0]));
            let (chunks,tail)=out.as_chunks_mut();assert!(tail.is_empty());
            for(chunk,val)in chunks.iter_mut().zip(self.state.iter()){{*chunk=val.to_be_bytes();}}
        """,
        )
        (values,) = re.findall(
            rf"constH{bits}_{bits}:State{bits}=\[((?:0x[0-9a-f]+,){{8}})\];", constants
        )
        initial.extend(
            [
                f"def initial{bits} : List SHA{bits}.Word := ["
                + values.rstrip(",")
                + "]",
                f"theorem initial{bits}_eq : initial{bits} = SHA{bits}.H0 := rfl",
                "",
            ]
        )
    return initial


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("output", type=Path)
    p.add_argument("initial", type=Path)
    args = p.parse_args()
    data = json.loads(
        subprocess.check_output(
            [
                "cargo",
                "metadata",
                "--locked",
                "--manifest-path",
                "bench/Cargo.toml",
                "--format-version",
                "1",
            ]
        )
    )
    lock = Path("bench/Cargo.lock").read_text()
    (peer,) = [
        p
        for p in data["packages"]
        if p["name"] == "slh-dsa" and p["version"] == "0.2.0-rc.5"
    ]
    with checked_archive(peer, lock) as tar:
        source = extract_body(tar, peer, "hashes/sha2.rs")
        address = extract_body(tar, peer, "address.rs")
    initial = verify_adapters(data["packages"], lock, source)
    args.initial.write_text(
        "\n".join(
            [
                "-- Generated from locked RustCrypto SHA-2 initialization constants.",
                "import Spec.Sha512",
                "import Spec.Sha256",
                "",
                "namespace slhdsa.RcSlhSha2",
                "open Spec",
                "",
                *initial,
                "end slhdsa.RcSlhSha2",
                "",
            ]
        )
    )
    lines = [
        "-- Generated from the checksummed slh-dsa crate by scripts/extract-peer-sha2-suite.py.",
        "import RcSlhSha2.Streams",
        "",
        "namespace slhdsa.RcSlhSha2",
        "open Spec",
        "",
    ]
    types = (
        "WotsHash",
        "WotsPk",
        "HashTree",
        "ForsTree",
        "ForsRoots",
        "WotsPrf",
        "ForsPrf",
    )
    require(
        set(re.findall(r"impl Address for (\w+)", address)) == set(types),
        "address implementations",
    )
    for tag, name in enumerate(types):
        impl = body(address, rf"impl Address for {name}\b")
        require(
            compact(impl) == f"constTYPE_CONST:u32={tag};",
            f"compressed override in {name}",
        )
        view = body(address, rf"impl AsRef<\[u8\]> for {name}\b")
        require(
            compact(body(view, r"fn as_ref\b")) == "self.as_bytes()",
            f"byte view in {name}",
        )
    a = compact(body(address, r"\bfn compressed\b"))
    a = match(
        r"letbytes=self\.as_ref\(\);letmutcompressed=Array::<u8,U22>::default\(\);(.*)compressed",
        a,
    )[1]
    bits = []
    next_dest = 0
    for st in a.strip(";").split(";"):
        if m := re.fullmatch(r"compressed\[(\d+)\]=bytes\[(\d+)\]", st):
            require(int(m[1]) == next_dest, "address byte placement")
            next_dest += 1
            bits.append(f"[addr[{m[2]}]!]")
        else:
            m = match(
                r"compressed\[(\d+)\.\.(\d+)\]\.copy_from_slice\(&bytes\[(\d+)\.\.(\d+)\]\)",
                st,
            )
            dest, end, src, stop = map(int, m.groups())
            require(dest == next_dest and end - dest == stop - src, "address range")
            bits.append(f"(addr.drop {src}).take {stop - src}")
            next_dest = end
    require(next_dest == 22, "compressed address size")
    lines += ["def compressed (addr : Bytes) : Bytes :=", "  " + " ++ ".join(bits), ""]
    for level in ["L1", "L35"]:
        impl = body(source, rf"HashSuite for Sha2{level}<N, M>")
        require("typeN=N;typeM=M;" in compact(impl), "hash trait sizes")
        lines.extend(translate(level.lower() + "_", impl))
    for suffix, level, n, m in re.findall(
        r"pub type Sha2_(\d+[sf]) = Sha2(L1|L35)<U(\d+), U(\d+)>;", source
    ):
        lines += [
            f"def suite{suffix} : Bool × Nat × Nat := ({str(level == 'L1').lower()}, {n}, {m})"
        ]
    args.output.write_text("\n".join([*lines, "", "end slhdsa.RcSlhSha2", ""]))


if __name__ == "__main__":
    main()
