//! NIST ACVP known-answer tests for all six SHA-2 parameter sets, reference
//! checks for the hash functions, and a cross-test against the original
//! single-parameter-set crate.

use serde_json::Value;
use slhdsa::params::{Params, SHA2_128F, SHA2_128S, SHA2_192F, SHA2_192S, SHA2_256F, SHA2_256S};
use slhdsa::slh;

const SETS: [(&str, &Params); 6] = [
    ("128s", &SHA2_128S),
    ("128f", &SHA2_128F),
    ("192s", &SHA2_192S),
    ("192f", &SHA2_192F),
    ("256s", &SHA2_256S),
    ("256f", &SHA2_256F),
];

fn vectors(set: &str) -> Value {
    let path = format!("{}/../vectors/slh-dsa-sha2-{}.json", env!("CARGO_MANIFEST_DIR"), set);
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn h(v: &Value) -> Vec<u8> {
    hex::decode(v.as_str().unwrap()).unwrap()
}

#[test]
fn table_2_sizes() {
    let expect = [(32, 7856), (32, 17088), (48, 16224), (48, 35664), (64, 29792), (64, 49856)];
    for ((name, p), (pk, sig)) in SETS.iter().zip(expect) {
        assert_eq!(2 * p.n, pk, "{name}");
        assert_eq!(p.sig_bytes(), sig, "{name}");
        assert_eq!(p.h, p.d * p.hp, "{name}");
        assert_eq!(p.m, p.md_bytes() + p.tree_bytes() + p.leaf_bytes(), "{name}");
    }
}

#[test]
fn sha256_matches_reference() {
    use sha2::Digest;
    let data: Vec<u8> = (0..300u32).map(|i| (i * 7 + 3) as u8).collect();
    for len in 0..300 {
        let ours = slhdsa::sha256::sha256(&data[..len]);
        let theirs = sha2::Sha256::digest(&data[..len]);
        assert_eq!(&ours[..], &theirs[..], "len {len}");
    }
}

#[test]
fn sha512_matches_reference() {
    use sha2::Digest;
    let data: Vec<u8> = (0..600u32).map(|i| (i * 7 + 3) as u8).collect();
    for len in 0..600 {
        let ours = slhdsa::sha512::sha512(&data[..len]);
        let theirs = sha2::Sha512::digest(&data[..len]);
        assert_eq!(&ours[..], &theirs[..], "len {len}");
    }
}

#[test]
fn hmac_matches_reference() {
    use hmac::Mac;
    let data: Vec<u8> = (0..300u32).map(|i| (i * 13 + 1) as u8).collect();
    for klen in [16, 24, 32] {
        for len in [0, 1, 55, 56, 64, 111, 112, 128, 199, 299] {
            let ours = slhdsa::sha256::hmac_sha256(&data[..klen], &data[..len]);
            let mut mac = hmac::Hmac::<sha2::Sha256>::new_from_slice(&data[..klen]).unwrap();
            mac.update(&data[..len]);
            assert_eq!(&ours[..], &mac.finalize().into_bytes()[..]);
            let ours = slhdsa::sha512::hmac_sha512(&data[..klen], &data[..len]);
            let mut mac = hmac::Hmac::<sha2::Sha512>::new_from_slice(&data[..klen]).unwrap();
            mac.update(&data[..len]);
            assert_eq!(&ours[..], &mac.finalize().into_bytes()[..]);
        }
    }
}

fn acvp_keygen(set: &str, p: &Params) {
    let v = vectors(set);
    let mut n = 0;
    for g in v["keyGen"].as_array().unwrap() {
        for t in g["tests"].as_array().unwrap() {
            let (sk, pk) = slh::slh_keygen_internal(p, &h(&t["skSeed"]), &h(&t["skPrf"]), &h(&t["pkSeed"]));
            assert_eq!(sk, h(&t["sk"]), "{set} tcId {}", t["tcId"]);
            assert_eq!(pk, h(&t["pk"]), "{set} tcId {}", t["tcId"]);
            n += 1;
        }
    }
    assert_eq!(n, 10);
}

fn acvp_siggen(set: &str, p: &Params) {
    let v = vectors(set);
    let mut n = 0;
    for g in v["sigGen"].as_array().unwrap() {
        let det = g["deterministic"].as_bool().unwrap();
        let internal = g["signatureInterface"] == "internal";
        for t in g["tests"].as_array().unwrap() {
            let sk = h(&t["sk"]);
            let rnd = if det { sk[2 * p.n..3 * p.n].to_vec() } else { h(&t["additionalRandomness"]) };
            let msg = h(&t["message"]);
            let sig = if internal {
                slh::slh_sign_internal(p, &msg, &sk, &rnd)
            } else {
                slh::slh_sign(p, &msg, &h(&t["context"]), &sk, &rnd).unwrap()
            };
            assert_eq!(sig.len(), p.sig_bytes());
            assert!(sig == h(&t["signature"]), "{set} tcId {}", t["tcId"]);
            n += 1;
        }
    }
    assert_eq!(n, 28);
}

fn acvp_sigver(set: &str, p: &Params) {
    let v = vectors(set);
    let (mut pass, mut fail) = (0, 0);
    for g in v["sigVer"].as_array().unwrap() {
        let internal = g["signatureInterface"] == "internal";
        for t in g["tests"].as_array().unwrap() {
            let pk = h(&t["pk"]);
            let msg = h(&t["message"]);
            let sig = h(&t["signature"]);
            let ok = if internal {
                slh::slh_verify_internal(p, &msg, &sig, &pk)
            } else {
                slh::slh_verify(p, &msg, &sig, &h(&t["context"]), &pk)
            };
            assert_eq!(ok, t["testPassed"].as_bool().unwrap(), "{set} tcId {} ({})", t["tcId"], t["reason"]);
            if ok { pass += 1 } else { fail += 1 }
        }
    }
    assert_eq!(pass + fail, 28);
    assert!(pass > 0 && fail > 0);
}

macro_rules! acvp {
    ($($name:ident, $idx:expr;)*) => {$(
        mod $name {
            #[test]
            fn keygen() { super::acvp_keygen(super::SETS[$idx].0, super::SETS[$idx].1) }
            #[test]
            fn siggen() { super::acvp_siggen(super::SETS[$idx].0, super::SETS[$idx].1) }
            #[test]
            fn sigver() { super::acvp_sigver(super::SETS[$idx].0, super::SETS[$idx].1) }
        }
    )*};
}
acvp! { acvp_128s, 0; acvp_128f, 1; acvp_192s, 2; acvp_192f, 3; acvp_256s, 4; acvp_256f, 5; }

/// The typed modules agree with the generic functions and reject tampering.
macro_rules! typed {
    ($($test:ident, $m:ident, $p:ident;)*) => {$(
        #[test]
        fn $test() {
            use slhdsa::$m as s;
            let (sk, pk) = s::slh_keygen_internal(&[1; s::N], &[2; s::N], &[3; s::N]);
            let (skv, pkv) = slh::slh_keygen_internal(&$p, &[1; s::N], &[2; s::N], &[3; s::N]);
            assert_eq!((sk.to_vec(), pk.to_vec()), (skv, pkv));
            let msg = b"hash-based signatures";
            let mut sig = s::slh_sign(msg, b"ctx", &sk, &[4; s::N]).unwrap();
            assert_eq!(sig.len(), $p.sig_bytes());
            assert!(sig == slh::slh_sign(&$p, msg, b"ctx", &sk, &[4; s::N]).unwrap());
            assert!(s::slh_sign(msg, &[0; 256], &sk, &[4; s::N]).is_none());
            assert!(s::slh_verify(msg, &sig, b"ctx", &pk));
            assert!(!s::slh_verify(msg, &sig, b"other", &pk));
            assert!(!s::slh_verify(b"hash-based signature", &sig, b"ctx", &pk));
            assert!(!s::slh_verify(msg, &sig, &[0; 256], &pk));
            let last = sig.len() - 1;
            for pos in [0, s::N, 3000, last] {
                sig[pos] ^= 1;
                assert!(!s::slh_verify(msg, &sig, b"ctx", &pk));
                sig[pos] ^= 1;
            }
            assert!(!s::slh_verify(msg, &sig[..last], b"ctx", &pk));
            let isig = s::slh_sign_internal(msg, &sk, &[5; s::N]);
            assert!(s::slh_verify_internal(msg, &isig, &pk));
            assert!(!s::slh_verify_internal(msg, &sig, &pk));
        }
    )*};
}
typed! {
    typed_128s, sha2_128s, SHA2_128S; typed_128f, sha2_128f, SHA2_128F;
    typed_192s, sha2_192s, SHA2_192S; typed_192f, sha2_192f, SHA2_192F;
    typed_256s, sha2_256s, SHA2_256S; typed_256f, sha2_256f, SHA2_256F;
}

/// A small deterministic generator for the cross-test inputs.
fn fill(seed: &mut u64, out: &mut [u8]) {
    for b in out.iter_mut() {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *b = (*seed >> 56) as u8;
    }
}

/// 128s behaviour is identical to the original single-parameter-set crate.
#[test]
fn cross_128s_against_original_crate() {
    use slhdsa::sha2_128s as new;
    let mut seed = 0x5eed_u64;
    for round in 0..6 {
        let (mut a, mut b, mut c, mut rnd) = ([0u8; 16], [0u8; 16], [0u8; 16], [0u8; 16]);
        fill(&mut seed, &mut a);
        fill(&mut seed, &mut b);
        fill(&mut seed, &mut c);
        fill(&mut seed, &mut rnd);
        let (sk, pk) = new::slh_keygen_internal(&a, &b, &c);
        assert_eq!((sk, pk), slhdsa_ref::slh_keygen_internal(&a, &b, &c));
        let mut msg = vec![0u8; [0, 1, 55, 64, 200, 1000][round]];
        fill(&mut seed, &mut msg);
        let mut ctx = vec![0u8; [0, 1, 17, 255, 256, 3][round]];
        fill(&mut seed, &mut ctx);
        let sig = new::slh_sign_internal(&msg, &sk, &rnd);
        assert!(sig == slhdsa_ref::slh_sign_internal(&msg, &sk, &rnd));
        let csig = new::slh_sign(&msg, &ctx, &sk, &rnd);
        assert!(csig == slhdsa_ref::slh_sign(&msg, &ctx, &sk, &rnd));
        // Verdicts agree on the genuine signature, corruptions and truncations.
        let mut cases: Vec<Vec<u8>> = vec![sig.clone(), sig[..sig.len() - 1].to_vec(), Vec::new()];
        for pos in [0usize, 15, 16, 2927, 2928, 5000, 7855] {
            let mut s = sig.clone();
            s[pos] ^= 0x40;
            cases.push(s);
        }
        if let Some(cs) = &csig {
            cases.push(cs.clone());
        }
        for s in &cases {
            assert_eq!(new::slh_verify_internal(&msg, s, &pk), slhdsa_ref::slh_verify_internal(&msg, s, &pk));
            assert_eq!(new::slh_verify(&msg, s, &ctx, &pk), slhdsa_ref::slh_verify(&msg, s, &ctx, &pk));
        }
        assert!(new::slh_verify_internal(&msg, &sig, &pk));
    }
}
