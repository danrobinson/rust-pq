//! NIST ACVP known-answer tests for all six SHA-2 parameter sets, reference
//! checks for the hash functions, and a cross-test against the original
//! single-parameter-set crate (`../../rust`).

use serde_json::Value;
use slhdsa::params::{Params, SHA2_128F, SHA2_128S, SHA2_192F, SHA2_192S, SHA2_256F, SHA2_256S};

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

fn arr<const L: usize>(v: &Value) -> [u8; L] {
    h(v).try_into().unwrap()
}

#[test]
fn table_2_sizes() {
    let expect = [(32, 7856), (32, 17088), (48, 16224), (48, 35664), (64, 29792), (64, 49856)];
    for ((name, p), (pk, sig)) in SETS.iter().zip(expect) {
        assert_eq!(2 * p.n, pk, "{name}");
        assert_eq!(p.sig_bytes(), sig, "{name}");
        assert_eq!(p.h, p.d * p.hp, "{name}");
        assert_eq!(p.m, p.md_bytes() + p.tree_bytes() + p.leaf_bytes(), "{name}");
        assert!(p.len() <= slhdsa::params::LEN_MAX && p.k as usize <= slhdsa::params::K_MAX, "{name}");
    }
    macro_rules! n_agrees { ($($m:ident),*) => {$(
        assert_eq!(slhdsa::$m::params::PARAMS.n, slhdsa::$m::params::N);
        assert_eq!(slhdsa::$m::params::PARAMS.sig_bytes(), slhdsa::$m::params::SIG_BYTES);
    )*}}
    n_agrees!(sha2_128s, sha2_128f, sha2_192s, sha2_192f, sha2_256s, sha2_256f);
    assert_eq!(slhdsa::sha2_128s::params::SIG_BYTES, 7856);
    assert_eq!(slhdsa::sha2_128f::params::SIG_BYTES, 17088);
    assert_eq!(slhdsa::sha2_192s::params::SIG_BYTES, 16224);
    assert_eq!(slhdsa::sha2_192f::params::SIG_BYTES, 35664);
    assert_eq!(slhdsa::sha2_256s::params::SIG_BYTES, 29792);
    assert_eq!(slhdsa::sha2_256f::params::SIG_BYTES, 49856);
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
    // Continuing from a state after one block, as the hash functions do.
    for len in 0..300 {
        let st = slhdsa::sha512::compress(&slhdsa::sha512::H0, &data, 0);
        let ours = slhdsa::sha512::sha512_from(&st, 128, &data[128..128 + len]);
        let theirs = sha2::Sha512::digest(&data[..128 + len]);
        assert_eq!(&ours[..], &theirs[..], "from, len {len}");
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

/// `PRF_msg` and `H_msg` against HMAC and MGF1 written with the `sha2` and
/// `hmac` crates, at message lengths around the block boundaries where the
/// code switches between copying and hashing in place.
#[test]
fn prf_msg_and_h_msg_match_reference() {
    use hmac::Mac;
    use sha2::Digest;
    fn mgf1<D: Digest>(seed: &[u8], len: usize) -> Vec<u8> {
        let mut t = Vec::new();
        let mut c = 0u32;
        while t.len() < len {
            let mut d = D::new();
            d.update(seed);
            d.update(c.to_be_bytes());
            t.extend_from_slice(&d.finalize());
            c += 1;
        }
        t.truncate(len);
        t
    }
    fn check<const N: usize>(p: &Params) {
        let data: Vec<u8> = (0..400u32).map(|i| (i * 31 + 7) as u8).collect();
        let k: [u8; N] = data[0..N].try_into().unwrap();
        let o: [u8; N] = data[N..2 * N].try_into().unwrap();
        let s: [u8; N] = data[2 * N..3 * N].try_into().unwrap();
        for len in (0..=140).chain([200, 255, 256, 257, 399 - 3 * N]) {
            let m = &data[3 * N..3 * N + len];
            let r = slhdsa::hash::prf_msg::<N>(&k, &o, m);
            let want = if N == 16 {
                let mut mac = hmac::Hmac::<sha2::Sha256>::new_from_slice(&k).unwrap();
                mac.update(&o);
                mac.update(m);
                mac.finalize().into_bytes()[..N].to_vec()
            } else {
                let mut mac = hmac::Hmac::<sha2::Sha512>::new_from_slice(&k).unwrap();
                mac.update(&o);
                mac.update(m);
                mac.finalize().into_bytes()[..N].to_vec()
            };
            assert_eq!(r.to_vec(), want, "PRF_msg n = {N} len {len}");
            let dig = slhdsa::hash::h_msg::<N>(p, &r, &s, &o, m);
            let want = if N == 16 {
                let inner = sha2::Sha256::digest([&r[..], &s, &o, m].concat());
                mgf1::<sha2::Sha256>(&[&r[..], &s, &inner].concat(), p.m)
            } else {
                let inner = sha2::Sha512::digest([&r[..], &s, &o, m].concat());
                mgf1::<sha2::Sha512>(&[&r[..], &s, &inner].concat(), p.m)
            };
            assert_eq!(dig, want, "H_msg n = {N} m = {} len {len}", p.m);
        }
    }
    check::<16>(&SHA2_128S);
    check::<16>(&SHA2_128F);
    check::<24>(&SHA2_192S);
    check::<24>(&SHA2_192F);
    check::<32>(&SHA2_256S);
    check::<32>(&SHA2_256F);
}

macro_rules! acvp {
    ($($name:ident, $set:literal, $m:ident;)*) => {$(
        mod $name {
            use super::{arr, h, vectors};
            use slhdsa::$m as s;
            use s::params::{N, SIG_BYTES};

            #[test]
            fn keygen() {
                let v = vectors($set);
                let mut n = 0;
                for g in v["keyGen"].as_array().unwrap() {
                    for t in g["tests"].as_array().unwrap() {
                        let (sk, pk) = s::slh_keygen_internal(&arr(&t["skSeed"]), &arr(&t["skPrf"]), &arr(&t["pkSeed"]));
                        assert_eq!(sk.to_vec(), h(&t["sk"]), "{} tcId {}", $set, t["tcId"]);
                        assert_eq!(pk.to_vec(), h(&t["pk"]), "{} tcId {}", $set, t["tcId"]);
                        // The interface function on the concatenated seeds.
                        let seeds: Vec<u8> = [h(&t["skSeed"]), h(&t["skPrf"]), h(&t["pkSeed"])].concat();
                        let (mut sk2, mut pk2) = ([0u8; s::params::SK_BYTES], [0u8; s::params::PK_BYTES]);
                        s::api::keygen(&seeds.try_into().unwrap(), &mut sk2, &mut pk2);
                        assert_eq!((sk2, pk2), (sk, pk));
                        assert_eq!(s::api::public_key(&sk), pk);
                        n += 1;
                    }
                }
                assert_eq!(n, 10);
            }

            #[test]
            fn siggen() {
                let v = vectors($set);
                let mut n = 0;
                for g in v["sigGen"].as_array().unwrap() {
                    let det = g["deterministic"].as_bool().unwrap();
                    let internal = g["signatureInterface"] == "internal";
                    for t in g["tests"].as_array().unwrap() {
                        let sk: [u8; 4 * N] = arr(&t["sk"]);
                        let rnd: [u8; N] = if det { sk[2 * N..3 * N].try_into().unwrap() } else { arr(&t["additionalRandomness"]) };
                        let msg = h(&t["message"]);
                        let want = h(&t["signature"]);
                        let sig = if internal {
                            let sig = s::slh_sign_internal(&msg, &sk, &rnd);
                            assert!(s::slh_sign_internal_checked(&msg, &sk, &rnd).as_ref() == Some(&sig));
                            sig
                        } else {
                            let ctx = h(&t["context"]);
                            let sig = s::slh_sign(&msg, &ctx, &sk, &rnd).unwrap();
                            assert!(s::slh_sign_checked(&msg, &ctx, &sk, &rnd).as_ref() == Some(&sig));
                            if det {
                                assert!(s::api::sign_deterministic(&msg, &ctx, &sk).as_ref() == Some(&sig));
                            } else {
                                assert!(s::api::sign(&msg, &ctx, &sk, &rnd).as_ref() == Some(&sig));
                            }
                            sig
                        };
                        assert_eq!(sig.len(), SIG_BYTES);
                        assert!(sig == want, "{} tcId {}", $set, t["tcId"]);
                        n += 1;
                    }
                }
                assert_eq!(n, 28);
            }

            #[test]
            fn sigver() {
                let v = vectors($set);
                let (mut pass, mut fail) = (0, 0);
                for g in v["sigVer"].as_array().unwrap() {
                    let internal = g["signatureInterface"] == "internal";
                    for t in g["tests"].as_array().unwrap() {
                        let pk: [u8; 2 * N] = arr(&t["pk"]);
                        let msg = h(&t["message"]);
                        let sig = h(&t["signature"]);
                        let ok = if internal {
                            s::slh_verify_internal(&msg, &sig, &pk)
                        } else {
                            let ctx = h(&t["context"]);
                            let ok = s::slh_verify(&msg, &sig, &ctx, &pk);
                            assert_eq!(s::api::verify(&msg, &sig, &ctx, &pk), ok);
                            ok
                        };
                        assert_eq!(ok, t["testPassed"].as_bool().unwrap(), "{} tcId {} ({})", $set, t["tcId"], t["reason"]);
                        if ok { pass += 1 } else { fail += 1 }
                    }
                }
                assert_eq!(pass + fail, 28);
                assert!(pass > 0 && fail > 0);
            }

            /// Round trip and rejection of tampering through the typed module.
            #[test]
            fn roundtrip_and_tamper() {
                let (sk, pk) = s::slh_keygen_internal(&[1; N], &[2; N], &[3; N]);
                let msg = b"hash-based signatures";
                let mut sig = s::slh_sign(msg, b"ctx", &sk, &[4; N]).unwrap();
                assert_eq!(sig.len(), SIG_BYTES);
                assert!(s::slh_sign(msg, &[0; 256], &sk, &[4; N]).is_none());
                assert!(s::slh_verify(msg, &sig, b"ctx", &pk));
                assert!(!s::slh_verify(msg, &sig, b"other", &pk));
                assert!(!s::slh_verify(b"hash-based signature", &sig, b"ctx", &pk));
                assert!(!s::slh_verify(msg, &sig, &[0; 256], &pk));
                let last = sig.len() - 1;
                for pos in [0, N, 3000, last] {
                    sig[pos] ^= 1;
                    assert!(!s::slh_verify(msg, &sig, b"ctx", &pk));
                    sig[pos] ^= 1;
                }
                assert!(!s::slh_verify(msg, &sig[..last], b"ctx", &pk));
                let isig = s::slh_sign_internal(msg, &sk, &[5; N]);
                assert!(s::slh_verify_internal(msg, &isig, &pk));
                assert!(!s::slh_verify_internal(msg, &sig, &pk));
            }
        }
    )*};
}
acvp! {
    acvp_128s, "128s", sha2_128s;
    acvp_128f, "128f", sha2_128f;
    acvp_192s, "192s", sha2_192s;
    acvp_192f, "192f", sha2_192f;
    acvp_256s, "256s", sha2_256s;
    acvp_256f, "256f", sha2_256f;
}

/// A small deterministic generator for the cross-test inputs.
fn fill(seed: &mut u64, out: &mut [u8]) {
    for b in out.iter_mut() {
        *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *b = (*seed >> 56) as u8;
    }
}

/// 128s behaviour is identical to the original single-parameter-set crate:
/// the internal and pure functions, the checked signer, the interface module
/// and the encodings.
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
        let seeds: [u8; 48] = [a, b, c].concat().try_into().unwrap();
        let (mut sk1, mut pk1, mut sk2, mut pk2) = ([0u8; 64], [0u8; 32], [0u8; 64], [0u8; 32]);
        new::api::keygen(&seeds, &mut sk1, &mut pk1);
        slhdsa_ref::api::keygen(&seeds, &mut sk2, &mut pk2);
        assert_eq!((sk1, pk1), (sk2, pk2));
        assert_eq!(new::api::public_key(&sk), slhdsa_ref::api::public_key(&sk));
        let mut msg = vec![0u8; [0, 1, 55, 64, 200, 1000][round]];
        fill(&mut seed, &mut msg);
        let mut ctx = vec![0u8; [0, 1, 17, 255, 256, 3][round]];
        fill(&mut seed, &mut ctx);
        let sig = new::slh_sign_internal(&msg, &sk, &rnd);
        assert!(sig == slhdsa_ref::slh_sign_internal(&msg, &sk, &rnd));
        assert!(new::slh_sign_internal_checked(&msg, &sk, &rnd) == slhdsa_ref::slh_sign_internal_checked(&msg, &sk, &rnd));
        let csig = new::slh_sign(&msg, &ctx, &sk, &rnd);
        assert!(csig == slhdsa_ref::slh_sign(&msg, &ctx, &sk, &rnd));
        assert!(new::slh_sign_checked(&msg, &ctx, &sk, &rnd) == slhdsa_ref::slh_sign_checked(&msg, &ctx, &sk, &rnd));
        assert!(new::api::sign(&msg, &ctx, &sk, &rnd) == slhdsa_ref::api::sign(&msg, &ctx, &sk, &rnd));
        assert!(new::api::sign_deterministic(&msg, &ctx, &sk) == slhdsa_ref::api::sign_deterministic(&msg, &ctx, &sk));
        assert!(new::api::sign_checked(&msg, &ctx, &sk, &rnd) == slhdsa_ref::api::sign_checked(&msg, &ctx, &sk, &rnd));
        assert!(
            new::api::sign_deterministic_checked(&msg, &ctx, &sk)
                == slhdsa_ref::api::sign_deterministic_checked(&msg, &ctx, &sk)
        );
        // A damaged key: both checked signers refuse, both plain signers agree.
        let mut bad = sk;
        bad[[0, 15, 32, 47, 48, 63][round]] ^= 0x10;
        assert!(new::slh_sign_internal_checked(&msg, &bad, &rnd).is_none());
        assert!(slhdsa_ref::slh_sign_internal_checked(&msg, &bad, &rnd).is_none());
        assert!(new::api::sign(&msg, b"", &bad, &rnd) == slhdsa_ref::api::sign(&msg, b"", &bad, &rnd));
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
            assert_eq!(new::api::verify(&msg, s, &ctx, &pk), slhdsa_ref::api::verify(&msg, s, &ctx, &pk));
        }
        assert!(new::slh_verify_internal(&msg, &sig, &pk));
        // Encodings.
        use new::encoding as e;
        use slhdsa_ref::encoding as r;
        assert_eq!(e::PKCS8_PREFIX, r::PKCS8_PREFIX);
        assert_eq!(e::SPKI_PREFIX, r::SPKI_PREFIX);
        let (mut d1, mut d2) = ([0u8; 84], [0u8; 84]);
        e::pkcs8_encode(&sk, &mut d1);
        r::pkcs8_encode(&sk, &mut d2);
        assert_eq!(d1, d2);
        assert_eq!(e::spki_encode(&pk), r::spki_encode(&pk));
        for bytes in [&d1[..], &d1[..83], &d1[1..], &e::spki_encode(&pk)[..], &sk[..], &pk[..], &sig[..], &[][..]] {
            let (mut k1, mut k2) = ([7u8; 64], [7u8; 64]);
            assert_eq!(e::pkcs8_decode(bytes, &mut k1), r::pkcs8_decode(bytes, &mut k2));
            assert_eq!(k1, k2);
            assert_eq!(e::spki_decode(bytes), r::spki_decode(bytes));
            assert_eq!(e::secret_key_from(bytes), r::secret_key_from(bytes));
            assert_eq!(e::public_key_from(bytes), r::public_key_from(bytes));
            assert_eq!(e::signature_len_ok(bytes), r::signature_len_ok(bytes));
        }
        assert_eq!(e::secret_keys_equal(&sk, &bad), r::secret_keys_equal(&sk, &bad));
        assert_eq!(e::secret_keys_equal(&sk, &sk), r::secret_keys_equal(&sk, &sk));
    }
}
