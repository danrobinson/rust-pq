//! NIST ACVP known-answer tests.

use serde_json::Value;
use slhdsa_current::*;

fn vectors() -> Value {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../../vectors/slh-dsa-sha2-128s.json");
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn h(v: &Value) -> Vec<u8> {
    hex::decode(v.as_str().unwrap()).unwrap()
}

fn arr<const L: usize>(v: &Value) -> [u8; L] {
    h(v).try_into().unwrap()
}

#[test]
fn sha256_matches_reference() {
    use sha2::Digest;
    let data: Vec<u8> = (0..300u32).map(|i| (i * 7 + 3) as u8).collect();
    for len in 0..300 {
        let ours = slhdsa_current::sha256::sha256(&data[..len]);
        let theirs = sha2::Sha256::digest(&data[..len]);
        assert_eq!(&ours[..], &theirs[..], "len {len}");
    }
}

#[test]
fn hmac_matches_reference() {
    use hmac::Mac;
    let data: Vec<u8> = (0..200u32).map(|i| (i * 13 + 1) as u8).collect();
    for len in [0, 1, 55, 56, 64, 199] {
        let ours = slhdsa_current::sha256::hmac_sha256(&data[..16], &data[..len]);
        let mut mac = hmac::Hmac::<sha2::Sha256>::new_from_slice(&data[..16]).unwrap();
        mac.update(&data[..len]);
        assert_eq!(&ours[..], &mac.finalize().into_bytes()[..]);
    }
}

#[test]
fn acvp_keygen() {
    let v = vectors();
    let mut n = 0;
    for g in v["keyGen"].as_array().unwrap() {
        for t in g["tests"].as_array().unwrap() {
            let (sk, pk) = slh_keygen_internal(&arr(&t["skSeed"]), &arr(&t["skPrf"]), &arr(&t["pkSeed"]));
            assert_eq!(sk.to_vec(), h(&t["sk"]));
            assert_eq!(pk.to_vec(), h(&t["pk"]));
            n += 1;
        }
    }
    assert!(n >= 10);
}

#[test]
fn acvp_siggen() {
    let v = vectors();
    let mut n = 0;
    for g in v["sigGen"].as_array().unwrap() {
        let det = g["deterministic"].as_bool().unwrap();
        let internal = g["signatureInterface"] == "internal";
        for t in g["tests"].as_array().unwrap() {
            let sk: [u8; 64] = arr(&t["sk"]);
            let rnd: [u8; 16] = if det { sk[32..48].try_into().unwrap() } else { arr(&t["additionalRandomness"]) };
            let msg = h(&t["message"]);
            let sig = if internal {
                slh_sign_internal(&msg, &sk, &rnd)
            } else {
                slh_sign(&msg, &h(&t["context"]), &sk, &rnd).unwrap()
            };
            assert_eq!(sig, h(&t["signature"]), "tcId {}", t["tcId"]);
            n += 1;
        }
    }
    assert!(n >= 28);
}

#[test]
fn acvp_sigver() {
    let v = vectors();
    let (mut pass, mut fail) = (0, 0);
    for g in v["sigVer"].as_array().unwrap() {
        let internal = g["signatureInterface"] == "internal";
        for t in g["tests"].as_array().unwrap() {
            let pk: [u8; 32] = arr(&t["pk"]);
            let msg = h(&t["message"]);
            let sig = h(&t["signature"]);
            let ok = if internal {
                slh_verify_internal(&msg, &sig, &pk)
            } else {
                slh_verify(&msg, &sig, &h(&t["context"]), &pk)
            };
            assert_eq!(ok, t["testPassed"].as_bool().unwrap(), "tcId {} ({})", t["tcId"], t["reason"]);
            if ok { pass += 1 } else { fail += 1 }
        }
    }
    assert!(pass > 0 && fail > 0);
}

#[test]
fn roundtrip_and_tamper() {
    let (sk, pk) = slh_keygen_internal(&[1; 16], &[2; 16], &[3; 16]);
    let msg = b"hash-based signatures";
    let mut sig = slh_sign(msg, b"ctx", &sk, &[4; 16]).unwrap();
    assert!(slh_verify(msg, &sig, b"ctx", &pk));
    assert!(!slh_verify(msg, &sig, b"other", &pk));
    assert!(!slh_verify(b"hash-based signature", &sig, b"ctx", &pk));
    for pos in [0, 16, 3000, 7855] {
        sig[pos] ^= 1;
        assert!(!slh_verify(msg, &sig, b"ctx", &pk));
        sig[pos] ^= 1;
    }
    assert!(!slh_verify(msg, &sig[..7855], b"ctx", &pk));
}
