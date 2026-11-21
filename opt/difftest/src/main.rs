//! Differential check between the original crate (`rust/`) and the optimised
//! one (`opt/rust/`). Built twice, once against each (see `../run.sh`); both
//! builds print every output of every public function on the NIST vectors and
//! on pseudo-random inputs, and the two transcripts must be byte-identical.
//!
//! Usage: dump <vectors.json> <random cases>

use serde_json::Value;
use slhdsa::sha256::{hmac_sha256, sha256};
use slhdsa::*;

/// SplitMix64: deterministic pseudo-random bytes, no dependencies.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn arr<const L: usize>(&mut self) -> [u8; L] {
        self.bytes(L).try_into().unwrap()
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn h(v: &Value) -> Vec<u8> {
    hex::decode(v.as_str().unwrap()).unwrap()
}
fn arr<const L: usize>(v: &Value) -> [u8; L] {
    h(v).try_into().unwrap()
}
fn x(b: &[u8]) -> String {
    hex::encode(b)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let v: Value = serde_json::from_str(&std::fs::read_to_string(&args[1]).unwrap()).unwrap();
    let cases: usize = args[2].parse().unwrap();

    // NIST vectors: outputs, not just pass/fail.
    for g in v["keyGen"].as_array().unwrap() {
        for t in g["tests"].as_array().unwrap() {
            let (sk, pk) = slh_keygen_internal(&arr(&t["skSeed"]), &arr(&t["skPrf"]), &arr(&t["pkSeed"]));
            println!("kat-keygen {} {} {}", t["tcId"], x(&sk), x(&pk));
        }
    }
    for g in v["sigGen"].as_array().unwrap() {
        let det = g["deterministic"].as_bool().unwrap();
        let internal = g["signatureInterface"] == "internal";
        for t in g["tests"].as_array().unwrap() {
            let sk: [u8; 64] = arr(&t["sk"]);
            let rnd: [u8; 16] = if det { sk[32..48].try_into().unwrap() } else { arr(&t["additionalRandomness"]) };
            let msg = h(&t["message"]);
            let sig = if internal {
                Some(slh_sign_internal(&msg, &sk, &rnd))
            } else {
                slh_sign(&msg, &h(&t["context"]), &sk, &rnd)
            };
            println!("kat-sign {} {:?}", t["tcId"], sig.map(|s| x(&s)));
        }
    }
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
            println!("kat-verify {} {}", t["tcId"], ok);
        }
    }

    // Pseudo-random inputs.
    let mut r = Rng(0x5eed_0f_5eed);
    for len in 0..300 {
        let m = r.bytes(len);
        let kl = r.below(65) as usize;
        let k = r.bytes(kl);
        println!("sha {} {} {}", len, x(&sha256(&m)), x(&hmac_sha256(&k, &m)));
    }
    for c in 0..cases {
        let (sk, pk) = slh_keygen_internal(&r.arr(), &r.arr(), &r.arr());
        println!("rnd-keygen {} {} {}", c, x(&sk), x(&pk));
        let ml = r.below(300) as usize;
        let msg = r.bytes(ml);
        let cl = if c % 5 == 4 { 256 } else { r.below(40) as usize };
        let ctx = r.bytes(cl);
        let rnd: [u8; 16] = r.arr();
        let sig_i = slh_sign_internal(&msg, &sk, &rnd);
        let sig = slh_sign(&msg, &ctx, &sk, &rnd);
        println!("rnd-sign {} {} {:?}", c, x(&sig_i), sig.as_ref().map(|s| x(s)));
        let mut verdicts = vec![slh_verify_internal(&msg, &sig_i, &pk)];
        let s = sig.unwrap_or_else(|| sig_i.clone());
        verdicts.push(slh_verify(&msg, &s, &ctx, &pk));
        // Tamper: one random bit of the signature, of the message, of the key.
        let mut t = s.clone();
        let pos = r.below(t.len() as u64) as usize;
        let bit = r.below(8);
        t[pos] ^= 1 << bit;
        verdicts.push(slh_verify(&msg, &t, &ctx, &pk));
        verdicts.push(slh_verify_internal(&msg, &t, &pk));
        let mut m2 = msg.clone();
        m2.push(0);
        verdicts.push(slh_verify(&m2, &s, &ctx, &pk));
        let mut pk2 = pk;
        let pp = r.below(32) as usize;
        pk2[pp] ^= 1;
        verdicts.push(slh_verify(&msg, &s, &ctx, &pk2));
        // Wrong lengths.
        verdicts.push(slh_verify_internal(&msg, &s[..s.len() - 1], &pk));
        let mut long = s.clone();
        long.push(0);
        verdicts.push(slh_verify_internal(&msg, &long, &pk));
        // Random garbage of the right length.
        let junk = r.bytes(7856);
        verdicts.push(slh_verify_internal(&msg, &junk, &pk));
        println!("rnd-verify {} {:?}", c, verdicts);
    }
}
