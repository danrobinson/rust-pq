//! Raw key import and standard DER conversion of fixed, length-valid key material.
use pkcs8::{DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey};
use std::{hint::black_box, time::Instant};

fn measure<T>(set: &str, op: &str, round: u8, mut f: impl FnMut() -> T) -> T {
    let count = 256;
    let start = Instant::now();
    for _ in 1..count {
        black_box(f());
    }
    let result = black_box(f());
    println!("{set},{op},{round},{:.3}", start.elapsed().as_nanos() as f64 / f64::from(count));
    result
}

fn save(set: &str, ext: &str, bytes: &[u8]) {
    let folder = std::env::var_os("SLH_VECTORS").unwrap();
    std::fs::write(std::path::Path::new(&folder).join(format!("{set}.{ext}")), bytes).unwrap();
}

macro_rules! bench_set {
    ($set:ident, $peer:ident, $round:expr, $upstream:expr) => {{
        use slhdsa::$set::{encoding, params::*};
        let sk = core::array::from_fn::<_, SK_BYTES, _>(|i| (i as u8).wrapping_add(42 + $round));
        let pk: [u8; PK_BYTES] = sk[2*N..].try_into().unwrap();
        let set = stringify!($set);
        if $upstream {
            type Sk = upstream::SigningKey<upstream::$peer>;
            type Pk = upstream::VerifyingKey<upstream::$peer>;
            let secret = measure(set,"secret_key_from",$round,|| Sk::try_from(black_box(&sk[..])).unwrap());
            let public = measure(set,"public_key_from",$round,|| Pk::try_from(black_box(&pk[..])).unwrap());
            let p8 = measure(set,"pkcs8_encode",$round,|| black_box(&secret).to_pkcs8_der().unwrap());
            let spki = measure(set,"spki_encode",$round,|| black_box(&public).to_public_key_der().unwrap());
            let sk2 = measure(set,"pkcs8_decode",$round,|| Sk::from_pkcs8_der(black_box(p8.as_bytes())).unwrap());
            let pk2 = measure(set,"spki_decode",$round,|| Pk::from_public_key_der(black_box(spki.as_bytes())).unwrap());
            assert_eq!(&sk2.to_bytes()[..], sk);
            assert_eq!(&pk2.to_bytes()[..], pk);
            save(set, "p8", p8.as_bytes());
            save(set, "spki", spki.as_bytes());
        } else {
            let secret = measure(set,"secret_key_from",$round,|| encoding::secret_key_from(black_box(&sk)).unwrap());
            let public = measure(set,"public_key_from",$round,|| encoding::public_key_from(black_box(&pk)).unwrap());
            let p8 = measure(set,"pkcs8_encode",$round,|| {
                let mut der = [0; PKCS8_BYTES];
                encoding::pkcs8_encode(black_box(&secret), &mut der);
                der
            });
            let spki = measure(set,"spki_encode",$round,|| encoding::spki_encode(black_box(&public)));
            let sk2 = measure(set,"pkcs8_decode",$round,|| {
                let mut key = [0; SK_BYTES];
                assert!(encoding::pkcs8_decode(black_box(&p8), &mut key));
                key
            });
            let pk2 = measure(set,"spki_decode",$round,|| encoding::spki_decode(black_box(&spki)).unwrap());
            assert_eq!(sk, sk2);
            assert_eq!(pk, pk2);
            save(set, "p8", &p8);
            save(set, "spki", &spki);
        }
    }};
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let round: u8 = args[1].parse().unwrap();
    let peer = args[2] == "rustcrypto";
    bench_set!(sha2_128s, Sha2_128s, round, peer);
    bench_set!(sha2_128f, Sha2_128f, round, peer);
    bench_set!(sha2_192s, Sha2_192s, round, peer);
    bench_set!(sha2_192f, Sha2_192f, round, peer);
    bench_set!(sha2_256s, Sha2_256s, round, peer);
    bench_set!(sha2_256f, Sha2_256f, round, peer);
    bench_set!(shake_128s, Shake128s, round, peer);
    bench_set!(shake_128f, Shake128f, round, peer);
    bench_set!(shake_192s, Shake192s, round, peer);
    bench_set!(shake_192f, Shake192f, round, peer);
    bench_set!(shake_256s, Shake256s, round, peer);
    bench_set!(shake_256f, Shake256f, round, peer);
}
