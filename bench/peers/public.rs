//! One CSV sample per public API operation. Pass a round number to vary the
//! input reproducibly across paired baseline and optimized runs.
use std::{hint::black_box, time::Instant};

fn measure<T>(set: &str, op: &str, round: u8, count: u32, mut f: impl FnMut() -> T) -> T {
    let begin = Instant::now();
    for _ in 1..count {
        black_box(f());
    }
    let result = black_box(f());
    println!(
        "{set},{op},{round},{:.3}",
        begin.elapsed().as_nanos() as f64 / f64::from(count)
    );
    result
}

fn save(set: &str, name: &str, bytes: &[u8]) {
    if let Some(dir) = std::env::var_os("SLH_VECTORS") {
        std::fs::write(std::path::Path::new(&dir).join(format!("{set}.{name}")), bytes).unwrap();
    }
}

macro_rules! bench_set {
    ($set:ident, $peer:ident, $round:expr, $msg:expr, $upstream:expr) => {{
        use slhdsa::$set::{api, params::*};
        let seeds = core::array::from_fn::<_, SEED_BYTES, _>(|i| (i as u8).wrapping_add(42 + $round));
        let entropy = [123 ^ $round; N];
        let msg = $msg;
        let set = stringify!($set);
        if $upstream {
            use upstream::signature::Keypair;
            let key = measure(set, "keygen", $round, 1, || {
                let seeds = black_box(&seeds);
                upstream::SigningKey::<upstream::$peer>::slh_keygen_internal(
                    &seeds[..N], &seeds[N..2 * N], &seeds[2 * N..],
                )
            });
            let pk = key.verifying_key();
            let public = measure(set, "public_key", $round, 256, || black_box(&key).verifying_key().to_bytes());
            let sig = measure(set, "sign", $round, 1, || key.try_sign_with_context(black_box(msg), b"", None).unwrap());
            let hedged = measure(set, "sign_hedged", $round, 1, || key.try_sign_with_context(black_box(msg), b"", Some(&entropy)).unwrap());
            measure(set, "verify", $round, 32, || pk.try_verify_with_context(msg, b"", black_box(&sig)).unwrap());
            save(set, "pk", &public);
            save(set, "sk", &key.to_bytes());
            save(set, "sig", &sig.to_bytes());
            save(set, "hedged", &hedged.to_bytes());
            assert!(pk.try_verify_with_context(msg, b"wrong", &sig).is_err());
        } else {
            let mut sk = [0; SK_BYTES];
            let mut pk = [0; PK_BYTES];
            measure(set, "keygen", $round, 1, || api::keygen(black_box(&seeds), &mut sk, &mut pk));
            let public = measure(set, "public_key", $round, 256, || api::public_key(black_box(&sk)));
            let sig = measure(set, "sign", $round, 1, || api::sign_deterministic(black_box(msg), b"", &sk).unwrap());
            let hedged = measure(set, "sign_hedged", $round, 1, || api::sign(black_box(msg), b"", &sk, &entropy).unwrap());
            measure(set, "verify", $round, 32, || assert!(api::verify(msg, black_box(&sig), b"", &pk)));
            assert_eq!(public, pk);
            save(set, "pk", &public);
            save(set, "sk", &sk);
            save(set, "sig", &sig);
            save(set, "hedged", &hedged);
            assert!(!api::verify(msg, &sig, b"wrong", &pk));
        }
    }};
}

fn main() {
    let mut args = std::env::args().skip(1).filter(|a| a != "--bench");
    let round = args
        .next()
        .map(|a| a.parse::<u8>().expect("round must be 0..255"))
        .unwrap_or(0);
    let len = args
        .next()
        .map(|a| a.parse().expect("message length in bytes"))
        .unwrap_or(32);
    let msg = vec![17 ^ round; len];
    let mut peer = false;
    let mut family = String::from("sha2");
    for option in args {
        match option.as_str() {
            "rustcrypto" => peer = true,
            "sha2" | "shake" | "all" => family = option,
            _ => panic!("expected a hash family or rustcrypto"),
        }
    }
    if family != "shake" {
        bench_set!(sha2_128s, Sha2_128s, round, msg.as_slice(), peer);
        bench_set!(sha2_128f, Sha2_128f, round, msg.as_slice(), peer);
        bench_set!(sha2_192s, Sha2_192s, round, msg.as_slice(), peer);
        bench_set!(sha2_192f, Sha2_192f, round, msg.as_slice(), peer);
        bench_set!(sha2_256s, Sha2_256s, round, msg.as_slice(), peer);
        bench_set!(sha2_256f, Sha2_256f, round, msg.as_slice(), peer);
    }
    if family != "sha2" {
        bench_set!(shake_128s, Shake128s, round, msg.as_slice(), peer);
        bench_set!(shake_128f, Shake128f, round, msg.as_slice(), peer);
        bench_set!(shake_192s, Shake192s, round, msg.as_slice(), peer);
        bench_set!(shake_192f, Shake192f, round, msg.as_slice(), peer);
        bench_set!(shake_256s, Shake256s, round, msg.as_slice(), peer);
        bench_set!(shake_256f, Shake256f, round, msg.as_slice(), peer);
    }
}
