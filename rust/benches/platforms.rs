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
        "{set},{op},{round},{}",
        begin.elapsed().as_nanos() / u128::from(count)
    );
    result
}

macro_rules! bench_set {
    ($set:ident, $peer:ident, $round:expr, $msg:expr, $upstream:expr) => {{
        use slhdsa::$set::{api, params::*};
        let seeds = [42u8.wrapping_add($round); SEED_BYTES];
        let mut sk = [0; SK_BYTES];
        let mut pk = [0; PK_BYTES];
        let msg = $msg;
        let set = stringify!($set);
        if $upstream {
            use upstream::signature::Keypair;
            let key = measure(set, "keygen", $round, 1, || {
                let seeds = black_box(&seeds);
                upstream::SigningKey::<upstream::$peer>::slh_keygen_internal(
                    &seeds[..N],
                    &seeds[N..2 * N],
                    &seeds[2 * N..],
                )
            });
            let pk = key.verifying_key();
            let sig = measure(set, "sign", $round, 1, || {
                key.try_sign_with_context(black_box(msg), b"", None)
                    .unwrap()
            });
            measure(set, "verify", $round, 32, || {
                pk.try_verify_with_context(msg, b"", black_box(&sig))
                    .unwrap()
            });
        } else {
            measure(set, "keygen", $round, 1, || {
                api::keygen(black_box(&seeds), &mut sk, &mut pk)
            });
            let sig = measure(set, "sign", $round, 1, || {
                api::sign_deterministic(black_box(msg), b"", &sk).unwrap()
            });
            measure(set, "verify", $round, 32, || {
                assert!(api::verify(msg, black_box(&sig), b"", &pk))
            });
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
    let peer = match args.next().as_deref() {
        None => false,
        Some("rustcrypto") => true,
        _ => panic!("expected rustcrypto or no backend argument"),
    };
    bench_set!(sha2_128s, Sha2_128s, round, msg.as_slice(), peer);
    bench_set!(sha2_128f, Sha2_128f, round, msg.as_slice(), peer);
    bench_set!(sha2_192s, Sha2_192s, round, msg.as_slice(), peer);
    bench_set!(sha2_192f, Sha2_192f, round, msg.as_slice(), peer);
    bench_set!(sha2_256s, Sha2_256s, round, msg.as_slice(), peer);
    bench_set!(sha2_256f, Sha2_256f, round, msg.as_slice(), peer);
}
