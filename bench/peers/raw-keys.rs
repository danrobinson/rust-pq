//! Higher-resolution paired measurements for the three fixed-size raw key APIs.
use std::{hint::black_box, time::Instant};
use upstream::signature::Keypair;

fn measure<T>(mut f: impl FnMut() -> T) -> f64 {
    const CALLS: u32 = 100_000;
    let start = Instant::now();
    for _ in 0..CALLS {
        black_box(f());
    }
    start.elapsed().as_nanos() as f64 / f64::from(CALLS)
}

fn compare<A, B>(
    set: &str,
    op: &str,
    round: u8,
    library: impl FnMut() -> A,
    peer: impl FnMut() -> B,
) {
    let (ours, theirs) = if round % 2 == 0 {
        (measure(library), measure(peer))
    } else {
        let t = measure(peer);
        (measure(library), t)
    };
    println!("{set},{op},{round},{ours},{theirs}");
}

macro_rules! bench_set {
    ($set:ident, $peer:ident, $round:expr) => {{
        use slhdsa::$set::{api, encoding, params::*};
        let sk = core::array::from_fn::<_, SK_BYTES, _>(|i| (i as u8).wrapping_add(42 + $round));
        let pk = api::public_key(&sk);
        type Sk = upstream::SigningKey<upstream::$peer>;
        type Pk = upstream::VerifyingKey<upstream::$peer>;
        let key = Sk::try_from(&sk[..]).unwrap();
        assert_eq!(&pk[..], &key.verifying_key().to_bytes()[..]);
        compare(
            stringify!($set),
            "public_key",
            $round,
            || api::public_key(black_box(&sk)),
            || black_box(&key).verifying_key().to_bytes(),
        );
        compare(
            stringify!($set),
            "secret_key_from",
            $round,
            || encoding::secret_key_from(black_box(&sk[..])).unwrap(),
            || Sk::try_from(black_box(&sk[..])).unwrap(),
        );
        compare(
            stringify!($set),
            "public_key_from",
            $round,
            || encoding::public_key_from(black_box(&pk[..])).unwrap(),
            || Pk::try_from(black_box(&pk[..])).unwrap(),
        );
    }};
}

fn main() {
    println!("set,operation,round,library_ns,rustcrypto_ns");
    for round in 0..=20 {
        bench_set!(sha2_128s, Sha2_128s, round);
        bench_set!(sha2_128f, Sha2_128f, round);
        bench_set!(sha2_192s, Sha2_192s, round);
        bench_set!(sha2_192f, Sha2_192f, round);
        bench_set!(sha2_256s, Sha2_256s, round);
        bench_set!(sha2_256f, Sha2_256f, round);
        bench_set!(shake_128s, Shake128s, round);
        bench_set!(shake_128f, Shake128f, round);
        bench_set!(shake_192s, Shake192s, round);
        bench_set!(shake_192f, Shake192f, round);
        bench_set!(shake_256s, Shake256s, round);
        bench_set!(shake_256f, Shake256f, round);
    }
}
