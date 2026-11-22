//! keygen / sign / verify of the verified crate (../rust) for each of the six SLH-DSA-SHA2
//! parameter sets, next to RustCrypto's `slh-dsa` for the same set, on a 32-byte message with an
//! empty context (deterministic signing, opt_rand = PK.seed). Each implementation verifies its
//! own signature, and the two signatures are checked to be byte-identical before timing.
//!
//! `BENCH_SETS=128s,192f` restricts the sets. With this crate's `hw` feature the verified crate
//! is built with `hw-sha2` (SHA-512, used by the 192 and 256 sets, stays portable).
use criterion::{criterion_group, criterion_main, Criterion, SamplingMode};
use std::hint::black_box;
use std::time::Duration;

macro_rules! set {
    ($c:expr, $name:literal, $ours:ident, $theirs:ident) => {{
        use slh_dsa::{Signature, SigningKey, VerifyingKey};
        use slhdsa::$ours as v;
        const N: usize = v::params::N;
        let (a, b, c) = ([0x11u8; N], [0x22u8; N], [0x33u8; N]);
        let m = slhdsa_bench::message(32);
        let ours = if cfg!(feature = "hw") { "verified+hw-sha2" } else { "verified" };
        let (sk, pk) = v::slh_keygen_internal(&a, &b, &c);
        let rsk = SigningKey::<slh_dsa::$theirs>::slh_keygen_internal(&a, &b, &c);
        let rvk = VerifyingKey::<slh_dsa::$theirs>::try_from(&pk[..]).unwrap();
        let sig = v::slh_sign(&m, &[], &sk, &c).unwrap();
        let rsig = rsk.try_sign_with_context(&m, &[], None).unwrap().to_vec();
        assert_eq!(rsk.to_bytes().to_vec(), sk.to_vec(), concat!($name, ": keys differ"));
        assert!(sig == rsig, concat!($name, ": signatures differ"));
        let rsig = Signature::<slh_dsa::$theirs>::try_from(&rsig[..]).unwrap();
        assert!(v::slh_verify(&m, &sig, &[], &pk) && rvk.try_verify_with_context(&m, &[], &rsig).is_ok());

        let mut g = $c.benchmark_group(concat!("keygen_", $name));
        g.sampling_mode(SamplingMode::Flat).sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(3));
        g.bench_function(ours, |bch| bch.iter(|| v::slh_keygen_internal(black_box(&a), black_box(&b), black_box(&c))));
        g.bench_function("rustcrypto-slh-dsa", |bch| {
            bch.iter(|| SigningKey::<slh_dsa::$theirs>::slh_keygen_internal(black_box(&a), black_box(&b), black_box(&c)))
        });
        g.finish();
        let mut g = $c.benchmark_group(concat!("sign_32B_", $name));
        g.sampling_mode(SamplingMode::Flat).sample_size(10).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(4));
        g.bench_function(ours, |bch| bch.iter(|| v::slh_sign(black_box(&m), &[], &sk, &c).unwrap()));
        g.bench_function("rustcrypto-slh-dsa", |bch| bch.iter(|| rsk.try_sign_with_context(black_box(&m), &[], None).unwrap()));
        g.finish();
        let mut g = $c.benchmark_group(concat!("verify_32B_", $name));
        g.sample_size(20).warm_up_time(Duration::from_secs(1)).measurement_time(Duration::from_secs(2));
        g.bench_function(ours, |bch| bch.iter(|| assert!(v::slh_verify(black_box(&m), black_box(&sig), &[], &pk))));
        g.bench_function("rustcrypto-slh-dsa", |bch| {
            bch.iter(|| assert!(rvk.try_verify_with_context(black_box(&m), &[], black_box(&rsig)).is_ok()))
        });
        g.finish();
    }};
}

fn benches(c: &mut Criterion) {
    let only = std::env::var("BENCH_SETS").ok();
    let want = |s: &str| only.as_deref().map_or(true, |o| o.split(',').any(|x| x == s));
    if want("128s") { set!(c, "128s", sha2_128s, Sha2_128s) }
    if want("128f") { set!(c, "128f", sha2_128f, Sha2_128f) }
    if want("192s") { set!(c, "192s", sha2_192s, Sha2_192s) }
    if want("192f") { set!(c, "192f", sha2_192f, Sha2_192f) }
    if want("256s") { set!(c, "256s", sha2_256s, Sha2_256s) }
    if want("256f") { set!(c, "256f", sha2_256f, Sha2_256f) }
}

criterion_group!(sets, benches);
criterion_main!(sets);
