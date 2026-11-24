#[cfg(not(feature = "opencl"))]
use slh_experiments::gpu::NoGpu;
use std::{hint::black_box, time::Instant};

fn time<T>(set: &str, op: &str, round: u8, count: u32, mut f: impl FnMut() -> T) -> T {
    let start = Instant::now();
    for _ in 1..count {
        black_box(f());
    }
    let out = black_box(f());
    println!(
        "{set},{op},{round},{}",
        start.elapsed().as_nanos() / u128::from(count)
    );
    out
}

macro_rules! suite {
    ($module:ident, $name:literal, $round:ident, $msg:ident, $gpu:expr) => {{
        use slh_experiments::$module::*;
        let seed = |offset: u8| std::array::from_fn(|i| 42 + $round + offset + i as u8);
        let sk = time($name, "keygen", $round, 1, || {
            #[cfg(feature = "multithread")]
            return SlhSecretKey::derive_with_cache(black_box(seed(0)), seed(16), seed(32), $gpu);
            #[cfg(not(feature = "multithread"))]
            return SlhSecretKey::derive_without_cache(
                black_box(seed(0)),
                seed(16),
                seed(32),
                $gpu,
            );
        });
        let pk = sk.pubkey();
        let public = time($name, "public_key", $round, 256, || {
            black_box(&sk).pubkey().to_bytes()
        });
        let entropy = [123 ^ $round; 16];
        let sign =
            |rng| slh_dsa_signature_serialize(&slh_dsa_sign_pure(&$msg, b"", &sk, rng, $gpu));
        let sig = time($name, "sign", $round, 1, || sign(None));
        let hedged = time($name, "sign_hedged", $round, 1, || sign(Some(&entropy)));
        time($name, "verify", $round, 32, || {
            assert!(slh_dsa_verify_pure(
                &$msg,
                &slh_dsa_signature_deserialize(black_box(&sig)),
                b"",
                &pk
            ))
        });
        assert!(!slh_dsa_verify_pure(
            &$msg,
            &slh_dsa_signature_deserialize(&sig),
            b"wrong",
            &pk
        ));
        for (suffix, data) in [
            ("pk", public.as_slice()),
            ("sk", &sk.to_bytes()),
            ("sig", &sig),
            ("hedged", &hedged),
        ] {
            std::fs::write(
                format!(
                    "{}/{}.{}",
                    std::env::var("SLH_VECTORS").unwrap(),
                    $name,
                    suffix
                ),
                data,
            )
            .unwrap();
        }
    }};
}

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let round: u8 = args[1].parse().unwrap();
    let msg = vec![17 ^ round; args[2].parse().unwrap()];
    #[cfg(feature = "opencl")]
    let accelerator = slh_experiments::gpu::OpenCL::create_gpu()
        .unwrap()
        .expect("GPU required");
    #[cfg(feature = "opencl")]
    let gpu = || &accelerator;
    #[cfg(not(feature = "opencl"))]
    let gpu = || NoGpu;
    suite!(slh_dsa_sha2_128s, "sha2_128s", round, msg, gpu());
    suite!(slh_dsa_sha2_128f, "sha2_128f", round, msg, gpu());
    #[cfg(not(feature = "opencl"))]
    suite!(slh_dsa_shake_128s, "shake_128s", round, msg, gpu());
    #[cfg(not(feature = "opencl"))]
    suite!(slh_dsa_shake_128f, "shake_128f", round, msg, gpu());
}
