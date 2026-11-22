//! Key generation, signing and verification through this crate and through
//! RustCrypto's `slh-dsa` 0.2.0-rc.5, for the six SHA-2 sets, from the same
//! seeds and messages. Runs alternate between the two crates; the medians and
//! the ranges are printed in milliseconds.
//!
//! ```text
//! cargo run --release --example timing --features hw-sha2
//! cargo run --release --example timing --features hw-sha2,hw-sha512
//! ```
//!
//! Optional arguments: the number of repetitions for key generation and
//! signing (default 7) and for verification (default 31).

use std::hint::black_box;
use std::time::Instant;

fn ms(f: impl FnOnce()) -> f64 {
    let t = Instant::now();
    f();
    t.elapsed().as_secs_f64() * 1e3
}

/// Median, minimum and maximum.
fn stats(mut v: Vec<f64>) -> (f64, f64, f64) {
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let mid = v.len() / 2;
    let med = if v.len() % 2 == 1 { v[mid] } else { (v[mid - 1] + v[mid]) / 2.0 };
    (med, v[0], v[v.len() - 1])
}

fn row(set: &str, op: &str, ours: Vec<f64>, theirs: Vec<f64>) {
    let (om, olo, ohi) = stats(ours);
    let (tm, tlo, thi) = stats(theirs);
    println!(
        "| {set} | {op} | {om:.3} ({olo:.3}–{ohi:.3}) | {tm:.3} ({tlo:.3}–{thi:.3}) | {:.2}× |",
        tm / om
    );
}

macro_rules! time_set {
    ($P:ident, $n:expr, $reps:expr, $vreps:expr) => {{
        use slh_dsa::signature::{Keypair, Signer, Verifier};
        const N: usize = $n;
        let set = stringify!($P);
        let seeds: Vec<u8> = (0..3 * N).map(|i| (i as u8).wrapping_mul(0x9d).wrapping_add(0x3b)).collect();
        let msg = b"timing message, 31 bytes long..";
        let (s1, s2, s3) = (&seeds[..N], &seeds[N..2 * N], &seeds[2 * N..]);

        let (mut ko, mut kt, mut so, mut st, mut vo, mut vt) = (vec![], vec![], vec![], vec![], vec![], vec![]);
        let ours = slh_dsa::SigningKey::<slh_dsa::$P>::slh_keygen_internal(s1, s2, s3);
        let theirs = upstream::SigningKey::<upstream::$P>::slh_keygen_internal(s1, s2, s3);
        assert_eq!(ours.to_bytes().as_slice(), theirs.to_bytes().as_slice());
        let sig_o = ours.sign(msg);
        let sig_t = upstream::signature::Signer::sign(&theirs, msg);
        assert_eq!(sig_o.to_bytes().as_slice(), sig_t.to_bytes().as_slice());
        let vk_o = ours.verifying_key();
        let vk_t = upstream::signature::Keypair::verifying_key(&theirs);
        for _ in 0..$reps {
            ko.push(ms(|| drop(black_box(slh_dsa::SigningKey::<slh_dsa::$P>::slh_keygen_internal(s1, s2, s3)))));
            kt.push(ms(|| drop(black_box(upstream::SigningKey::<upstream::$P>::slh_keygen_internal(s1, s2, s3)))));
            so.push(ms(|| drop(black_box(ours.sign(black_box(msg))))));
            st.push(ms(|| drop(black_box(upstream::signature::Signer::sign(&theirs, black_box(msg))))));
        }
        for _ in 0..$vreps {
            vo.push(ms(|| assert!(vk_o.verify(black_box(msg), &sig_o).is_ok())));
            vt.push(ms(|| assert!(upstream::signature::Verifier::verify(&vk_t, black_box(msg), &sig_t).is_ok())));
        }
        row(set, "keygen", ko, kt);
        row(set, "sign", so, st);
        row(set, "verify", vo, vt);
    }};
}

fn main() {
    let args: Vec<usize> = std::env::args().skip(1).map(|a| a.parse().expect("a number")).collect();
    let reps = args.first().copied().unwrap_or(7);
    let vreps = args.get(1).copied().unwrap_or(31);
    println!(
        "features: hw-sha2 {}, hw-sha512 {}; {reps} runs of keygen and sign, {vreps} of verify; milliseconds, median (min–max)",
        cfg!(feature = "hw-sha2"),
        cfg!(feature = "hw-sha512")
    );
    println!("| set | operation | this crate | RustCrypto | RustCrypto / this crate |");
    println!("|---|---|---|---|---|");
    time_set!(Sha2_128s, 16, reps, vreps);
    time_set!(Sha2_128f, 16, reps, vreps);
    time_set!(Sha2_192s, 24, reps, vreps);
    time_set!(Sha2_192f, 24, reps, vreps);
    time_set!(Sha2_256s, 32, reps, vreps);
    time_set!(Sha2_256f, 32, reps, vreps);
}
