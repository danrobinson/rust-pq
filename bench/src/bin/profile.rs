//! Coarse breakdown of where the verified crate's SLH-DSA-SHA2-128s signing time goes, using
//! its public sub-functions (it is not modified). Also usable as a target for
//! a sampling profiler:  `profile loop` signs forever.
use slhdsa::address::{Adrs, FORS_TREE};
use slhdsa::params::SHA2_128S as P;
use slhdsa::sha2_128s as v;
use std::hint::black_box;
use std::time::Instant;

fn per_call<F: FnMut()>(n: u32, mut f: F) -> f64 {
    for _ in 0..n / 10 {
        f();
    }
    let mut best = f64::MAX;
    for _ in 0..5 {
        let t = Instant::now();
        for _ in 0..n {
            f();
        }
        best = best.min(t.elapsed().as_nanos() as f64 / n as f64);
    }
    best
}

fn main() {
    let (sk, _pk) = v::slh_keygen_internal(&[0x11; 16], &[0x22; 16], &[0x33; 16]);
    let pk_seed: [u8; 16] = sk[32..48].try_into().unwrap();
    let sk_seed: [u8; 16] = sk[0..16].try_into().unwrap();
    let m = [7u8; 32];
    // Internal functions take the precomputed seed context.
    let seed = slhdsa::hash::seed_ctx::<16>(&pk_seed);
    if std::env::args().nth(1).as_deref() == Some("loop") {
        loop {
            black_box(v::slh_sign(&m, &[], &sk, &pk_seed));
        }
    }
    let sign = per_call(3, || {
        black_box(v::slh_sign(black_box(&m), &[], &sk, &pk_seed));
    });
    let adrs = Adrs::new().with_tree(5).with_type(FORS_TREE).with_keypair(3);
    let md = [0x5au8; 21];
    let fors = per_call(3, || {
        black_box(slhdsa::fors::fors_sign::<16>(&P, black_box(&md), &sk_seed, &seed, adrs));
    });
    let ht = per_call(3, || {
        black_box(slhdsa::ht::ht_sign::<16>(&P, black_box(&[1u8; 16]), &sk_seed, &seed, 12345, 77));
    });
    let wots_pk = per_call(200, || {
        black_box(slhdsa::wots::wots_pk_gen::<16>(&sk_seed, black_box(&seed), Adrs::new()));
    });
    let thash_f = per_call(1_000_000, || {
        black_box(slhdsa::hash::thash_short::<16>(&seed, black_box(&adrs), black_box(&[3u8; 16])));
    });
    let thash_h = per_call(1_000_000, || {
        black_box(slhdsa::hash::thash_short::<16>(&seed, black_box(&adrs), black_box(&[3u8; 32])));
    });
    let sha_102 = per_call(1_000_000, || {
        black_box(slhdsa::sha256::sha256(black_box(&[1u8; 102])));
    });
    let sha_32 = per_call(1_000_000, || {
        black_box(slhdsa::sha256::sha256(black_box(&[1u8; 32])));
    });
    let sha_64k = per_call(2_000, || {
        black_box(slhdsa::sha256::sha256(black_box(&[1u8; 65536 - 9])));
    });
    let compress = sha_64k / 1024.0; // 1024 blocks: per-block cost with padding overhead amortised
    println!("verified crate, best-of-5 per-call times (ns)");
    println!("slh_sign (32 B msg)          {:>14.0}", sign);
    println!("  fors_sign                  {:>14.0}  ({:.1}% of sign)", fors, 100.0 * fors / sign);
    println!("  ht_sign                    {:>14.0}  ({:.1}% of sign)", ht, 100.0 * ht / sign);
    println!("wots_pk_gen (one XMSS leaf)  {:>14.0}", wots_pk);
    println!("thash_short F (16 B, 1 block) {:>13.1}", thash_f);
    println!("thash_short H (32 B, 1 block) {:>13.1}", thash_h);
    println!("sha256(102 B) (2 blocks)     {:>14.1}", sha_102);
    println!("sha256(32 B)  (1 block)      {:>14.1}", sha_32);
    println!("compression, amortised       {:>14.1}  (sha256 of 64 KiB / 1024)", compress);
    println!();
    println!("thash_short F: 1 compression = {:.0} ns ({:.0}%), everything else (stack block, address serialisation) = {:.0} ns ({:.0}%)",
        compress, 100.0 * compress / thash_f, thash_f - compress, 100.0 * (thash_f - compress) / thash_f);
    println!("sign: 2,218,488 compressions x {:.1} ns = {:.0} ms of {:.0} ms ({:.0}%)",
        compress, 2218488.0 * compress / 1e6, sign / 1e6, 100.0 * 2218488.0 * compress / sign);
}
