//! SHA-256 compression-function calls per keygen / sign / verify, for the
//! unmodified copy of the verified crate (base) and variants A, B, C.
use std::sync::atomic::Ordering::Relaxed;

macro_rules! measure {
    ($k:ident, $mlen:expr) => {{
        let c = &$k::sha256::COMPRESSIONS;
        let m: Vec<u8> = (0..$mlen).map(|i| i as u8).collect();
        c.store(0, Relaxed);
        let (sk, pk) = $k::slh_keygen_internal(&[0x11; 16], &[0x22; 16], &[0x33; 16]);
        let kg = c.load(Relaxed);
        let rnd: [u8; 16] = sk[32..48].try_into().unwrap();
        c.store(0, Relaxed);
        let sig = $k::slh_sign(&m, &[], &sk, &rnd).unwrap();
        let sg = c.load(Relaxed);
        c.store(0, Relaxed);
        assert!($k::slh_verify(&m, &sig, &[], &pk));
        let vf = c.load(Relaxed);
        (kg, sg, vf, sig)
    }};
}

fn main() {
    println!("| copy | msg bytes | keygen | sign | verify |");
    println!("|---|---|---|---|---|");
    for mlen in [32usize, 1024, 1 << 20] {
        let b = measure!(slhdsa_base, mlen);
        let a = measure!(slhdsa_a, mlen);
        let bb = measure!(slhdsa_b, mlen);
        let c = measure!(slhdsa_c, mlen);
        let cur = measure!(slhdsa_current, mlen);
        let d = measure!(slhdsa_d, mlen);
        assert!(a.3 == b.3 && bb.3 == b.3 && c.3 == b.3 && cur.3 == b.3 && d.3 == b.3, "variant signatures differ");
        for (n, r) in [("base (= verified-before)", &b), ("verified (current rust/)", &cur), ("A", &a), ("B", &bb), ("C", &c), ("D", &d)] {
            println!("| {n} | {mlen} | {} | {} | {} |", r.0, r.1, r.2);
        }
    }
}
