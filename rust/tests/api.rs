//! The main interface (`slhdsa::api`) and the checked signer beneath it.

use slhdsa::address::{Adrs, FORS_TREE};
use slhdsa::fors::{fors_pk_from_sig, fors_pk_gen, fors_sign};
use slhdsa::hash::seed_ctx;
use slhdsa::ht::{ht_sign, ht_sign_checked};
use slhdsa::params::{HP, N};
use slhdsa::xmss::xmss_node;
use slhdsa::{
    keygen, public_key, sign, sign_checked, sign_deterministic, sign_deterministic_checked, slh_keygen_internal,
    slh_sign, slh_sign_checked, slh_sign_internal, slh_sign_internal_checked, slh_verify, slh_verify_internal, verify,
};

/// SplitMix64: a fixed stream, so the cases are the same on every run.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn bytes<const L: usize>(&mut self) -> [u8; L] {
        let mut out = [0u8; L];
        for b in out.iter_mut() {
            *b = self.next() as u8;
        }
        out
    }

    fn vec(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }
}

fn key(rng: &mut Rng) -> ([u8; 64], [u8; 32]) {
    let seeds: [u8; 48] = rng.bytes();
    let mut sk = [0u8; 64];
    let mut pk = [0u8; 32];
    keygen(&seeds, &mut sk, &mut pk);
    (sk, pk)
}

#[test]
fn keygen_is_the_internal_function_on_the_three_seeds() {
    let mut rng = Rng(1);
    for _ in 0..3 {
        let seeds: [u8; 48] = rng.bytes();
        let mut sk = [0u8; 64];
        let mut pk = [0u8; 32];
        keygen(&seeds, &mut sk, &mut pk);
        let (sk2, pk2) = slh_keygen_internal(
            seeds[0..16].try_into().unwrap(),
            seeds[16..32].try_into().unwrap(),
            seeds[32..48].try_into().unwrap(),
        );
        assert_eq!(sk, sk2);
        assert_eq!(pk, pk2);
        assert_eq!(public_key(&sk), pk);
        assert_eq!(&sk[0..48], &seeds[..]);
    }
}

#[test]
fn checked_signing_returns_the_standard_signature() {
    let mut rng = Rng(2);
    for round in 0..6 {
        let (sk, pk) = key(&mut rng);
        let m = rng.vec([0, 1, 16, 33, 200, 5000][round]);
        let ctx = rng.vec([0, 1, 7, 100, 255, 3][round]);
        let addrnd: [u8; 16] = rng.bytes();

        let plain = slh_sign(&m, &ctx, &sk, &addrnd).unwrap();
        assert_eq!(sign(&m, &ctx, &sk, &addrnd).as_ref(), Some(&plain));
        assert_eq!(sign_checked(&m, &ctx, &sk, &addrnd).as_ref(), Some(&plain));
        assert_eq!(slh_sign_checked(&m, &ctx, &sk, &addrnd).as_ref(), Some(&plain));
        assert!(verify(&m, &plain, &ctx, &pk));
        assert!(slh_verify(&m, &plain, &ctx, &pk));

        let pk_seed: [u8; 16] = sk[32..48].try_into().unwrap();
        let det = slh_sign(&m, &ctx, &sk, &pk_seed).unwrap();
        assert_eq!(sign_deterministic(&m, &ctx, &sk).as_ref(), Some(&det));
        assert_eq!(sign_deterministic_checked(&m, &ctx, &sk).as_ref(), Some(&det));
        assert!(verify(&m, &det, &ctx, &pk));
        assert_ne!(det, plain);

        let internal = slh_sign_internal(&m, &sk, &addrnd);
        assert_eq!(slh_sign_internal_checked(&m, &sk, &addrnd).as_ref(), Some(&internal));
        assert!(slh_verify_internal(&m, &internal, &pk));
    }
}

#[test]
fn context_longer_than_255_bytes_is_refused() {
    let mut rng = Rng(3);
    let (sk, _) = key(&mut rng);
    assert!(sign(b"m", &[0u8; 256], &sk, &[0u8; 16]).is_none());
    assert!(sign_deterministic(b"m", &[0u8; 256], &sk).is_none());
    assert!(sign_checked(b"m", &[0u8; 256], &sk, &[0u8; 16]).is_none());
    assert!(sign_deterministic_checked(b"m", &[0u8; 256], &sk).is_none());
    assert!(sign(b"m", &[0u8; 255], &sk, &[0u8; 16]).is_some());
    assert!(sign_checked(b"m", &[0u8; 255], &sk, &[0u8; 16]).is_some());
}

/// A private key that key generation would not produce: any change to
/// `SK.seed`, `PK.seed` or `PK.root` makes the recomputed top root differ
/// from the stored one. (`SK.prf` only chooses the randomizer.)
#[test]
fn a_damaged_key_gives_no_signature() {
    let mut rng = Rng(4);
    let (sk, pk) = key(&mut rng);
    let addrnd: [u8; 16] = rng.bytes();
    for at in [0usize, 15, 32, 47, 48, 63] {
        let mut bad = sk;
        bad[at] ^= 0x10;
        assert!(sign_checked(b"message", b"", &bad, &addrnd).is_none(), "byte {at}");
        assert!(sign_deterministic_checked(b"message", b"", &bad).is_none(), "byte {at}");
        assert!(slh_sign_internal_checked(b"message", &bad, &addrnd).is_none(), "byte {at}");
        // The plain signer releases a signature for such a key; it does not verify.
        let sig = sign(b"message", b"", &bad, &addrnd).unwrap();
        assert!(!slh_verify(b"message", &sig, b"", &pk));
    }
    let mut prf_changed = sk;
    prf_changed[20] ^= 0x10;
    let sig = sign_checked(b"message", b"", &prf_changed, &addrnd).unwrap();
    assert!(verify(b"message", &sig, b"", &pk));
}

/// The fault the check exists for, acted out on the hypertree signer: the
/// value one route hands up is wrong. The signature that the unchecked
/// signer makes from it still verifies (that is the danger); the checked one
/// reports the disagreement.
#[test]
fn a_wrong_value_from_one_route_is_caught() {
    let mut rng = Rng(5);
    let (sk, _) = key(&mut rng);
    let sk_seed: [u8; N] = sk[0..16].try_into().unwrap();
    let pk_seed: [u8; N] = sk[32..48].try_into().unwrap();
    let pk_root: [u8; N] = sk[48..64].try_into().unwrap();
    let seed = seed_ctx(&pk_seed);
    let (idx_tree, idx_leaf) = (0x2f_1234_5678_9abcu64 & ((1 << 54) - 1), 300u32);
    let adrs = Adrs::new().with_tree(idx_tree).with_type(FORS_TREE).with_keypair(idx_leaf);
    let md: [u8; 21] = rng.bytes();

    let sig_fors = fors_sign(&md, &sk_seed, &seed, adrs);
    let honest = fors_pk_from_sig(&sig_fors, &md, &seed, adrs);
    assert_eq!(fors_pk_gen(&sk_seed, &seed, adrs), honest);

    // No fault: the checked signer agrees with the unchecked one.
    let (sig, ok) = ht_sign_checked(&honest, &honest, &sk_seed, &seed, idx_tree, idx_leaf, &pk_root);
    assert!(ok);
    assert_eq!(sig, ht_sign(&honest, &sk_seed, &seed, idx_tree, idx_leaf));

    // The top tree's root, recomputed from the seed, is PK.root.
    let top = Adrs::new().with_layer(6).with_tree(0);
    assert_eq!(xmss_node(&sk_seed, 0, HP, &seed, top), pk_root);

    // A wrong FORS public key from either route.
    let mut wrong = honest;
    wrong[3] ^= 1;
    assert!(!ht_sign_checked(&wrong, &honest, &sk_seed, &seed, idx_tree, idx_leaf, &pk_root).1);
    assert!(!ht_sign_checked(&honest, &wrong, &sk_seed, &seed, idx_tree, idx_leaf, &pk_root).1);
    // The same wrong value from both routes passes every pairwise check: a
    // signature on it is a valid signature of that value. That is why the
    // two routes must share no work.
    assert!(ht_sign_checked(&wrong, &wrong, &sk_seed, &seed, idx_tree, idx_leaf, &pk_root).1);
    // A wrong top root.
    let mut other_root = pk_root;
    other_root[0] ^= 1;
    assert!(!ht_sign_checked(&honest, &honest, &sk_seed, &seed, idx_tree, idx_leaf, &other_root).1);
}

/// Wall-clock cost of the check, printed with `--nocapture`.
#[test]
fn cost_of_the_check() {
    let mut rng = Rng(6);
    let (sk, _) = key(&mut rng);
    let addrnd: [u8; 16] = rng.bytes();
    let rounds = 8;
    let t = std::time::Instant::now();
    for i in 0..rounds {
        std::hint::black_box(sign(&[i as u8], b"", &sk, &addrnd));
    }
    let plain = t.elapsed().as_secs_f64() / rounds as f64;
    let t = std::time::Instant::now();
    for i in 0..rounds {
        std::hint::black_box(sign_checked(&[i as u8], b"", &sk, &addrnd));
    }
    let checked = t.elapsed().as_secs_f64() / rounds as f64;
    println!(
        "sign {:.2} ms, sign_checked {:.2} ms, ratio {:.2}",
        plain * 1e3,
        checked * 1e3,
        checked / plain
    );
}
