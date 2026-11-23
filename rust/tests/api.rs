//! The main interface (`sha2_*::api`) and the functions beneath it, for all
//! six parameter sets. Ported from the single-set crate's `tests/api.rs` (git commit 26aa3d8).

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

macro_rules! api_tests {
    ($($name:ident, $m:ident, $seed:expr;)*) => {$(
        mod $name {
            use super::Rng;
            use slhdsa::address::Adrs;
            use slhdsa::hash::seed_ctx;
            use slhdsa::xmss::xmss_node;
            use slhdsa::$m as s;
            use s::params::{N, PARAMS, PK_BYTES, SEED_BYTES, SK_BYTES};
            use s::{
                keygen, public_key, sign, sign_deterministic, slh_keygen_internal, slh_sign, slh_sign_internal,
                slh_verify, slh_verify_internal, verify,
            };

            fn key(rng: &mut Rng) -> ([u8; SK_BYTES], [u8; PK_BYTES]) {
                let seeds: [u8; SEED_BYTES] = rng.bytes();
                let mut sk = [0u8; SK_BYTES];
                let mut pk = [0u8; PK_BYTES];
                keygen(&seeds, &mut sk, &mut pk);
                (sk, pk)
            }

            #[test]
            fn keygen_is_the_internal_function_on_the_three_seeds() {
                let mut rng = Rng($seed + 1);
                for _ in 0..2 {
                    let seeds: [u8; SEED_BYTES] = rng.bytes();
                    let mut sk = [0u8; SK_BYTES];
                    let mut pk = [0u8; PK_BYTES];
                    keygen(&seeds, &mut sk, &mut pk);
                    let (sk2, pk2) = slh_keygen_internal(
                        seeds[0..N].try_into().unwrap(),
                        seeds[N..2 * N].try_into().unwrap(),
                        seeds[2 * N..3 * N].try_into().unwrap(),
                    );
                    assert_eq!(sk, sk2);
                    assert_eq!(pk, pk2);
                    assert_eq!(public_key(&sk), pk);
                    assert_eq!(&sk[0..3 * N], &seeds[..]);
                }
            }

            #[test]
            fn the_interface_signers_return_the_standard_signature() {
                let mut rng = Rng($seed + 2);
                for round in 0..3 {
                    let (sk, pk) = key(&mut rng);
                    let m = rng.vec([0, 33, 5000][round]);
                    let ctx = rng.vec([0, 7, 255][round]);
                    let addrnd: [u8; N] = rng.bytes();

                    let plain = slh_sign(&m, &ctx, &sk, &addrnd).unwrap();
                    assert_eq!(sign(&m, &ctx, &sk, &addrnd).as_ref(), Some(&plain));
                    assert!(verify(&m, &plain, &ctx, &pk));
                    assert!(slh_verify(&m, &plain, &ctx, &pk));

                    let pk_seed: [u8; N] = sk[2 * N..3 * N].try_into().unwrap();
                    let det = slh_sign(&m, &ctx, &sk, &pk_seed).unwrap();
                    assert_eq!(sign_deterministic(&m, &ctx, &sk).as_ref(), Some(&det));
                    assert!(verify(&m, &det, &ctx, &pk));
                    assert_ne!(det, plain);

                    let internal = slh_sign_internal(&m, &sk, &addrnd);
                    assert!(slh_verify_internal(&m, &internal, &pk));
                }
            }

            #[test]
            fn context_longer_than_255_bytes_is_refused() {
                let mut rng = Rng($seed + 3);
                let (sk, _) = key(&mut rng);
                assert!(sign(b"m", &[0u8; 256], &sk, &[0u8; N]).is_none());
                assert!(sign_deterministic(b"m", &[0u8; 256], &sk).is_none());
                assert!(sign(b"m", &[0u8; 255], &sk, &[0u8; N]).is_some());
            }

            /// A private key that key generation would not produce: any change to
            /// `SK.seed`, `PK.seed` or `PK.root`. The signer still returns a
            /// signature (FIPS 205 does not check the key); it does not verify under
            /// the original public key. A changed `SK.prf` only chooses another
            /// randomizer, and the signature still verifies.
            #[test]
            fn a_damaged_key_gives_a_signature_that_does_not_verify() {
                let mut rng = Rng($seed + 4);
                let (sk, pk) = key(&mut rng);
                let addrnd: [u8; N] = rng.bytes();
                for at in [0usize, N - 1, 2 * N, 3 * N - 1, 3 * N, 4 * N - 1] {
                    let mut bad = sk;
                    bad[at] ^= 0x10;
                    let sig = sign(b"message", b"", &bad, &addrnd).unwrap();
                    assert!(!slh_verify(b"message", &sig, b"", &pk), "byte {at}");
                }
                let mut prf_changed = sk;
                prf_changed[N + 4] ^= 0x10;
                let sig = sign(b"message", b"", &prf_changed, &addrnd).unwrap();
                assert!(verify(b"message", &sig, b"", &pk));
            }

            /// The top tree's root, recomputed from the seed, is the `PK.root` that
            /// key generation stored.
            #[test]
            fn the_top_root_is_pk_root() {
                let p = &PARAMS;
                let mut rng = Rng($seed + 5);
                let (sk, _) = key(&mut rng);
                let sk_seed: [u8; N] = sk[0..N].try_into().unwrap();
                let pk_seed: [u8; N] = sk[2 * N..3 * N].try_into().unwrap();
                let pk_root: [u8; N] = sk[3 * N..4 * N].try_into().unwrap();
                let seed = seed_ctx::<N>(&pk_seed);
                let top = Adrs::new().with_layer(p.d - 1).with_tree(0);
                assert_eq!(xmss_node::<N>(&sk_seed, 0, p.hp, &seed, top), pk_root);
            }
        }
    )*};
}

api_tests! {
    api_128s, sha2_128s, 0x100;
    api_128f, sha2_128f, 0x200;
    api_192s, sha2_192s, 0x300;
    api_192f, sha2_192f, 0x400;
    api_256s, sha2_256s, 0x500;
    api_256f, sha2_256f, 0x600;
}
