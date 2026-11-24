//! Verification tests for hypertree top-tree caching (`cache`) and HashSLH-DSA (`prehash`).
#![cfg(feature = "platform-sha2")]

use sha2::Digest as _;
use sha3::digest::{ExtendableOutput as _, Update as _};
use slhdsa::cache::{self, HashFamily, TopTreeCache};
use slhdsa::prehash::{self, PreHash};
use upstream::signature::Keypair;

/// Deterministic SplitMix64 PRNG for reproducible tests.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }
}

fn ref_prehash(ph: PreHash, msg: &[u8]) -> Vec<u8> {
    match ph {
        PreHash::Sha256 => sha2::Sha256::digest(msg).to_vec(),
        PreHash::Sha512 => sha2::Sha512::digest(msg).to_vec(),
        PreHash::Shake128 => {
            let mut out = vec![0u8; 32];
            sha3::Shake128::default()
                .chain(msg)
                .finalize_xof_into(&mut out);
            out
        }
        PreHash::Shake256 => {
            let mut out = vec![0u8; 64];
            sha3::Shake256::default()
                .chain(msg)
                .finalize_xof_into(&mut out);
            out
        }
    }
}

// ============================================================================
// 1. SHAKE128 & PreHash primitive tests
// ============================================================================

#[test]
fn shake128_matches_sha3_at_all_rate_boundaries() {
    let mut rng = Rng(0x51a3_1280);
    let data = rng.bytes(10_000);

    // Every length 0..=350 crosses 0, 1, and 2 SHAKE128 rate blocks (168 B).
    for len in (0..=350).chain([512, 1024, 4096, 10_000]) {
        let mut expected = [0u8; 32];
        sha3::Shake128::default()
            .chain(&data[..len])
            .finalize_xof_into(&mut expected);
        let mut actual = [0u8; 32];
        prehash::shake128(&data[..len], &mut actual);
        assert_eq!(actual, expected, "SHAKE128 32B mismatch at input len {len}");
    }

    // Multi-block squeezing across rate boundary 168 B.
    for out_len in [0, 1, 16, 32, 64, 167, 168, 169, 336, 512] {
        let mut expected = vec![0u8; out_len];
        sha3::Shake128::default()
            .chain(&data[..400])
            .finalize_xof_into(&mut expected);
        let mut actual = vec![0u8; out_len];
        prehash::shake128(&data[..400], &mut actual);
        assert_eq!(actual, expected, "SHAKE128 squeeze mismatch at out_len {out_len}");
    }
}

#[test]
fn prehash_oids_and_digests_match_fips205() {
    assert_eq!(
        PreHash::Sha256.oid_der(),
        &[0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01]
    );
    assert_eq!(
        PreHash::Sha512.oid_der(),
        &[0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03]
    );
    assert_eq!(
        PreHash::Shake128.oid_der(),
        &[0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0b]
    );
    assert_eq!(
        PreHash::Shake256.oid_der(),
        &[0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x0c]
    );

    let mut rng = Rng(0x2050_cafe);
    for len in [0, 1, 55, 64, 128, 168, 1024, 4097] {
        let msg = rng.bytes(len);
        for ph in [PreHash::Sha256, PreHash::Sha512, PreHash::Shake128, PreHash::Shake256] {
            let got = ph.hash(&msg);
            let want = ref_prehash(ph, &msg);
            assert_eq!(got.len(), ph.digest_len());
            assert_eq!(got, want, "PreHash::{ph:?} mismatch at len {len}");
        }
    }
}

// ============================================================================
// 2. Per-set byte-for-byte TopTreeCache & HashSLH-DSA tests for all 12 sets
// ============================================================================

macro_rules! test_all_twelve {
    ($($mod_name:ident, $set:ident, $up:ident, $family:expr, $seed:expr, $precompute_d2:expr;)*) => {$(
        mod $mod_name {
            use super::*;
            use slhdsa::$set as base;
            use slhdsa::$set::params::{N, PARAMS, PK_BYTES, SEED_BYTES, SIG_BYTES, SK_BYTES};
            use slhdsa::cache::$set as c;
            use slhdsa::prehash::$set as ph;
            type Up = upstream::$up;

            #[test]
            fn top_tree_cache_matches_uncached_byte_for_byte() {
                let mut rng = Rng($seed);
                let seeds: [u8; SEED_BYTES] = rng.bytes(SEED_BYTES).try_into().unwrap();

                // 1. keygen_with_cache produces byte-identical (sk, pk) to api::keygen
                let mut sk_ref = [0u8; SK_BYTES];
                let mut pk_ref = [0u8; PK_BYTES];
                base::api::keygen(&seeds, &mut sk_ref, &mut pk_ref);

                let mut sk = [0u8; SK_BYTES];
                let mut pk = [0u8; PK_BYTES];
                let cache = c::keygen_with_cache(&seeds, &mut sk, &mut pk);
                assert_eq!(sk, sk_ref);
                assert_eq!(pk, pk_ref);
                assert_eq!(cache.family(), $family);
                assert_eq!(cache.pk_seed(), &pk[..N]);
                assert_eq!(cache.pk_root(), &pk[N..]);
                assert!(cache.matches_key(&sk));

                // 2. TopTreeCache::new matches keygen_with_cache identically
                let cache2 = c::new(&sk);
                assert_eq!(cache, cache2);
                let expected_nodes = (1usize << (PARAMS.hp + 1)) - 1;
                assert_eq!(cache.top_tree_nodes(), expected_nodes);
                assert_eq!(cache.memory_bytes(), expected_nodes * N);
                assert_eq!(cache.layer_d2_cached_trees(), 0);

                // 3. Cached pure hedged & deterministic signing (short + long >= 1024 B + max ctx)
                for (msg_len, ctx_len) in [(0usize, 0usize), (37, 11), (1025, 255)] {
                    let msg = rng.bytes(msg_len);
                    let ctx = rng.bytes(ctx_len);
                    let rand: [u8; N] = rng.bytes(N).try_into().unwrap();

                    let sig_uncached = base::api::sign(&msg, &ctx, &sk, &rand).unwrap();
                    let sig_cached = c::sign_cached(&msg, &ctx, &sk, &rand, &cache).unwrap();
                    assert_eq!(sig_cached.len(), SIG_BYTES);
                    assert_eq!(sig_cached, sig_uncached, "hedged cached != uncached");
                    assert!(base::api::verify(&msg, &sig_cached, &ctx, &pk));

                    let det_uncached = base::api::sign_deterministic(&msg, &ctx, &sk).unwrap();
                    let det_cached = c::sign_deterministic_cached(&msg, &ctx, &sk, &cache).unwrap();
                    assert_eq!(det_cached, det_uncached, "det cached != uncached");
                    assert!(base::api::verify(&msg, &det_cached, &ctx, &pk));

                    // Internal cached signing
                    let int_uncached = base::slh_sign_internal(&msg, &sk, &rand);
                    let int_cached = c::sign_internal_cached(&msg, &sk, &rand, &cache);
                    assert_eq!(int_cached, int_uncached, "internal cached != uncached");
                }

                // 4. Context > 255 rejected
                let too_long_ctx = vec![0x42u8; 256];
                let rand: [u8; N] = [7u8; N];
                assert!(c::sign_cached(b"msg", &too_long_ctx, &sk, &rand, &cache).is_none());
                assert!(c::sign_deterministic_cached(b"msg", &too_long_ctx, &sk, &cache).is_none());

                // 5. Optional layer d - 2 caching (precomputed for -f sets, dynamic MRU for all sets)
                if $precompute_d2 {
                    let mut d2_cache = cache.clone();
                    c::precompute_layer_d2(&mut d2_cache, &sk);
                    assert_eq!(d2_cache.layer_d2_cached_trees(), 1usize << PARAMS.hp);
                    for i in 0..3u8 {
                        let m = [i; 48];
                        let sig_ref = base::api::sign_deterministic(&m, b"d2-pre", &sk).unwrap();
                        let sig_d2 =
                            c::sign_deterministic_cached(&m, b"d2-pre", &sk, &d2_cache).unwrap();
                        assert_eq!(sig_d2, sig_ref, "precomputed layer d-2 mismatch");
                    }
                }

                // Dynamic MRU layer d - 2 cache (miss -> populate -> hit -> eviction)
                let mut mru_cache = cache.clone().with_layer_d2_capacity(2);
                let msgs = [b"alpha".as_slice(), b"beta", b"alpha", b"gamma", b"delta"];
                for m in msgs {
                    let sig_ref = base::api::sign_deterministic(m, b"mru", &sk).unwrap();
                    let sig_mru =
                        c::sign_deterministic_cached_mut(m, b"mru", &sk, &mut mru_cache).unwrap();
                    assert_eq!(sig_mru, sig_ref, "MRU layer d-2 mismatch");
                    assert!(mru_cache.layer_d2_cached_trees() <= 2);
                }
                assert!(mru_cache.layer_d2_cached_trees() >= 1);
            }

            #[test]
            fn hash_slh_dsa_matches_upstream_and_prehashed_and_cached() {
                let mut rng = Rng($seed + 0x1000);
                let seeds: [u8; SEED_BYTES] = rng.bytes(SEED_BYTES).try_into().unwrap();
                let mut sk = [0u8; SK_BYTES];
                let mut pk = [0u8; PK_BYTES];
                let cache = c::keygen_with_cache(&seeds, &mut sk, &mut pk);

                let up_sk = upstream::SigningKey::<Up>::slh_keygen_internal(
                    &seeds[..N],
                    &seeds[N..2 * N],
                    &seeds[2 * N..],
                );
                let up_vk = up_sk.verifying_key();
                assert_eq!(&sk[..], &up_sk.to_bytes()[..]);
                assert_eq!(&pk[..], &up_vk.to_bytes()[..]);

                let msg = rng.bytes(2049);
                let ctx = rng.bytes(19);
                let rand: [u8; N] = rng.bytes(N).try_into().unwrap();

                for mode in [PreHash::Sha256, PreHash::Sha512, PreHash::Shake128, PreHash::Shake256] {
                    let digest = ref_prehash(mode, &msg);
                    let domain = [1u8, ctx.len() as u8];
                    let oid = mode.oid_der();

                    // Independent RustCrypto upstream FIPS 205 Alg 23 framing
                    let up_sig = up_sk
                        .slh_sign_internal(&[&domain, &ctx, oid, &digest], Some(&rand))
                        .to_bytes();
                    let up_det = up_sk
                        .slh_sign_internal(&[&domain, &ctx, oid, &digest], None)
                        .to_bytes();

                    // Our HashSLH-DSA hedged & deterministic
                    let sig = ph::hash_slh_sign(&msg, &ctx, mode, &sk, &rand).unwrap();
                    let sig_det = ph::hash_slh_sign_deterministic(&msg, &ctx, mode, &sk).unwrap();
                    assert_eq!(&sig[..], &up_sig[..], "hash_slh_sign != upstream ({mode:?})");
                    assert_eq!(&sig_det[..], &up_det[..], "hash_slh_sign_det != upstream ({mode:?})");

                    // Pre-hashed streaming entry points
                    let sig_pre = ph::hash_slh_sign_prehashed(&digest, &ctx, mode, &sk, &rand).unwrap();
                    let sig_pre_det =
                        ph::hash_slh_sign_prehashed_deterministic(&digest, &ctx, mode, &sk).unwrap();
                    assert_eq!(sig_pre, sig);
                    assert_eq!(sig_pre_det, sig_det);

                    // Cached HashSLH-DSA entry points
                    let sig_cached =
                        ph::hash_slh_sign_cached(&msg, &ctx, mode, &sk, &rand, &cache).unwrap();
                    let sig_det_cached =
                        ph::hash_slh_sign_deterministic_cached(&msg, &ctx, mode, &sk, &cache)
                            .unwrap();
                    let sig_pre_cached = ph::hash_slh_sign_prehashed_cached(
                        &digest, &ctx, mode, &sk, &rand, &cache,
                    )
                    .unwrap();
                    let sig_pre_det_cached = ph::hash_slh_sign_prehashed_deterministic_cached(
                        &digest, &ctx, mode, &sk, &cache,
                    )
                    .unwrap();
                    assert_eq!(sig_cached, sig);
                    assert_eq!(sig_det_cached, sig_det);
                    assert_eq!(sig_pre_cached, sig);
                    assert_eq!(sig_pre_det_cached, sig_det);

                    // Verification: both ours and upstream accept
                    assert!(ph::hash_slh_verify(&msg, &sig, &ctx, mode, &pk));
                    assert!(ph::hash_slh_verify(&msg, &sig_det, &ctx, mode, &pk));
                    assert!(ph::hash_slh_verify_prehashed(&digest, &sig, &ctx, mode, &pk));
                    assert!(up_vk
                        .slh_verify_internal(
                            &[&domain, &ctx, oid, &digest],
                            &upstream::Signature::<Up>::try_from(&sig[..]).unwrap(),
                        )
                        .is_ok());

                    // Domain separation: pure verify MUST reject HashSLH-DSA signature!
                    assert!(!base::api::verify(&msg, &sig, &ctx, &pk));

                    // Wrong pre-hash mode MUST fail verification!
                    let other_mode = match mode {
                        PreHash::Sha256 => PreHash::Shake128,
                        PreHash::Shake128 => PreHash::Sha256,
                        PreHash::Sha512 => PreHash::Shake256,
                        PreHash::Shake256 => PreHash::Sha512,
                    };
                    assert!(!ph::hash_slh_verify(&msg, &sig, &ctx, other_mode, &pk));

                    // Tampered message / context / signature MUST fail verification!
                    let mut bad_msg = msg.clone();
                    bad_msg[0] ^= 1;
                    assert!(!ph::hash_slh_verify(&bad_msg, &sig, &ctx, mode, &pk));
                    assert!(!ph::hash_slh_verify(&msg, &sig, b"wrong-ctx", mode, &pk));
                    let mut bad_sig = sig.clone();
                    bad_sig[SIG_BYTES / 2] ^= 0x80;
                    assert!(!ph::hash_slh_verify(&msg, &bad_sig, &ctx, mode, &pk));
                }

                // Pure signature MUST be rejected by HashSLH-DSA verify!
                let pure_sig = base::api::sign_deterministic(&msg, &ctx, &sk).unwrap();
                assert!(!ph::hash_slh_verify(&msg, &pure_sig, &ctx, PreHash::Sha256, &pk));

                // Context > 255 and wrong digest length rejected
                let bad_ctx = vec![0u8; 256];
                assert!(ph::hash_slh_sign(&msg, &bad_ctx, PreHash::Sha256, &sk, &rand).is_none());
                assert!(!ph::hash_slh_verify(&msg, &pure_sig, &bad_ctx, PreHash::Sha256, &pk));
                let bad_digest = vec![0u8; 31];
                assert!(
                    ph::hash_slh_sign_prehashed(&bad_digest, &ctx, PreHash::Sha256, &sk, &rand)
                        .is_none()
                );
                assert!(
                    !ph::hash_slh_verify_prehashed(&bad_digest, &pure_sig, &ctx, PreHash::Sha256, &pk)
                );
                let digest32 = [0u8; 32];
                assert!(
                    ph::hash_slh_sign_prehashed(&digest32, &ctx, PreHash::Sha512, &sk, &rand)
                        .is_none()
                );
                assert!(
                    !ph::hash_slh_verify_prehashed(&digest32, &pure_sig, &ctx, PreHash::Sha512, &pk)
                );
            }
        }
    )*};
}

test_all_twelve! {
    t_sha2_128s,  sha2_128s,  Sha2_128s,  HashFamily::Sha2,  101, false;
    t_sha2_128f,  sha2_128f,  Sha2_128f,  HashFamily::Sha2,  102, true;
    t_sha2_192s,  sha2_192s,  Sha2_192s,  HashFamily::Sha2,  103, false;
    t_sha2_192f,  sha2_192f,  Sha2_192f,  HashFamily::Sha2,  104, true;
    t_sha2_256s,  sha2_256s,  Sha2_256s,  HashFamily::Sha2,  105, false;
    t_sha2_256f,  sha2_256f,  Sha2_256f,  HashFamily::Sha2,  106, true;
    t_shake_128s, shake_128s, Shake128s,  HashFamily::Shake, 201, false;
    t_shake_128f, shake_128f, Shake128f,  HashFamily::Shake, 202, true;
    t_shake_192s, shake_192s, Shake192s,  HashFamily::Shake, 203, false;
    t_shake_192f, shake_192f, Shake192f,  HashFamily::Shake, 204, true;
    t_shake_256s, shake_256s, Shake256s,  HashFamily::Shake, 205, false;
    t_shake_256f, shake_256f, Shake256f,  HashFamily::Shake, 206, true;
}

// ============================================================================
// 3. Key-mismatch safety check & NIST ACVP vector spot-check
// ============================================================================

#[test]
#[should_panic(expected = "does not match")]
fn cache_rejects_mismatched_key() {
    let mut sk1 = [0u8; 64];
    let mut pk1 = [0u8; 32];
    let cache1 = cache::sha2_128f::keygen_with_cache(&[1u8; 48], &mut sk1, &mut pk1);

    let mut sk2 = [0u8; 64];
    let mut pk2 = [0u8; 32];
    slhdsa::sha2_128f::api::keygen(&[2u8; 48], &mut sk2, &mut pk2);

    assert!(!cache1.matches_key(&sk2));
    let _ = cache::sha2_128f::sign_deterministic_cached(b"oops", b"", &sk2, &cache1);
}

#[test]
fn cache_matches_nist_acvp_vectors() {
    let files = [
        ("slh-dsa-sha2-128f.json", HashFamily::Sha2, &slhdsa::sha2_128f::params::PARAMS),
        ("slh-dsa-shake-128f.json", HashFamily::Shake, &slhdsa::shake_128f::params::PARAMS),
        ("slh-dsa-sha2-128s.json", HashFamily::Sha2, &slhdsa::sha2_128s::params::PARAMS),
        ("slh-dsa-shake-128s.json", HashFamily::Shake, &slhdsa::shake_128s::params::PARAMS),
    ];

    for (file, family, params) in files {
        let path = format!("{}/../vectors/{file}", env!("CARGO_MANIFEST_DIR"));
        let raw = std::fs::read_to_string(&path).expect("ACVP vector file present");
        let v: serde_json::Value = serde_json::from_str(&raw).expect("valid JSON");

        // Verify keyGen cases from ACVP groups
        let mut kg_checked = 0;
        for g in v["keyGen"].as_array().unwrap() {
            for tc in g["tests"].as_array().unwrap().iter().take(2) {
                let mut seeds = Vec::new();
                seeds.extend(hex::decode(tc["skSeed"].as_str().unwrap()).unwrap());
                seeds.extend(hex::decode(tc["skPrf"].as_str().unwrap()).unwrap());
                seeds.extend(hex::decode(tc["pkSeed"].as_str().unwrap()).unwrap());
                let want_sk = hex::decode(tc["sk"].as_str().unwrap()).unwrap();
                let want_pk = hex::decode(tc["pk"].as_str().unwrap()).unwrap();
                let mut sk = [0u8; 64];
                let mut pk = [0u8; 32];
                let c = cache::keygen_with_cache::<16>(family, params, &seeds, &mut sk, &mut pk);
                assert_eq!(&sk[..], &want_sk[..], "{file} keyGen sk");
                assert_eq!(&pk[..], &want_pk[..], "{file} keyGen pk");
                assert!(c.matches_key(&sk));
                kg_checked += 1;
            }
        }
        assert!(kg_checked >= 2);

        // Verify sigGen cases across internal + pure, deterministic + hedged groups
        let mut sg_checked = 0;
        for g in v["sigGen"].as_array().unwrap() {
            let det = g["deterministic"].as_bool().unwrap();
            let internal = g["signatureInterface"] == "internal";
            for tc in g["tests"].as_array().unwrap().iter().take(1) {
                let sk = hex::decode(tc["sk"].as_str().unwrap()).unwrap();
                let msg = hex::decode(tc["message"].as_str().unwrap()).unwrap();
                let want_sig = hex::decode(tc["signature"].as_str().unwrap()).unwrap();
                let c = TopTreeCache::<16>::new(family, params, &sk);
                let rand: [u8; 16] = if det {
                    sk[32..48].try_into().unwrap()
                } else {
                    hex::decode(tc["additionalRandomness"].as_str().unwrap())
                        .unwrap()
                        .try_into()
                        .unwrap()
                };
                let got = if internal {
                    c.sign_internal(params, &msg, &sk, &rand)
                } else {
                    let ctx = hex::decode(tc["context"].as_str().unwrap()).unwrap();
                    let s = c.sign(params, &msg, &ctx, &sk, &rand).unwrap();
                    if det {
                        assert_eq!(c.sign_deterministic(params, &msg, &ctx, &sk).unwrap(), s);
                    }
                    s
                };
                assert_eq!(got, want_sig, "{file} sigGen (internal={internal}, det={det})");
                sg_checked += 1;
            }
        }
        assert!(sg_checked >= 2);
    }
}

#[test]
fn typed_signers_reject_a_cache_from_the_other_hash_family() {
    let mut sk = [0; 64];
    let mut pk = [0; 32];
    let cache = cache::shake_128f::keygen_with_cache(&[0; 48], &mut sk, &mut pk);
    assert!(std::panic::catch_unwind(|| {
        cache::sha2_128f::sign_deterministic_cached(b"message", b"", &sk, &cache)
    }).is_err());
    assert!(std::panic::catch_unwind(|| {
        prehash::sha2_128f::hash_slh_sign_deterministic_cached(
            b"message", b"", PreHash::Sha256, &sk, &cache,
        )
    }).is_err());
}
