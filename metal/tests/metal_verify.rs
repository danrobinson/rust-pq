//! Exhaustive byte-for-byte verification of the Metal GPU backend against:
//! 1. NIST ACVP known-answer test vectors (all 6 SHA-2 parameter sets: 10 keyGen + 28 sigGen each).
//! 2. CPU `slhdsa` reference implementation across single, batch, hedged, deterministic, context,
//!    two-phase XMSS, and streaming XMSS execution paths.
//! 3. `slhdsa::*::verify` verification of every GPU-generated signature.

use serde_json::Value;
use slhdsa_metal::MetalSigner;
use std::sync::OnceLock;

fn shared_gpu() -> &'static MetalSigner {
    static GPU: OnceLock<MetalSigner> = OnceLock::new();
    GPU.get_or_init(|| MetalSigner::new().expect("failed to initialize Metal GPU signer"))
}

fn vectors(set: &str) -> Value {
    let path = format!(
        "{}/../vectors/slh-dsa-{}.json",
        env!("CARGO_MANIFEST_DIR"),
        set
    );
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn h(v: &Value) -> Vec<u8> {
    hex::decode(v.as_str().unwrap()).unwrap()
}

fn arr<const L: usize>(v: &Value) -> [u8; L] {
    h(v).try_into().unwrap()
}

#[test]
fn device_sanity() {
    let gpu = shared_gpu();
    let name = gpu.device_name();
    assert!(!name.is_empty(), "Metal device name should not be empty");
    assert!(
        gpu.has_unified_memory(),
        "expected Apple Silicon Unified Memory"
    );
    eprintln!("Metal GPU device: {name} (unified_memory=true)");
}

#[test]
fn batch_64_keygen_and_sign_verify() {
    use slhdsa::sha2_128f as cpu;
    use slhdsa_metal::sha2_128f as gpu_api;

    let gpu = shared_gpu();
    let seeds: Vec<([u8; 16], [u8; 16], [u8; 16])> = (0..64u8)
        .map(|i| ([i; 16], [i.wrapping_add(1); 16], [i.wrapping_add(2); 16]))
        .collect();
    let keys = gpu
        .keygen_internal_batch::<16>(&cpu::params::PARAMS, &seeds)
        .unwrap();
    assert_eq!(keys.len(), 64);

    // Spot-check key 0 and key 63 against CPU reference
    for &idx in &[0usize, 31, 63] {
        let (s0, s1, s2) = seeds[idx];
        let (cpu_sk, cpu_pk) = cpu::slh_keygen_internal(&s0, &s1, &s2);
        assert_eq!(keys[idx].0.as_slice(), &cpu_sk);
        assert_eq!(keys[idx].1.as_slice(), &cpu_pk);
    }

    let sk: [u8; 64] = keys[0].0.as_slice().try_into().unwrap();
    let pk: [u8; 32] = keys[0].1.as_slice().try_into().unwrap();
    let msgs_owned: Vec<Vec<u8>> = (0..64u8).map(|i| vec![i; 48]).collect();
    let msgs: Vec<&[u8]> = msgs_owned.iter().map(|m| m.as_slice()).collect();
    let rnds_owned: Vec<[u8; 16]> = (0..64u8).map(|i| [i.wrapping_mul(17); 16]).collect();
    let rnds: Vec<&[u8; 16]> = rnds_owned.iter().collect();

    let sigs = gpu_api::sign_batch_same_key(gpu, &sk, &msgs, b"batch64", &rnds)
        .unwrap()
        .unwrap();
    assert_eq!(sigs.len(), 64);
    for (i, (m, sig)) in msgs.iter().zip(sigs.iter()).enumerate() {
        assert!(cpu::verify(m, sig, b"batch64", &pk), "batch64 sig {i} failed verify");
    }
    // Check byte-for-byte identity with CPU for first and last signature
    assert_eq!(
        sigs[0],
        cpu::sign(msgs[0], b"batch64", &sk, rnds[0]).unwrap()
    );
    assert_eq!(
        sigs[63],
        cpu::sign(msgs[63], b"batch64", &sk, rnds[63]).unwrap()
    );
}

#[test]
fn shake_batch_64_keygen_and_sign_verify() {
    use slhdsa::shake_128f as cpu;
    use slhdsa_metal::shake_128f as gpu_api;

    let gpu = shared_gpu();
    let seeds: Vec<([u8; 16], [u8; 16], [u8; 16])> = (0..64u8)
        .map(|i| ([i; 16], [i.wrapping_add(3); 16], [i.wrapping_add(7); 16]))
        .collect();
    let keys = gpu
        .shake_keygen_internal_batch::<16>(&cpu::params::PARAMS, &seeds)
        .unwrap();
    assert_eq!(keys.len(), 64);

    for &idx in &[0usize, 31, 63] {
        let (s0, s1, s2) = seeds[idx];
        let (cpu_sk, cpu_pk) = cpu::slh_keygen_internal(&s0, &s1, &s2);
        assert_eq!(keys[idx].0.as_slice(), &cpu_sk);
        assert_eq!(keys[idx].1.as_slice(), &cpu_pk);
    }

    let sk: [u8; 64] = keys[0].0.as_slice().try_into().unwrap();
    let pk: [u8; 32] = keys[0].1.as_slice().try_into().unwrap();
    let msgs_owned: Vec<Vec<u8>> = (0..64u8).map(|i| vec![i; 48]).collect();
    let msgs: Vec<&[u8]> = msgs_owned.iter().map(|m| m.as_slice()).collect();
    let rnds_owned: Vec<[u8; 16]> = (0..64u8).map(|i| [i.wrapping_mul(19); 16]).collect();
    let rnds: Vec<&[u8; 16]> = rnds_owned.iter().collect();

    let sigs = gpu_api::sign_batch_same_key(gpu, &sk, &msgs, b"shake64", &rnds)
        .unwrap()
        .unwrap();
    assert_eq!(sigs.len(), 64);
    for (i, (m, sig)) in msgs.iter().zip(sigs.iter()).enumerate() {
        assert!(cpu::verify(m, sig, b"shake64", &pk), "shake batch64 sig {i} failed verify");
    }
    assert_eq!(
        sigs[0],
        cpu::sign(msgs[0], b"shake64", &sk, rnds[0]).unwrap()
    );
    assert_eq!(
        sigs[63],
        cpu::sign(msgs[63], b"shake64", &sk, rnds[63]).unwrap()
    );
}

macro_rules! verify_set {
    ($mod_name:ident, $set:literal, $cpu:ident, $gpu_mod:ident, $kg_batch:ident, $sg_batch:ident) => {
        mod $mod_name {
            use super::{arr, h, shared_gpu, vectors};
            use slhdsa::$cpu as cpu;
            use slhdsa_metal::$gpu_mod as gpu_api;
            use slhdsa_metal::{MetalSigner, SignInternalReq};
            use cpu::params::{N, PARAMS, PK_BYTES, SEED_BYTES, SIG_BYTES, SK_BYTES};

            #[test]
            fn acvp_keygen_single_and_batch() {
                let gpu = shared_gpu();
                let v = vectors($set);
                let mut batch_inputs = Vec::new();
                let mut expected = Vec::new();

                for g in v["keyGen"].as_array().unwrap() {
                    for t in g["tests"].as_array().unwrap() {
                        let sk_seed: [u8; N] = arr(&t["skSeed"]);
                        let sk_prf: [u8; N] = arr(&t["skPrf"]);
                        let pk_seed: [u8; N] = arr(&t["pkSeed"]);
                        let want_sk = h(&t["sk"]);
                        let want_pk = h(&t["pk"]);

                        // Single GPU keygen_internal
                        let (sk, pk) = gpu_api::keygen_internal(gpu, &sk_seed, &sk_prf, &pk_seed)
                            .expect("GPU keygen_internal failed");
                        assert_eq!(sk.to_vec(), want_sk, "{} tcId {} sk", $set, t["tcId"]);
                        assert_eq!(pk.to_vec(), want_pk, "{} tcId {} pk", $set, t["tcId"]);

                        // Single GPU keygen (concatenated seeds)
                        let mut seeds = [0u8; SEED_BYTES];
                        seeds[..N].copy_from_slice(&sk_seed);
                        seeds[N..2 * N].copy_from_slice(&sk_prf);
                        seeds[2 * N..3 * N].copy_from_slice(&pk_seed);
                        let (mut sk2, mut pk2) = ([0u8; SK_BYTES], [0u8; PK_BYTES]);
                        gpu_api::keygen(gpu, &seeds, &mut sk2, &mut pk2).unwrap();
                        assert_eq!((sk2, pk2), (sk, pk));

                        batch_inputs.push((sk_seed, sk_prf, pk_seed));
                        expected.push((want_sk, want_pk));
                    }
                }
                assert_eq!(batch_inputs.len(), 10);

                // All 10 ACVP keys in ONE single GPU batch dispatch!
                let batch_out = gpu
                    .$kg_batch::<N>(&PARAMS, &batch_inputs)
                    .expect("GPU keygen batch failed");
                assert_eq!(batch_out.len(), 10);
                for (i, ((sk, pk), (want_sk, want_pk))) in
                    batch_out.iter().zip(expected.iter()).enumerate()
                {
                    assert_eq!(sk, want_sk, "{} batch keygen #{i} sk", $set);
                    assert_eq!(pk, want_pk, "{} batch keygen #{i} pk", $set);
                }
            }

            #[test]
            fn acvp_siggen_single_and_batch() {
                let gpu = shared_gpu();
                let v = vectors($set);

                struct Case {
                    tc_id: u64,
                    internal: bool,
                    det: bool,
                    sk: [u8; SK_BYTES],
                    rnd: [u8; N],
                    msg: Vec<u8>,
                    ctx: Vec<u8>,
                    framed: Vec<u8>,
                    want: Vec<u8>,
                }

                let mut cases = Vec::new();
                for g in v["sigGen"].as_array().unwrap() {
                    let det = g["deterministic"].as_bool().unwrap();
                    let internal = g["signatureInterface"] == "internal";
                    for t in g["tests"].as_array().unwrap() {
                        let sk: [u8; SK_BYTES] = arr(&t["sk"]);
                        let rnd: [u8; N] = if det {
                            sk[2 * N..3 * N].try_into().unwrap()
                        } else {
                            arr(&t["additionalRandomness"])
                        };
                        let msg = h(&t["message"]);
                        let ctx = if internal { Vec::new() } else { h(&t["context"]) };
                        let framed = if internal {
                            msg.clone()
                        } else {
                            let mut mp = Vec::with_capacity(2 + ctx.len() + msg.len());
                            mp.push(0);
                            mp.push(ctx.len() as u8);
                            mp.extend_from_slice(&ctx);
                            mp.extend_from_slice(&msg);
                            mp
                        };
                        let want = h(&t["signature"]);
                        cases.push(Case {
                            tc_id: t["tcId"].as_u64().unwrap(),
                            internal,
                            det,
                            sk,
                            rnd,
                            msg,
                            ctx,
                            framed,
                            want,
                        });
                    }
                }
                assert_eq!(cases.len(), 28);

                // 1) Verify every single ACVP vector individually (internal, hedged, deterministic, with context)
                for c in &cases {
                    let pk: [u8; PK_BYTES] = c.sk[2 * N..4 * N].try_into().unwrap();
                    let sig = if c.internal {
                        let s = gpu_api::sign_internal(gpu, &c.msg, &c.sk, &c.rnd).unwrap();
                        assert!(
                            cpu::slh_verify_internal(&c.msg, &s, &pk),
                            "{} tcId {} verify_internal failed",
                            $set,
                            c.tc_id
                        );
                        s
                    } else if c.det {
                        let s = gpu_api::sign_deterministic(gpu, &c.msg, &c.ctx, &c.sk)
                            .unwrap()
                            .unwrap();
                        assert!(
                            cpu::verify(&c.msg, &s, &c.ctx, &pk),
                            "{} tcId {} verify det failed",
                            $set,
                            c.tc_id
                        );
                        s
                    } else {
                        let s = gpu_api::sign(gpu, &c.msg, &c.ctx, &c.sk, &c.rnd)
                            .unwrap()
                            .unwrap();
                        assert!(
                            cpu::verify(&c.msg, &s, &c.ctx, &pk),
                            "{} tcId {} verify hedged failed",
                            $set,
                            c.tc_id
                        );
                        s
                    };
                    assert_eq!(sig.len(), SIG_BYTES);
                    assert_eq!(sig, c.want, "{} single tcId {} mismatch", $set, c.tc_id);
                }

                // 2) Verify ALL 28 ACVP vectors in ONE single GPU batch dispatch!
                let reqs: Vec<SignInternalReq<'_, N>> = cases
                    .iter()
                    .map(|c| SignInternalReq {
                        msg: &c.framed,
                        sk: &c.sk,
                        addrnd: &c.rnd,
                    })
                    .collect();
                let batch_sigs = gpu
                    .$sg_batch::<N>(&PARAMS, &reqs)
                    .expect("GPU batch sign failed");
                assert_eq!(batch_sigs.len(), 28);
                for (c, sig) in cases.iter().zip(batch_sigs.iter()) {
                    assert_eq!(sig, &c.want, "{} batch tcId {} mismatch", $set, c.tc_id);
                }
            }

            #[test]
            fn cpu_parity_both_xmss_modes_and_edge_cases() {
                // Dedicated signers forcing both two-phase (per-chain) and streaming (per-leaf) XMSS paths.
                let mut gpu_two_phase = MetalSigner::new().unwrap();
                gpu_two_phase.two_phase_leaf_limit = Some(usize::MAX);
                let mut gpu_streaming = MetalSigner::new().unwrap();
                gpu_streaming.two_phase_leaf_limit = Some(0);

                let sk_seed = [0x11u8; N];
                let sk_prf = [0x22u8; N];
                let pk_seed = [0x33u8; N];

                let (cpu_sk, cpu_pk) = cpu::slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
                let (tp_sk, tp_pk) =
                    gpu_api::keygen_internal(&gpu_two_phase, &sk_seed, &sk_prf, &pk_seed).unwrap();
                let (st_sk, st_pk) =
                    gpu_api::keygen_internal(&gpu_streaming, &sk_seed, &sk_prf, &pk_seed).unwrap();
                assert_eq!((tp_sk, tp_pk), (cpu_sk, cpu_pk), "{} two-phase keygen", $set);
                assert_eq!((st_sk, st_pk), (cpu_sk, cpu_pk), "{} streaming keygen", $set);

                // Context > 255 bytes must return None (matching FIPS 205 Algorithm 22)
                assert!(gpu_api::sign(&gpu_two_phase, b"msg", &[0u8; 256], &cpu_sk, &[7u8; N])
                    .unwrap()
                    .is_none());
                assert!(gpu_api::sign_deterministic(&gpu_two_phase, b"msg", &[0u8; 256], &cpu_sk)
                    .unwrap()
                    .is_none());

                // Max valid context (255 bytes)
                let max_ctx = [0xABu8; 255];
                let cpu_max_sig = cpu::sign(b"max ctx test", &max_ctx, &cpu_sk, &[9u8; N]).unwrap();
                let gpu_max_sig =
                    gpu_api::sign(&gpu_two_phase, b"max ctx test", &max_ctx, &cpu_sk, &[9u8; N])
                        .unwrap()
                        .unwrap();
                assert_eq!(gpu_max_sig, cpu_max_sig);
                assert!(cpu::verify(b"max ctx test", &gpu_max_sig, &max_ctx, &cpu_pk));

                // Same-key batch of 4 messages tested on BOTH two-phase and streaming paths
                let msgs: [&[u8]; 4] = [
                    b"",
                    b"hello Apple Silicon M4 Metal GPU!",
                    &[0x5Au8; 137],
                    &[0xC3u8; 2048],
                ];
                let r0 = [0x01u8; N];
                let r1 = [0x02u8; N];
                let r2 = [0x03u8; N];
                let r3 = [0x04u8; N];
                let rnds: [&[u8; N]; 4] = [&r0, &r1, &r2, &r3];
                let ctx = b"slhdsa-metal-test";

                let cpu_sigs: Vec<Vec<u8>> = msgs
                    .iter()
                    .zip(rnds.iter())
                    .map(|(m, r)| cpu::sign(m, ctx, &cpu_sk, r).unwrap())
                    .collect();

                let tp_sigs = gpu_api::sign_batch_same_key(&gpu_two_phase, &cpu_sk, &msgs, ctx, &rnds)
                    .unwrap()
                    .unwrap();
                let st_sigs = gpu_api::sign_batch_same_key(&gpu_streaming, &cpu_sk, &msgs, ctx, &rnds)
                    .unwrap()
                    .unwrap();

                assert_eq!(tp_sigs, cpu_sigs, "{} two-phase batch sign mismatch", $set);
                assert_eq!(st_sigs, cpu_sigs, "{} streaming batch sign mismatch", $set);
                for (m, sig) in msgs.iter().zip(tp_sigs.iter()) {
                    assert!(cpu::verify(m, sig, ctx, &cpu_pk));
                }

                // Deterministic batch helper
                let det_cpu: Vec<Vec<u8>> = msgs
                    .iter()
                    .map(|m| cpu::sign_deterministic(m, ctx, &cpu_sk).unwrap())
                    .collect();
                let det_gpu =
                    gpu_api::sign_deterministic_batch_same_key(&gpu_streaming, &cpu_sk, &msgs, ctx)
                        .unwrap()
                        .unwrap();
                assert_eq!(det_gpu, det_cpu, "{} deterministic batch sign mismatch", $set);
            }
        }
    };
}

verify_set!(sha2_128s_tests, "sha2-128s", sha2_128s, sha2_128s, keygen_internal_batch, sign_internal_batch);
verify_set!(sha2_128f_tests, "sha2-128f", sha2_128f, sha2_128f, keygen_internal_batch, sign_internal_batch);
verify_set!(sha2_192s_tests, "sha2-192s", sha2_192s, sha2_192s, keygen_internal_batch, sign_internal_batch);
verify_set!(sha2_192f_tests, "sha2-192f", sha2_192f, sha2_192f, keygen_internal_batch, sign_internal_batch);
verify_set!(sha2_256s_tests, "sha2-256s", sha2_256s, sha2_256s, keygen_internal_batch, sign_internal_batch);
verify_set!(sha2_256f_tests, "sha2-256f", sha2_256f, sha2_256f, keygen_internal_batch, sign_internal_batch);

verify_set!(shake_128s_tests, "shake-128s", shake_128s, shake_128s, shake_keygen_internal_batch, shake_sign_internal_batch);
verify_set!(shake_128f_tests, "shake-128f", shake_128f, shake_128f, shake_keygen_internal_batch, shake_sign_internal_batch);
verify_set!(shake_192s_tests, "shake-192s", shake_192s, shake_192s, shake_keygen_internal_batch, shake_sign_internal_batch);
verify_set!(shake_192f_tests, "shake-192f", shake_192f, shake_192f, shake_keygen_internal_batch, shake_sign_internal_batch);
verify_set!(shake_256s_tests, "shake-256s", shake_256s, shake_256s, shake_keygen_internal_batch, shake_sign_internal_batch);
verify_set!(shake_256f_tests, "shake-256f", shake_256f, shake_256f, shake_keygen_internal_batch, shake_sign_internal_batch);

#[test]
fn rejects_nonstandard_geometry_before_dispatch() {
    let mut p = slhdsa::params::SHA2_128F;
    p.k += 1;
    let gpu = shared_gpu();
    assert!(gpu.keygen_internal_batch::<16>(&p, &[]).is_err());
    assert!(gpu.shake_sign_internal_batch::<16>(&p, &[]).is_err());
}
