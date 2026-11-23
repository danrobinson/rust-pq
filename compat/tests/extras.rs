//! What this crate adds to, or does differently from, RustCrypto's `slh-dsa`:
//! operating-system randomness, hedged signing, keys that key generation would not
//! produce, and care
//! with the secret; and many random inputs against RustCrypto. Every test is
//! run for each of the six SHA-2 parameter sets.

mod common;

/// The message lengths at which the two hashes of the message change shape.
///
/// `PRF_msg` hashes `opt_rand ‖ M'` after one key block, `H_msg` hashes
/// `R ‖ PK.seed ‖ PK.root ‖ M'`; `M' = 0 ‖ |ctx| ‖ ctx ‖ M`. The hash is
/// SHA-256 (64-byte blocks, 8-byte length) for n = 16 and SHA-512 (128-byte
/// blocks, 16-byte length) otherwise. Around each total where the padding
/// spills into another block, or the data fills one exactly, one byte less,
/// equal and one more: as `(ctx length, message length)`.
pub fn boundary_lengths(n: usize) -> Vec<(usize, usize)> {
    let (blk, lb) = if n == 16 { (64, 8) } else { (128, 16) };
    let mut out = vec![(0, 0), (0, 1), (5, 0)];
    let mut round = 0;
    for offset in [n, 3 * n] {
        for t in [blk - lb, blk, 2 * blk] {
            for d in [-1i64, 0, 1] {
                let total = (t as i64 + d - offset as i64 - 2) as usize;
                let ctx = (round * 14) % 50;
                round += 1;
                let pair = if total >= ctx { (ctx, total - ctx) } else { (0, total) };
                if !out.contains(&pair) {
                    out.push(pair);
                }
            }
        }
    }
    out.push((255, 1000));
    out.push((3, 70_000));
    out
}

macro_rules! extras {
    ($m:ident: $P:ident, $n:expr) => {
        mod $m {
            use crate::common::{FailingRng, TestRng};
            use slh_dsa::signature::{Keypair, RandomizedSigner, Signer};
            use slh_dsa::{$P, SigningKey};

            const N: usize = $n;

            /// The upstream types, for checking this crate's output with independent code.
            fn upstream_verify(vk: &[u8], msg: &[u8], ctx: &[u8], sig: &[u8]) -> bool {
                let vk = upstream::VerifyingKey::<upstream::$P>::try_from(vk).unwrap();
                let sig = upstream::Signature::<upstream::$P>::try_from(sig).unwrap();
                vk.try_verify_with_context(msg, ctx, &sig).is_ok()
            }

            #[test]
            #[cfg(feature = "getrandom")]
            fn generate_and_hedged_signing() {
                let sk = SigningKey::<$P>::generate().unwrap();
                let other = SigningKey::<$P>::generate().unwrap();
                assert!(sk != other, "two generated keys are equal");
                let vk = sk.verifying_key();

                // The key is the one FIPS 205 derives from its own seeds.
                let bytes = sk.to_bytes();
                let again = SigningKey::<$P>::slh_keygen_internal(&bytes[..N], &bytes[N..2 * N], &bytes[2 * N..3 * N]);
                assert!(again == sk);

                let msg = b"hedged";
                let ctx = b"ctx";
                let a = sk.try_sign_hedged(msg, ctx).unwrap();
                let b = sk.try_sign_hedged(msg, ctx).unwrap();
                assert!(a != b, "two hedged signatures of one message are equal");
                for sig in [&a, &b] {
                    assert!(vk.try_verify_with_context(msg, ctx, sig).is_ok());
                    assert!(vk.try_verify_with_context(msg, b"", sig).is_err());
                    assert!(upstream_verify(&vk.to_bytes(), msg, ctx, &sig.to_bytes()));
                }
                assert!(sk.try_sign_hedged(msg, &[0u8; 256]).is_err());
            }

            #[test]
            fn failing_random_source_is_an_error_not_a_weak_signature() {
                let sk = SigningKey::<$P>::new(&mut TestRng(1));
                assert!(sk.try_sign_with_rng(&mut FailingRng, b"m").is_err());
            }

            #[test]
            fn debug_output_does_not_contain_the_secret() {
                let sk = SigningKey::<$P>::new(&mut TestRng(7));
                let bytes = sk.to_bytes();
                let shown = format!("{sk:?} {sk:#?}");
                // `Debug` of a byte slice prints decimal numbers; look for runs of the secret.
                let secret: Vec<String> = bytes[..2 * N].iter().map(|b| b.to_string()).collect();
                for run in secret.windows(4) {
                    assert!(!shown.contains(&run.join(", ")), "secret bytes in Debug output");
                    assert!(!shown.contains(&run.join(",\n")), "secret bytes in Debug output");
                }
                // The public half is shown.
                let public: Vec<String> = bytes[2 * N..2 * N + 4].iter().map(|b| b.to_string()).collect();
                assert!(shown.contains(&public.join(", ")));
            }

            #[test]
            fn signing_key_comparison() {
                let sk = SigningKey::<$P>::new(&mut TestRng(3));
                let bytes = sk.to_bytes();
                for at in [0usize, N - 1, N, 2 * N - 1, 2 * N, 3 * N - 1, 3 * N, 4 * N - 1] {
                    let mut changed = bytes.clone();
                    changed[at] ^= 0x80;
                    let other = SigningKey::<$P>::try_from(changed.as_slice()).unwrap();
                    assert!(other != sk, "keys differing at byte {at} compare equal");
                }
                assert!(SigningKey::<$P>::try_from(bytes.as_slice()).unwrap() == sk);
            }

            /// Many keys, message lengths around every block boundary of the
            /// two message hashes, and long messages: signatures equal
            /// RustCrypto's byte for byte, and each crate accepts the other's.
            #[test]
            fn random_inputs_match_upstream() {
                let mut rng = TestRng(0x5eed ^ N as u64);
                for (round, (ctx_len, len)) in super::boundary_lengths(N).into_iter().enumerate() {
                    let seeds = rng.bytes(3 * N);
                    let msg = rng.bytes(len);
                    let ctx = rng.bytes(ctx_len);
                    let rand = rng.bytes(N);
                    let opt_rand = if round % 2 == 0 { None } else { Some(rand.as_slice()) };

                    let ours = SigningKey::<$P>::slh_keygen_internal(&seeds[..N], &seeds[N..2 * N], &seeds[2 * N..]);
                    let theirs = upstream::SigningKey::<upstream::$P>::slh_keygen_internal(
                        &seeds[..N],
                        &seeds[N..2 * N],
                        &seeds[2 * N..],
                    );
                    assert_eq!(ours.to_bytes(), theirs.to_bytes(), "keys differ, round {round}");

                    let sig = ours.try_sign_with_context(&msg, &ctx, opt_rand).unwrap();
                    let sig_theirs = theirs.try_sign_with_context(&msg, &ctx, opt_rand).unwrap();
                    assert!(
                        sig.to_bytes() == sig_theirs.to_bytes(),
                        "signatures differ, round {round}, ctx {ctx_len}, length {len}"
                    );

                    let vk = ours.verifying_key();
                    assert!(vk.try_verify_with_context(&msg, &ctx, &sig).is_ok());
                    assert!(upstream_verify(&vk.to_bytes(), &msg, &ctx, &sig.to_bytes()));
                    if len > 0 {
                        let mut bad = msg.clone();
                        bad[len / 2] ^= 1;
                        assert!(vk.try_verify_with_context(&bad, &ctx, &sig).is_err());
                    }
                }
                // Plain `sign` on a few more keys.
                for _ in 0..3 {
                    let ours = SigningKey::<$P>::new(&mut TestRng(rng.0));
                    let theirs = upstream::SigningKey::<upstream::$P>::new(&mut TestRng(rng.0));
                    let msg = rng.bytes(33);
                    assert!(ours.sign(&msg).to_bytes() == upstream::signature::Signer::sign(&theirs, &msg).to_bytes());
                }
            }

            /// A private key whose stored public half is not the one its seeds
            /// give: the signer, like RustCrypto's, signs with it, and the
            /// signature does not verify.
            #[test]
            fn a_key_with_a_wrong_public_half() {
                let sk = SigningKey::<$P>::new(&mut TestRng(22));
                let msg = b"message";
                let mut odd = sk.to_bytes();
                odd[4 * N - 1] ^= 1;
                let ours = SigningKey::<$P>::try_from(odd.as_slice()).unwrap();
                let theirs = upstream::SigningKey::<upstream::$P>::try_from(odd.as_slice()).unwrap();
                let plain = ours.try_sign(msg).unwrap();
                assert!(plain.to_bytes() == upstream::signature::Signer::sign(&theirs, msg).to_bytes());
                assert!(ours.verifying_key().try_verify_with_context(msg, b"", &plain).is_err());
            }
        }
    };
}

extras!(sha2_128s: Sha2_128s, 16);
extras!(sha2_128f: Sha2_128f, 16);
extras!(sha2_192s: Sha2_192s, 24);
extras!(sha2_192f: Sha2_192f, 24);
extras!(sha2_256s: Sha2_256s, 32);
extras!(sha2_256f: Sha2_256f, 32);

/// The boundary lengths are what they claim: for each set, the totals hashed
/// by `PRF_msg` and `H_msg` hit every boundary named above.
#[test]
fn boundary_lengths_cover_the_boundaries() {
    for n in [16usize, 24, 32] {
        let (blk, lb) = if n == 16 { (64, 8) } else { (128, 16) };
        let lengths = boundary_lengths(n);
        for offset in [n, 3 * n] {
            for t in [blk - lb, blk, 2 * blk] {
                for d in [-1i64, 0, 1] {
                    let want = (t as i64 + d) as usize;
                    assert!(
                        lengths.iter().any(|(c, l)| offset + 2 + c + l == want),
                        "n = {n}: no case hashes {want} bytes after offset {offset}"
                    );
                }
            }
        }
    }
}

/// With `hw-sha2`, SHA-256 really runs on the instructions (on a CPU that has
/// them, which every AArch64 Apple CPU does).
#[test]
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64"))]
fn hw_sha2_backend_is_in_use() {
    assert!(slhdsa::sha256::hw_active(), "hw-sha2 is on, but SHA-256 runs portable code");
}

/// Likewise for SHA-512 (FEAT_SHA512), also under `hw-sha2`.
#[test]
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64"))]
fn hw_sha512_backend_is_in_use() {
    assert!(slhdsa::sha512::hw_active(), "hw-sha2 is on, but SHA-512 runs portable code");
}
