//! Interoperability with RustCrypto's `slh-dsa` 0.2.0-rc.5 for all six SHA-2
//! parameter sets: the same keys from the same seeds, byte-identical
//! signatures (internal and pure interface, deterministic and hedged), each
//! crate verifying the other's signatures and rejecting tampered ones, and
//! byte-identical PKCS#8 and SubjectPublicKeyInfo encodings, which each
//! crate decodes from the other. The algorithm identifiers are taken from
//! `const_oid::db::fips205` through RustCrypto's `ParameterSet`.

use pkcs8::{DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey};
use upstream::signature::Keypair;
use upstream::ParameterSet;

/// SplitMix64.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn vec(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }
}

macro_rules! interop {
    ($($name:ident, $m:ident, $up:ident, $oid:literal, $seed:expr;)*) => {$(
        mod $name {
            use super::*;
            use slhdsa::$m as s;
            use s::params::{N, PK_BYTES, SIG_BYTES, SK_BYTES};
            type P = upstream::$up;

            #[test]
            fn keys_signatures_and_verdicts_agree() {
                let mut rng = Rng($seed);
                for round in 0..2 {
                    let seeds = rng.vec(3 * N);
                    let ours_sk: [u8; SK_BYTES];
                    let ours_pk: [u8; PK_BYTES];
                    (ours_sk, ours_pk) = s::slh_keygen_internal(
                        seeds[..N].try_into().unwrap(),
                        seeds[N..2 * N].try_into().unwrap(),
                        seeds[2 * N..].try_into().unwrap(),
                    );
                    let theirs = upstream::SigningKey::<P>::slh_keygen_internal(&seeds[..N], &seeds[N..2 * N], &seeds[2 * N..]);
                    let theirs_vk = theirs.verifying_key();
                    assert_eq!(&ours_sk[..], &theirs.to_bytes()[..]);
                    assert_eq!(&ours_pk[..], &theirs_vk.to_bytes()[..]);

                    // Exercise the segmented platform path against the upstream implementation.
                    let msg = rng.vec([0, 1025][round]);
                    let ctx = rng.vec([0, 255][round]);
                    let rand = rng.vec(N);
                    let rand_n: [u8; N] = rand.clone().try_into().unwrap();

                    // Internal interface, hedged and deterministic.
                    let a = s::slh_sign_internal(&msg, &ours_sk, &rand_n);
                    let b = theirs.slh_sign_internal(&[&msg], Some(&rand)).to_bytes();
                    assert!(a[..] == b[..], "sign_internal");
                    let pk_seed: [u8; N] = ours_sk[2 * N..3 * N].try_into().unwrap();
                    let a_det = s::slh_sign_internal(&msg, &ours_sk, &pk_seed);
                    assert!(a_det[..] == theirs.slh_sign_internal(&[&msg], None).to_bytes()[..], "sign_internal det");

                    // Pure interface with a context, hedged and deterministic,
                    // through the interface module.
                    let c = s::api::sign(&msg, &ctx, &ours_sk, &rand_n).unwrap();
                    let d = theirs.try_sign_with_context(&msg, &ctx, Some(&rand)).unwrap().to_bytes();
                    assert!(c[..] == d[..], "sign");
                    let c_det = s::api::sign_deterministic(&msg, &ctx, &ours_sk).unwrap();
                    assert!(c_det[..] == theirs.try_sign_with_context(&msg, &ctx, None).unwrap().to_bytes()[..], "sign det");
                    assert_eq!(c.len(), SIG_BYTES);

                    // Each verifies the other's, and both reject the same tampering.
                    let sig_up = upstream::Signature::<P>::try_from(&c[..]).unwrap();
                    assert!(theirs_vk.try_verify_with_context(&msg, &ctx, &sig_up).is_ok());
                    assert!(theirs_vk.slh_verify_internal(&[&msg], &upstream::Signature::<P>::try_from(&a[..]).unwrap()).is_ok());
                    assert!(s::api::verify(&msg, &d, &ctx, &ours_pk));
                    assert!(s::slh_verify_internal(&msg, &b, &ours_pk));
                    for at in [0, N, SIG_BYTES / 3, SIG_BYTES - 1] {
                        let mut t = c.clone();
                        t[at] ^= 0x08;
                        let theirs_ok = theirs_vk
                            .try_verify_with_context(&msg, &ctx, &upstream::Signature::<P>::try_from(&t[..]).unwrap())
                            .is_ok();
                        assert!(!theirs_ok);
                        assert!(!s::api::verify(&msg, &t, &ctx, &ours_pk));
                    }
                }
            }

            #[test]
            fn encodings_agree() {
                let mut rng = Rng($seed + 7);
                let seeds = rng.vec(3 * N);
                let theirs = upstream::SigningKey::<P>::slh_keygen_internal(&seeds[..N], &seeds[N..2 * N], &seeds[2 * N..]);
                let sk: [u8; SK_BYTES] = theirs.to_bytes()[..].try_into().unwrap();
                let pk: [u8; PK_BYTES] = theirs.verifying_key().to_bytes()[..].try_into().unwrap();

                // The identifier is the one in const_oid's FIPS 205 table, and
                // its last arc is in our prefixes.
                assert_eq!(<P as ParameterSet>::ALGORITHM_OID.to_string(), $oid);
                let oid = <P as ParameterSet>::ALGORITHM_OID;
                let oid_bytes = oid.as_bytes();
                assert!(s::encoding::PKCS8_PREFIX.windows(oid_bytes.len()).any(|w| w == oid_bytes));
                assert!(s::encoding::SPKI_PREFIX.windows(oid_bytes.len()).any(|w| w == oid_bytes));

                let their_der = theirs.to_pkcs8_der().unwrap();
                let mut ours = [0u8; s::params::PKCS8_BYTES];
                s::encoding::pkcs8_encode(&sk, &mut ours);
                assert_eq!(&ours[..], their_der.as_bytes(), "PKCS#8");
                let mut back = [0u8; SK_BYTES];
                assert!(s::encoding::pkcs8_decode(their_der.as_bytes(), &mut back));
                assert_eq!(back, sk);
                assert_eq!(&upstream::SigningKey::<P>::from_pkcs8_der(&ours).unwrap().to_bytes()[..], &sk[..]);

                let their_spki = theirs.verifying_key().to_public_key_der().unwrap();
                let ours = s::encoding::spki_encode(&pk);
                assert_eq!(&ours[..], their_spki.as_bytes(), "SPKI");
                assert_eq!(s::encoding::spki_decode(their_spki.as_bytes()), Some(pk));
                assert_eq!(&upstream::VerifyingKey::<P>::from_public_key_der(&ours).unwrap().to_bytes()[..], &pk[..]);
            }

            /// The encoders, decoders and byte conversions on their own.
            #[test]
            fn encoding_functions() {
                use s::encoding::*;
                let mut rng = Rng($seed + 9);
                let sk: [u8; SK_BYTES] = rng.vec(SK_BYTES).try_into().unwrap();
                let pk: [u8; PK_BYTES] = rng.vec(PK_BYTES).try_into().unwrap();
                assert_eq!(secret_key_from(&sk), Some(sk));
                assert_eq!(secret_key_from(&sk[1..]), None);
                assert_eq!(secret_key_from(&[&sk[..], &[0]].concat()), None);
                assert_eq!(public_key_from(&pk), Some(pk));
                assert_eq!(public_key_from(&sk), None);
                assert!(signature_len_ok(&vec![0; SIG_BYTES]));
                assert!(!signature_len_ok(&vec![0; SIG_BYTES - 1]));
                assert!(secret_keys_equal(&sk, &sk));
                for at in [0, SK_BYTES / 2, SK_BYTES - 1] {
                    let mut other = sk;
                    other[at] ^= 0x80;
                    assert!(!secret_keys_equal(&sk, &other));
                }
                let mut der = [0u8; s::params::PKCS8_BYTES];
                pkcs8_encode(&sk, &mut der);
                assert_eq!(&der[..PKCS8_PREFIX.len()], &PKCS8_PREFIX[..]);
                let mut out = [9u8; SK_BYTES];
                assert!(!pkcs8_decode(&der[1..], &mut out));
                assert!(!pkcs8_decode(&[&der[..], &[0]].concat(), &mut out));
                for at in 0..PKCS8_PREFIX.len() {
                    let mut bad = der;
                    bad[at] ^= 1;
                    assert!(!pkcs8_decode(&bad, &mut out));
                }
                assert_eq!(out, [9u8; SK_BYTES], "a refused decoding leaves the key untouched");
                assert!(pkcs8_decode(&der, &mut out));
                assert_eq!(out, sk);
                let spki = spki_encode(&pk);
                assert_eq!(spki_decode(&spki), Some(pk));
                assert_eq!(spki_decode(&spki[1..]), None);
                assert_eq!(spki_decode(&der), None);
                for at in 0..SPKI_PREFIX.len() {
                    let mut bad = spki;
                    bad[at] ^= 1;
                    assert_eq!(spki_decode(&bad), None);
                }
            }
        }
    )*};
}

interop! {
    rc_128s, sha2_128s, Sha2_128s, "2.16.840.1.101.3.4.3.20", 11;
    rc_128f, sha2_128f, Sha2_128f, "2.16.840.1.101.3.4.3.21", 22;
    rc_192s, sha2_192s, Sha2_192s, "2.16.840.1.101.3.4.3.22", 33;
    rc_192f, sha2_192f, Sha2_192f, "2.16.840.1.101.3.4.3.23", 44;
    rc_256s, sha2_256s, Sha2_256s, "2.16.840.1.101.3.4.3.24", 55;
    rc_256f, sha2_256f, Sha2_256f, "2.16.840.1.101.3.4.3.25", 66;
    rc_shake_128s, shake_128s, Shake128s, "2.16.840.1.101.3.4.3.26", 11;
    rc_shake_128f, shake_128f, Shake128f, "2.16.840.1.101.3.4.3.27", 22;
    rc_shake_192s, shake_192s, Shake192s, "2.16.840.1.101.3.4.3.28", 33;
    rc_shake_192f, shake_192f, Shake192f, "2.16.840.1.101.3.4.3.29", 44;
    rc_shake_256s, shake_256s, Shake256s, "2.16.840.1.101.3.4.3.30", 55;
    rc_shake_256f, shake_256f, Shake256f, "2.16.840.1.101.3.4.3.31", 66;
}
