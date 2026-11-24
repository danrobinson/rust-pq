//! The drop-in claim, tested: one piece of source, written against the
//! interface of RustCrypto's `slh-dsa`, is compiled twice, once against that
//! crate and once against this one, and must produce the same bytes and the
//! same accept/reject answers at every step, for all twelve pure SLH-DSA sets.

mod common;

macro_rules! usage {
    ($krate:ident, $P:ident, $n:expr, $fors_end:expr) => {
        use crate::common::{FailingRng, TestRng};
        use hybrid_array::Array;
        use pkcs8::{
            der::Encode,
            spki::{AssociatedAlgorithmIdentifier, SignatureAlgorithmIdentifier, SignatureBitStringEncoding},
            DecodePrivateKey, DecodePublicKey, EncodePrivateKey, EncodePublicKey, LineEnding,
        };
        use $krate::signature::{
            Keypair, MultipartSigner, MultipartVerifier, RandomizedMultipartSigner, RandomizedSigner,
            SignatureEncoding, Signer, Verifier,
        };
        use $krate::{
            ParameterSet, Signature, SignatureLen, SigningKey, SigningKeyLen, VerifyingKey, VerifyingKeyLen,
        };
        /// The parameter set under test, under one name in both crates.
        type Set = $krate::$P;
        /// `n`, and where the FORS signature ends (`n + k(1 + a)n`).
        const N: usize = $n;
        const FORS_END: usize = $fors_end;

        /// Code generic over the parameter set, as a caller might write it.
        fn sign_and_check<P: ParameterSet>(sk: &SigningKey<P>, msg: &[u8]) -> Vec<u8> {
            let sig: Signature<P> = sk.sign(msg);
            let vk: VerifyingKey<P> = sk.verifying_key();
            assert!(vk.verify(msg, &sig).is_ok());
            sig.to_vec()
        }

        /// Every public entry point, with each result recorded.
        pub fn run() -> Vec<(&'static str, Vec<u8>)> {
            let mut out: Vec<(&'static str, Vec<u8>)> = Vec::new();
            let mut rec = |name: &'static str, bytes: &[u8]| out.push((name, bytes.to_vec()));
            let flag = |ok: bool| [ok as u8];
            let mut rng = TestRng(2026);
            let msg = b"Hello, world!".as_slice();
            let other = b"Goodbye, world!".as_slice();

            // Names and identifiers.
            rec("name", <Set as ParameterSet>::NAME.as_bytes());
            rec("oid", <Set as ParameterSet>::ALGORITHM_OID.as_bytes());
            rec("sig alg id", &Signature::<Set>::ALGORITHM_IDENTIFIER.to_der().unwrap());
            rec(
                "signer alg id",
                &SigningKey::<Set>::SIGNATURE_ALGORITHM_IDENTIFIER.to_der().unwrap(),
            );
            let _: Array<u8, <Set as SigningKeyLen>::SkLen> = Default::default();
            let _: Array<u8, <Set as VerifyingKeyLen>::VkLen> = Default::default();
            let _: Array<u8, <Set as SignatureLen>::SigLen> = Default::default();

            // Key generation from a random source.
            let sk = SigningKey::<Set>::new(&mut rng);
            let vk = sk.verifying_key();
            let vk_ref: &VerifyingKey<Set> = sk.as_ref();
            rec("sk", &sk.to_bytes());
            rec("sk vec", &sk.to_vec());
            rec("vk", &vk.to_bytes());
            rec("vk vec", &vk.to_vec());
            rec("vk ref", &vk_ref.to_bytes());

            // Deterministic signing and verification.
            let sig = sk.sign(msg);
            rec("sign", &sig.to_bytes());
            rec("try_sign", &sk.try_sign(msg).unwrap().to_vec());
            rec("generic", &sign_and_check(&sk, msg));
            rec("verify", &flag(vk.verify(msg, &sig).is_ok()));
            rec("verify other message", &flag(vk.verify(other, &sig).is_ok()));
            rec("sign empty", &sk.sign(b"").to_vec());

            // Hedged signing with the caller's random source.
            let hedged = sk.sign_with_rng(&mut rng, msg);
            rec("sign_with_rng", &hedged.to_vec());
            rec("verify hedged", &flag(vk.verify(msg, &hedged).is_ok()));
            rec("try_sign_with_rng", &sk.try_sign_with_rng(&mut rng, msg).unwrap().to_vec());
            rec("failing rng", &flag(sk.try_sign_with_rng(&mut FailingRng, msg).is_ok()));

            // Multi-part messages.
            let parts: [&[u8]; 4] = [b"Hello", b"", b", wor", b"ld!"];
            let multi = sk.multipart_sign(&parts);
            rec("multipart_sign", &multi.to_vec());
            rec("try_multipart_sign", &sk.try_multipart_sign(&parts).unwrap().to_vec());
            rec("multipart_sign none", &sk.multipart_sign(&[]).to_vec());
            rec("multipart_verify", &flag(vk.multipart_verify(&parts, &sig).is_ok()));
            rec("multipart_verify bad", &flag(vk.multipart_verify(&parts[..3], &sig).is_ok()));
            rec("verify multi", &flag(vk.verify(msg, &multi).is_ok()));
            rec("multipart_sign_with_rng", &sk.multipart_sign_with_rng(&mut rng, &parts).to_vec());
            rec(
                "try_multipart_sign_with_rng",
                &sk.try_multipart_sign_with_rng(&mut rng, &parts).unwrap().to_vec(),
            );

            // Context strings.
            let ctx = b"a context".as_slice();
            let rand = rng.bytes(N);
            let with_ctx = sk.try_sign_with_context(msg, ctx, None).unwrap();
            rec("ctx sign", &with_ctx.to_vec());
            let long = [0x5a; 1025];
            let long_signature = sk.try_sign_with_context(&long, ctx, None).unwrap();
            rec("long ctx sign", &long_signature.to_vec());
            rec("long ctx verify", &flag(vk.try_verify_with_context(&long, ctx, &long_signature).is_ok()));
            rec("ctx sign rand", &sk.try_sign_with_context(msg, ctx, Some(&rand)).unwrap().to_vec());
            rec("ctx 255", &sk.try_sign_with_context(msg, &[7u8; 255], None).unwrap().to_vec());
            rec("ctx 256", &flag(sk.try_sign_with_context(msg, &[7u8; 256], None).is_ok()));
            rec("ctx verify", &flag(vk.try_verify_with_context(msg, ctx, &with_ctx).is_ok()));
            rec("ctx verify other ctx", &flag(vk.try_verify_with_context(msg, b"", &with_ctx).is_ok()));
            rec("ctx verify 256", &flag(vk.try_verify_with_context(msg, &[7u8; 256], &with_ctx).is_ok()));
            rec("ctx verify plain", &flag(vk.verify(msg, &with_ctx).is_ok()));

            // The internal functions of FIPS 205.
            let seeds = rng.bytes(3 * N);
            let sk2 = SigningKey::<Set>::slh_keygen_internal(&seeds[..N], &seeds[N..2 * N], &seeds[2 * N..]);
            let vk2 = sk2.verifying_key();
            rec("keygen_internal sk", &sk2.to_bytes());
            rec("keygen_internal vk", &vk2.to_bytes());
            let internal = sk2.slh_sign_internal(&[msg], None);
            rec("sign_internal", &internal.to_vec());
            rec("sign_internal rand", &sk2.slh_sign_internal(&[msg, other], Some(&rand)).to_vec());
            rec("verify_internal", &flag(vk2.slh_verify_internal(&[msg], &internal).is_ok()));
            rec("verify_internal split", &flag(vk2.slh_verify_internal(&[&msg[..5], &msg[5..]], &internal).is_ok()));
            rec("verify_internal other", &flag(vk2.slh_verify_internal(&[other], &internal).is_ok()));
            rec("verify_internal wrong key", &flag(vk.slh_verify_internal(&[msg], &internal).is_ok()));
            rec("internal is not pure", &flag(vk2.verify(msg, &internal).is_ok()));

            // Signature encodings.
            let sig_bytes = sig.to_bytes();
            rec("sig encoded_len", &(sig.encoded_len() as u64).to_be_bytes());
            rec("sig repr", &SignatureEncoding::to_bytes(&sig));
            rec("sig into vec", &Vec::<u8>::from(&sig));
            rec("sig bitstring", &sig.to_bitstring().unwrap().to_der().unwrap());
            let from_slice = Signature::<Set>::try_from(sig_bytes.as_slice()).unwrap();
            let from_array: Signature<Set> = (&sig_bytes).into();
            rec("sig eq", &flag(from_slice == sig && from_array == sig && sig.clone() == sig));
            rec("sig ne", &flag(hedged == sig));
            rec("sig from array", &Array::<u8, _>::from(from_array));
            rec("sig short", &flag(Signature::<Set>::try_from(&sig_bytes[1..]).is_ok()));
            rec("sig long", &flag(Signature::<Set>::try_from([&sig_bytes[..], &[0u8]].concat().as_slice()).is_ok()));
            rec("sig empty", &flag(Signature::<Set>::try_from([].as_slice()).is_ok()));
            let mut tampered = sig_bytes.clone();
            let sig_len = sig_bytes.len();
            for at in [0usize, N - 1, N, FORS_END - 1, FORS_END, sig_len - 1] {
                tampered[at] ^= 1;
                rec("tampered", &flag(vk.verify(msg, &(&tampered).into()).is_ok()));
                tampered[at] ^= 1;
            }
            rec("untampered", &flag(vk.verify(msg, &(&tampered).into()).is_ok()));
            rec("zero signature", &flag(vk.verify(msg, &(&Array::default()).into()).is_ok()));

            // Key encodings.
            let vk_bytes = vk.to_bytes();
            let vk_from_array: VerifyingKey<Set> = vk_bytes.clone().try_into().unwrap();
            let vk_from_slice = VerifyingKey::<Set>::try_from(vk_bytes.as_slice()).unwrap();
            rec("vk eq", &flag(vk_from_array == vk && vk_from_slice == vk && vk.clone() == vk));
            rec("vk ne", &flag(vk2 == vk));
            rec("vk to array", &Array::<u8, _>::from(&vk));
            rec("vk short", &flag(VerifyingKey::<Set>::try_from(&vk_bytes[1..]).is_ok()));
            rec("vk verifies", &flag(vk_from_slice.verify(msg, &sig).is_ok()));
            let sk_bytes = sk.to_bytes();
            let sk_from_slice = SigningKey::<Set>::try_from(sk_bytes.as_slice()).unwrap();
            rec("sk eq", &flag(sk_from_slice == sk && sk.clone() == sk));
            rec("sk ne", &flag(sk2 == sk));
            rec("sk short", &flag(SigningKey::<Set>::try_from(&sk_bytes[1..]).is_ok()));
            rec("sk from slice signs", &sk_from_slice.sign(msg).to_vec());
            rec("sk from slice vk", &sk_from_slice.verifying_key().to_bytes());
            // A private key whose public half does not match is accepted as given.
            let mut odd = sk_bytes.clone();
            odd[4 * N - 1] ^= 1;
            let odd_sk = SigningKey::<Set>::try_from(odd.as_slice()).unwrap();
            rec("odd sk vk", &odd_sk.verifying_key().to_bytes());
            rec("odd sk sign", &odd_sk.sign(msg).to_vec());

            // PKCS#8 and SubjectPublicKeyInfo.
            let sk_der = sk.to_pkcs8_der().unwrap();
            rec("pkcs8 der", sk_der.as_bytes());
            rec("pkcs8 pem", sk.to_pkcs8_pem(LineEnding::LF).unwrap().as_bytes());
            let sk_back = SigningKey::<Set>::from_pkcs8_der(sk_der.as_bytes()).unwrap();
            rec("pkcs8 back", &sk_back.to_bytes());
            rec(
                "pkcs8 pem back",
                &SigningKey::<Set>::from_pkcs8_pem(&sk.to_pkcs8_pem(LineEnding::LF).unwrap())
                    .unwrap()
                    .to_bytes(),
            );
            let vk_der = vk.to_public_key_der().unwrap();
            rec("spki der", vk_der.as_bytes());
            rec("spki pem", vk.to_public_key_pem(LineEnding::LF).unwrap().as_bytes());
            let vk_back = VerifyingKey::<Set>::from_public_key_der(vk_der.as_bytes()).unwrap();
            rec("spki back", &vk_back.to_bytes());
            // Wrong contents: truncated, a public key where a private one belongs, another algorithm.
            rec("pkcs8 truncated", &flag(SigningKey::<Set>::from_pkcs8_der(&sk_der.as_bytes()[..40]).is_ok()));
            rec("pkcs8 from spki", &flag(SigningKey::<Set>::from_pkcs8_der(vk_der.as_bytes()).is_ok()));
            rec("spki from pkcs8", &flag(VerifyingKey::<Set>::from_public_key_der(sk_der.as_bytes()).is_ok()));
            let mut other_alg = sk_der.as_bytes().to_vec();
            let oid = <Set as ParameterSet>::ALGORITHM_OID;
            let at = other_alg.windows(oid.as_bytes().len()).position(|w| w == oid.as_bytes()).unwrap();
            other_alg[at + oid.as_bytes().len() - 1] ^= 1;
            rec("pkcs8 other algorithm", &flag(SigningKey::<Set>::from_pkcs8_der(&other_alg).is_ok()));
            let mut other_vk = vk_der.as_bytes().to_vec();
            let at = other_vk.windows(oid.as_bytes().len()).position(|w| w == oid.as_bytes()).unwrap();
            other_vk[at + oid.as_bytes().len() - 1] ^= 1;
            rec("spki other algorithm", &flag(VerifyingKey::<Set>::from_public_key_der(&other_vk).is_ok()));

            out
        }
    };
}

/// Each set, under the same name in both crates: `n` and the end of the
/// FORS signature, `n + k(1 + a)n` (FIPS 205, Table 2).
macro_rules! sets {
    ($($m:ident: $P:ident, $n:expr, $k:expr, $a:expr;)*) => {
        $(mod $m {
            pub mod ours {
                usage!(slh_dsa, $P, $n, $n + $k * (1 + $a) * $n);
            }
            pub mod theirs {
                usage!(upstream, $P, $n, $n + $k * (1 + $a) * $n);
            }
        })*

        /// Every set's name, run in each crate.
        const SETS: &[(&str, fn() -> Vec<(&'static str, Vec<u8>)>, fn() -> Vec<(&'static str, Vec<u8>)>)] =
            &[$((stringify!($P), $m::ours::run, $m::theirs::run)),*];
    };
}

sets! {
    sha2_128s: Sha2_128s, 16, 14, 12;
    sha2_128f: Sha2_128f, 16, 33, 6;
    sha2_192s: Sha2_192s, 24, 17, 14;
    sha2_192f: Sha2_192f, 24, 33, 8;
    sha2_256s: Sha2_256s, 32, 22, 14;
    sha2_256f: Sha2_256f, 32, 35, 9;
    shake_128s: Shake128s, 16, 14, 12;
    shake_128f: Shake128f, 16, 33, 6;
    shake_192s: Shake192s, 24, 17, 14;
    shake_192f: Shake192f, 24, 33, 8;
    shake_256s: Shake256s, 32, 22, 14;
    shake_256f: Shake256f, 32, 35, 9;
}

/// The FIPS 205 names and signature lengths, as an independent check.
const EXPECTED: [(&str, &str, usize); 12] = [
    ("Sha2_128s", "SLH-DSA-SHA2-128s", 7856),
    ("Sha2_128f", "SLH-DSA-SHA2-128f", 17088),
    ("Sha2_192s", "SLH-DSA-SHA2-192s", 16224),
    ("Sha2_192f", "SLH-DSA-SHA2-192f", 35664),
    ("Sha2_256s", "SLH-DSA-SHA2-256s", 29792),
    ("Sha2_256f", "SLH-DSA-SHA2-256f", 49856),
    ("Shake128s", "SLH-DSA-SHAKE-128s", 7856),
    ("Shake128f", "SLH-DSA-SHAKE-128f", 17088),
    ("Shake192s", "SLH-DSA-SHAKE-192s", 16224),
    ("Shake192f", "SLH-DSA-SHAKE-192f", 35664),
    ("Shake256s", "SLH-DSA-SHAKE-256s", 29792),
    ("Shake256f", "SLH-DSA-SHAKE-256f", 49856),
];

/// All twelve sets in one test, so that the total is pinned in one place.
#[test]
fn same_source_gives_the_same_bytes() {
    let mut total = 0;
    for (i, (set, ours, theirs)) in SETS.iter().enumerate() {
        let ours = ours();
        let theirs = theirs();
        assert_eq!(ours.len(), theirs.len(), "{set}");
        assert_eq!(ours.len(), 88, "number of recorded results, {set}");
        for (a, b) in ours.iter().zip(theirs.iter()) {
            assert_eq!(a.0, b.0);
            assert!(a.1 == b.1, "`{}` differs between this crate and RustCrypto's, {set}", a.0);
        }
        // The run is not vacuous: the answers that must be yes and no are so.
        let get = |name: &str| &ours.iter().find(|(n, _)| *n == name).unwrap().1;
        assert_eq!(get("verify"), &[1], "{set}");
        assert_eq!(get("verify other message"), &[0], "{set}");
        assert_eq!(get("ctx 256"), &[0], "{set}");
        assert_eq!(get("failing rng"), &[0], "{set}");
        assert_eq!(get("untampered"), &[1], "{set}");
        assert_eq!(ours.iter().filter(|(n, b)| *n == "tampered" && b == &[0]).count(), 6, "{set}");
        assert_ne!(get("sign"), get("sign_with_rng"), "{set}");
        assert_eq!(get("sign"), get("multipart_sign"), "{set}");
        let (name, fips_name, sig_len) = EXPECTED[i];
        assert_eq!(*set, name);
        assert_eq!(get("name"), fips_name.as_bytes());
        assert_eq!(get("sign").len(), sig_len, "{set}");
        total += ours.len();
        println!("{set}: {} results equal", ours.len());
    }
    assert_eq!(total, 1056, "number of recorded results, all twelve sets");
}
