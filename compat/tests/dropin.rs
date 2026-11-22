//! The drop-in claim, tested: one piece of source, written against the
//! interface of RustCrypto's `slh-dsa`, is compiled twice, once against that
//! crate and once against this one, and must produce the same bytes and the
//! same accept/reject answers at every step.

mod common;

macro_rules! usage {
    ($krate:ident) => {
        use super::common::{FailingRng, TestRng};
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
            ParameterSet, Sha2_128s, Signature, SignatureLen, SigningKey, SigningKeyLen, VerifyingKey,
            VerifyingKeyLen,
        };

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
            rec("name", <Sha2_128s as ParameterSet>::NAME.as_bytes());
            rec("oid", <Sha2_128s as ParameterSet>::ALGORITHM_OID.as_bytes());
            rec("sig alg id", &Signature::<Sha2_128s>::ALGORITHM_IDENTIFIER.to_der().unwrap());
            rec(
                "signer alg id",
                &SigningKey::<Sha2_128s>::SIGNATURE_ALGORITHM_IDENTIFIER.to_der().unwrap(),
            );
            let _: Array<u8, <Sha2_128s as SigningKeyLen>::SkLen> = Default::default();
            let _: Array<u8, <Sha2_128s as VerifyingKeyLen>::VkLen> = Default::default();
            let _: Array<u8, <Sha2_128s as SignatureLen>::SigLen> = Default::default();

            // Key generation from a random source.
            let sk = SigningKey::<Sha2_128s>::new(&mut rng);
            let vk = sk.verifying_key();
            let vk_ref: &VerifyingKey<Sha2_128s> = sk.as_ref();
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
            let rand = rng.bytes(16);
            let with_ctx = sk.try_sign_with_context(msg, ctx, None).unwrap();
            rec("ctx sign", &with_ctx.to_vec());
            rec("ctx sign rand", &sk.try_sign_with_context(msg, ctx, Some(&rand)).unwrap().to_vec());
            rec("ctx 255", &sk.try_sign_with_context(msg, &[7u8; 255], None).unwrap().to_vec());
            rec("ctx 256", &flag(sk.try_sign_with_context(msg, &[7u8; 256], None).is_ok()));
            rec("ctx verify", &flag(vk.try_verify_with_context(msg, ctx, &with_ctx).is_ok()));
            rec("ctx verify other ctx", &flag(vk.try_verify_with_context(msg, b"", &with_ctx).is_ok()));
            rec("ctx verify 256", &flag(vk.try_verify_with_context(msg, &[7u8; 256], &with_ctx).is_ok()));
            rec("ctx verify plain", &flag(vk.verify(msg, &with_ctx).is_ok()));

            // The internal functions of FIPS 205.
            let seeds = rng.bytes(48);
            let sk2 = SigningKey::<Sha2_128s>::slh_keygen_internal(&seeds[..16], &seeds[16..32], &seeds[32..]);
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
            let from_slice = Signature::<Sha2_128s>::try_from(sig_bytes.as_slice()).unwrap();
            let from_array: Signature<Sha2_128s> = (&sig_bytes).into();
            rec("sig eq", &flag(from_slice == sig && from_array == sig && sig.clone() == sig));
            rec("sig ne", &flag(hedged == sig));
            rec("sig from array", &Array::<u8, _>::from(from_array));
            rec("sig short", &flag(Signature::<Sha2_128s>::try_from(&sig_bytes[1..]).is_ok()));
            rec("sig long", &flag(Signature::<Sha2_128s>::try_from([&sig_bytes[..], &[0u8]].concat().as_slice()).is_ok()));
            rec("sig empty", &flag(Signature::<Sha2_128s>::try_from([].as_slice()).is_ok()));
            let mut tampered = sig_bytes.clone();
            for at in [0usize, 15, 16, 2927, 2928, 7855] {
                tampered[at] ^= 1;
                rec("tampered", &flag(vk.verify(msg, &(&tampered).into()).is_ok()));
                tampered[at] ^= 1;
            }
            rec("untampered", &flag(vk.verify(msg, &(&tampered).into()).is_ok()));
            rec("zero signature", &flag(vk.verify(msg, &(&Array::default()).into()).is_ok()));

            // Key encodings.
            let vk_bytes = vk.to_bytes();
            let vk_from_array: VerifyingKey<Sha2_128s> = vk_bytes.clone().try_into().unwrap();
            let vk_from_slice = VerifyingKey::<Sha2_128s>::try_from(vk_bytes.as_slice()).unwrap();
            rec("vk eq", &flag(vk_from_array == vk && vk_from_slice == vk && vk.clone() == vk));
            rec("vk ne", &flag(vk2 == vk));
            rec("vk to array", &Array::<u8, _>::from(&vk));
            rec("vk short", &flag(VerifyingKey::<Sha2_128s>::try_from(&vk_bytes[1..]).is_ok()));
            rec("vk verifies", &flag(vk_from_slice.verify(msg, &sig).is_ok()));
            let sk_bytes = sk.to_bytes();
            let sk_from_slice = SigningKey::<Sha2_128s>::try_from(sk_bytes.as_slice()).unwrap();
            rec("sk eq", &flag(sk_from_slice == sk && sk.clone() == sk));
            rec("sk ne", &flag(sk2 == sk));
            rec("sk short", &flag(SigningKey::<Sha2_128s>::try_from(&sk_bytes[1..]).is_ok()));
            rec("sk from slice signs", &sk_from_slice.sign(msg).to_vec());
            rec("sk from slice vk", &sk_from_slice.verifying_key().to_bytes());
            // A private key whose public half does not match is accepted as given.
            let mut odd = sk_bytes.clone();
            odd[63] ^= 1;
            let odd_sk = SigningKey::<Sha2_128s>::try_from(odd.as_slice()).unwrap();
            rec("odd sk vk", &odd_sk.verifying_key().to_bytes());
            rec("odd sk sign", &odd_sk.sign(msg).to_vec());

            // PKCS#8 and SubjectPublicKeyInfo.
            let sk_der = sk.to_pkcs8_der().unwrap();
            rec("pkcs8 der", sk_der.as_bytes());
            rec("pkcs8 pem", sk.to_pkcs8_pem(LineEnding::LF).unwrap().as_bytes());
            let sk_back = SigningKey::<Sha2_128s>::from_pkcs8_der(sk_der.as_bytes()).unwrap();
            rec("pkcs8 back", &sk_back.to_bytes());
            rec(
                "pkcs8 pem back",
                &SigningKey::<Sha2_128s>::from_pkcs8_pem(&sk.to_pkcs8_pem(LineEnding::LF).unwrap())
                    .unwrap()
                    .to_bytes(),
            );
            let vk_der = vk.to_public_key_der().unwrap();
            rec("spki der", vk_der.as_bytes());
            rec("spki pem", vk.to_public_key_pem(LineEnding::LF).unwrap().as_bytes());
            let vk_back = VerifyingKey::<Sha2_128s>::from_public_key_der(vk_der.as_bytes()).unwrap();
            rec("spki back", &vk_back.to_bytes());
            // Wrong contents: truncated, a public key where a private one belongs, another algorithm.
            rec("pkcs8 truncated", &flag(SigningKey::<Sha2_128s>::from_pkcs8_der(&sk_der.as_bytes()[..40]).is_ok()));
            rec("pkcs8 from spki", &flag(SigningKey::<Sha2_128s>::from_pkcs8_der(vk_der.as_bytes()).is_ok()));
            rec("spki from pkcs8", &flag(VerifyingKey::<Sha2_128s>::from_public_key_der(sk_der.as_bytes()).is_ok()));
            let mut other_alg = sk_der.as_bytes().to_vec();
            let oid = <Sha2_128s as ParameterSet>::ALGORITHM_OID;
            let at = other_alg.windows(oid.as_bytes().len()).position(|w| w == oid.as_bytes()).unwrap();
            other_alg[at + oid.as_bytes().len() - 1] ^= 1;
            rec("pkcs8 other algorithm", &flag(SigningKey::<Sha2_128s>::from_pkcs8_der(&other_alg).is_ok()));
            let mut other_vk = vk_der.as_bytes().to_vec();
            let at = other_vk.windows(oid.as_bytes().len()).position(|w| w == oid.as_bytes()).unwrap();
            other_vk[at + oid.as_bytes().len() - 1] ^= 1;
            rec("spki other algorithm", &flag(VerifyingKey::<Sha2_128s>::from_public_key_der(&other_vk).is_ok()));

            out
        }
    };
}

mod ours {
    usage!(slh_dsa);
}

mod theirs {
    usage!(upstream);
}

#[test]
fn same_source_gives_the_same_bytes() {
    let ours = ours::run();
    let theirs = theirs::run();
    assert_eq!(ours.len(), theirs.len());
    assert_eq!(ours.len(), 86, "number of recorded results");
    for (a, b) in ours.iter().zip(theirs.iter()) {
        assert_eq!(a.0, b.0);
        assert!(a.1 == b.1, "`{}` differs between this crate and RustCrypto's", a.0);
    }
    // The run is not vacuous: the answers that must be yes and no are so.
    let get = |name: &str| &ours.iter().find(|(n, _)| *n == name).unwrap().1;
    assert_eq!(get("verify"), &[1]);
    assert_eq!(get("verify other message"), &[0]);
    assert_eq!(get("ctx 256"), &[0]);
    assert_eq!(get("failing rng"), &[0]);
    assert_eq!(get("untampered"), &[1]);
    assert_eq!(ours.iter().filter(|(n, b)| *n == "tampered" && b == &[0]).count(), 6);
    assert_eq!(get("sign").len(), 7856);
    assert_ne!(get("sign"), get("sign_with_rng"));
    assert_eq!(get("sign"), get("multipart_sign"));
    assert_eq!(get("name"), b"SLH-DSA-SHA2-128s");
}
