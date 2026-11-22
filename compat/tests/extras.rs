//! What this crate adds to, or does differently from, RustCrypto's `slh-dsa`:
//! operating-system randomness, hedged signing, and care with the secret.

mod common;

use common::{FailingRng, TestRng};
use slh_dsa::signature::{Keypair, RandomizedSigner, Signer};
use slh_dsa::{Sha2_128s, SigningKey};

/// The upstream types, for checking this crate's output with independent code.
fn upstream_verify(vk: &[u8], msg: &[u8], ctx: &[u8], sig: &[u8]) -> bool {
    let vk = upstream::VerifyingKey::<upstream::Sha2_128s>::try_from(vk).unwrap();
    let sig = upstream::Signature::<upstream::Sha2_128s>::try_from(sig).unwrap();
    vk.try_verify_with_context(msg, ctx, &sig).is_ok()
}

#[test]
#[cfg(feature = "getrandom")]
fn generate_and_hedged_signing() {
    let sk = SigningKey::<Sha2_128s>::generate().unwrap();
    let other = SigningKey::<Sha2_128s>::generate().unwrap();
    assert!(sk != other, "two generated keys are equal");
    let vk = sk.verifying_key();

    // The key is the one FIPS 205 derives from its own seeds.
    let bytes = sk.to_bytes();
    let again = SigningKey::<Sha2_128s>::slh_keygen_internal(&bytes[..16], &bytes[16..32], &bytes[32..48]);
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
    let sk = SigningKey::<Sha2_128s>::new(&mut TestRng(1));
    assert!(sk.try_sign_with_rng(&mut FailingRng, b"m").is_err());
}

#[test]
fn debug_output_does_not_contain_the_secret() {
    let sk = SigningKey::<Sha2_128s>::new(&mut TestRng(7));
    let bytes = sk.to_bytes();
    let shown = format!("{sk:?} {sk:#?}");
    // `Debug` of a byte slice prints decimal numbers; look for runs of the secret.
    let secret: Vec<String> = bytes[..32].iter().map(|b| b.to_string()).collect();
    for run in secret.windows(4) {
        assert!(!shown.contains(&run.join(", ")), "secret bytes in Debug output");
        assert!(!shown.contains(&run.join(",\n")), "secret bytes in Debug output");
    }
    // The public half is shown.
    let public: Vec<String> = bytes[32..36].iter().map(|b| b.to_string()).collect();
    assert!(shown.contains(&public.join(", ")));
}

#[test]
fn signing_key_comparison() {
    let sk = SigningKey::<Sha2_128s>::new(&mut TestRng(3));
    let bytes = sk.to_bytes();
    for at in [0usize, 15, 16, 31, 32, 47, 48, 63] {
        let mut changed = bytes.clone();
        changed[at] ^= 0x80;
        let other = SigningKey::<Sha2_128s>::try_from(changed.as_slice()).unwrap();
        assert!(other != sk, "keys differing at byte {at} compare equal");
    }
    assert!(SigningKey::<Sha2_128s>::try_from(bytes.as_slice()).unwrap() == sk);
}

/// Many keys, message lengths around every block boundary of the message
/// hash, and long messages: signatures equal RustCrypto's byte for byte, and
/// each crate accepts the other's.
#[test]
fn random_inputs_match_upstream() {
    let mut rng = TestRng(0x5eed);
    let lengths = [0usize, 1, 15, 16, 17, 47, 48, 49, 63, 64, 65, 111, 112, 113, 127, 128, 129, 1000, 70_000];
    for (round, len) in lengths.iter().enumerate() {
        let seeds = rng.bytes(48);
        let msg = rng.bytes(*len);
        let ctx = rng.bytes(round * 14 % 256);
        let rand = rng.bytes(16);
        let opt_rand = if round % 2 == 0 { None } else { Some(rand.as_slice()) };

        let ours = SigningKey::<Sha2_128s>::slh_keygen_internal(&seeds[..16], &seeds[16..32], &seeds[32..]);
        let theirs =
            upstream::SigningKey::<upstream::Sha2_128s>::slh_keygen_internal(&seeds[..16], &seeds[16..32], &seeds[32..]);
        assert_eq!(ours.to_bytes(), theirs.to_bytes(), "keys differ, round {round}");

        let sig = ours.try_sign_with_context(&msg, &ctx, opt_rand).unwrap();
        let sig_theirs = theirs.try_sign_with_context(&msg, &ctx, opt_rand).unwrap();
        assert!(sig.to_bytes() == sig_theirs.to_bytes(), "signatures differ, round {round}, length {len}");

        let vk = ours.verifying_key();
        assert!(vk.try_verify_with_context(&msg, &ctx, &sig).is_ok());
        assert!(upstream_verify(&vk.to_bytes(), &msg, &ctx, &sig.to_bytes()));
        if *len > 0 {
            let mut bad = msg.clone();
            bad[len / 2] ^= 1;
            assert!(vk.try_verify_with_context(&bad, &ctx, &sig).is_err());
        }
    }
    // Plain `sign` on a few more keys.
    for _ in 0..3 {
        let ours = SigningKey::<Sha2_128s>::new(&mut TestRng(rng.0));
        let theirs = upstream::SigningKey::<upstream::Sha2_128s>::new(&mut TestRng(rng.0));
        let msg = rng.bytes(33);
        assert!(ours.sign(&msg).to_bytes() == upstream::signature::Signer::sign(&theirs, &msg).to_bytes());
    }
}

/// The checked signer: the same signature as the plain one on a good key,
/// with and without supplied randomness, and an error for a private key
/// whose stored public half is not the one its seeds give (the plain signer,
/// like RustCrypto's, signs with such a key and the signature does not
/// verify).
#[test]
fn checked_signing() {
    let sk = SigningKey::<Sha2_128s>::new(&mut TestRng(22));
    let rand = TestRng(23).bytes(16);
    for opt_rand in [None, Some(rand.as_slice())] {
        let plain = sk.try_sign_with_context(b"m", b"c", opt_rand).unwrap();
        let checked = sk.try_sign_checked(b"m", b"c", opt_rand).unwrap();
        assert!(checked == plain);
    }
    assert!(sk.try_sign_checked(b"m", &[0u8; 256], None).is_err());

    let msg = b"message";
    let mut odd = sk.to_bytes();
    odd[63] ^= 1;
    let ours = SigningKey::<Sha2_128s>::try_from(odd.as_slice()).unwrap();
    let theirs = upstream::SigningKey::<upstream::Sha2_128s>::try_from(odd.as_slice()).unwrap();
    assert!(ours.try_sign_checked(msg, b"", None).is_err());
    assert!(ours.try_sign_checked(msg, b"", Some(rand.as_slice())).is_err());
    let plain = ours.try_sign(msg).unwrap();
    assert!(plain.to_bytes() == upstream::signature::Signer::sign(&theirs, msg).to_bytes());
    assert!(ours.verifying_key().try_verify_with_context(msg, b"", &plain).is_err());
}
