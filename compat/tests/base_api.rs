//! Compile identical generic callers and compare the feature-independent API.
mod common;

macro_rules! caller {
    ($krate:ident, $module:ident) => {
        mod $module {
            use crate::common::TestRng;
            use $krate::signature::{Keypair, Signer, Verifier};
            use $krate::{ParameterSet, Signature, SigningKey};

            fn clone_set<P: ParameterSet>(set: &P) -> P {
                set.clone()
            }
            fn debug_set<P: ParameterSet>(set: &P) -> &dyn core::fmt::Debug {
                set
            }

            pub fn sign<P: ParameterSet>() -> (Vec<u8>, Vec<u8>) {
                let _: fn(&P) -> P = clone_set::<P>;
                let _: fn(&P) -> &dyn core::fmt::Debug = debug_set::<P>;
                let sk = SigningKey::<P>::new(&mut TestRng(42));
                let vk = sk.verifying_key();
                let sig: Signature<P> = sk.sign(b"generic caller");
                vk.verify(b"generic caller", &sig).unwrap();
                assert!(vk.verify(b"other message", &sig).is_err());
                (
                    vk.to_bytes().as_slice().to_owned(),
                    sig.to_bytes().as_slice().to_owned(),
                )
            }
        }
    };
}

caller!(upstream, reference);
caller!(slh_dsa, local);

#[test]
fn generic_caller_matches_upstream() {
    assert_eq!(
        local::sign::<slh_dsa::Sha2_128f>(),
        reference::sign::<upstream::Sha2_128f>()
    );
    assert_eq!(
        local::sign::<slh_dsa::Shake128f>(),
        reference::sign::<upstream::Shake128f>()
    );
}
