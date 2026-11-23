//! Compile identical generic callers and compare the feature-independent API.
mod common;

macro_rules! caller {
    ($krate:ident, $module:ident) => {
        mod $module {
            use crate::common::TestRng;
            use $krate::signature::{Keypair, Signer, Verifier};
            use $krate::{ParameterSet, Signature, SigningKey};

            // The public family spellings must be interchangeable with each named set.
            #[test]
            fn family_type_aliases() {
                use hybrid_array::sizes::{U16, U24, U30, U32, U34, U39, U42, U47, U49};
                use $krate::*;
                fn identity<P: ParameterSet>(key: &SigningKey<P>) -> &SigningKey<P> { key }
                macro_rules! same_type {
                    ($named:ty, $family:ty) => {
                        let _: fn(&SigningKey<$named>) -> &SigningKey<$family> = identity::<$named>;
                    };
                }
                same_type!(Sha2_128s, Sha2L1<U16, U30>);
                same_type!(Sha2_128f, Sha2L1<U16, U34>);
                same_type!(Sha2_192s, Sha2L35<U24, U39>);
                same_type!(Sha2_192f, Sha2L35<U24, U42>);
                same_type!(Sha2_256s, Sha2L35<U32, U47>);
                same_type!(Sha2_256f, Sha2L35<U32, U49>);
                same_type!(Shake128s, Shake<U16, U30>);
                same_type!(Shake128f, Shake<U16, U34>);
                same_type!(Shake192s, Shake<U24, U39>);
                same_type!(Shake192f, Shake<U24, U42>);
                same_type!(Shake256s, Shake<U32, U47>);
                same_type!(Shake256f, Shake<U32, U49>);
            }

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
