//! The six SHA-2 parameter sets with fixed-size key types.
//!
//! Each module wraps the generic functions of `slh` for one parameter set,
//! so that key and seed lengths are fixed by the types.

macro_rules! parameter_set {
    ($name:ident, $params:ident, $n:expr, $doc:expr) => {
        #[doc = $doc]
        pub mod $name {
            use crate::params::$params;
            use crate::slh;

            /// Security parameter: seed and hash length in bytes.
            pub const N: usize = $n;
            /// Public key length in bytes.
            pub const PK_BYTES: usize = 2 * $n;
            /// Private key length in bytes.
            pub const SK_BYTES: usize = 4 * $n;

            /// Algorithm 18, `slh_keygen_internal`. Returns `(SK, PK)`.
            pub fn slh_keygen_internal(
                sk_seed: &[u8; N],
                sk_prf: &[u8; N],
                pk_seed: &[u8; N],
            ) -> ([u8; SK_BYTES], [u8; PK_BYTES]) {
                let (skv, pkv) = slh::slh_keygen_internal(&$params, sk_seed, sk_prf, pk_seed);
                let mut sk = [0u8; SK_BYTES];
                sk.copy_from_slice(&skv);
                let mut pk = [0u8; PK_BYTES];
                pk.copy_from_slice(&pkv);
                (sk, pk)
            }

            /// Algorithm 19, `slh_sign_internal`.
            pub fn slh_sign_internal(m: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Vec<u8> {
                slh::slh_sign_internal(&$params, m, sk, addrnd)
            }

            /// Algorithm 20, `slh_verify_internal`.
            pub fn slh_verify_internal(m: &[u8], sig: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                slh::slh_verify_internal(&$params, m, sig, pk)
            }

            /// Algorithm 22, `slh_sign` (pure signing), with caller-supplied
            /// randomness. `None` if the context is longer than 255 bytes.
            pub fn slh_sign(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
                slh::slh_sign(&$params, m, ctx, sk, addrnd)
            }

            /// Algorithm 24, `slh_verify` (pure verification).
            pub fn slh_verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                slh::slh_verify(&$params, m, sig, ctx, pk)
            }
        }
    };
}

parameter_set!(sha2_128s, SHA2_128S, 16, "SLH-DSA-SHA2-128s.");
parameter_set!(sha2_128f, SHA2_128F, 16, "SLH-DSA-SHA2-128f.");
parameter_set!(sha2_192s, SHA2_192S, 24, "SLH-DSA-SHA2-192s.");
parameter_set!(sha2_192f, SHA2_192F, 24, "SLH-DSA-SHA2-192f.");
parameter_set!(sha2_256s, SHA2_256S, 32, "SLH-DSA-SHA2-256s.");
parameter_set!(sha2_256f, SHA2_256F, 32, "SLH-DSA-SHA2-256f.");
