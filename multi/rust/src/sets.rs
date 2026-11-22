//! The six SHA-2 parameter sets with fixed-size key types.
//!
//! Each module wraps the generic functions of `slh`, `api` and `encoding` at
//! one parameter set, so that key and seed lengths are fixed by the types,
//! and offers them under the names and signatures of the single-set crate
//! (`../rust`): `sha2_128s::api::keygen`, `sha2_128s::slh_sign_internal_checked`,
//! `sha2_128s::encoding::pkcs8_encode`, `sha2_128s::params::SK_BYTES`, ….

macro_rules! parameter_set {
    ($name:ident, $params:ident, $n:expr, $doc:expr,
     pkcs8: [$($pk8:expr),*], spki: [$($spki:expr),*]) => {
        #[doc = $doc]
        pub mod $name {
            use alloc::vec::Vec;
            use crate::slh;

            /// The sizes of this parameter set (FIPS 205, Table 2).
            pub mod params {
                /// The parameter set as the generic functions take it.
                pub const PARAMS: crate::params::Params = crate::params::$params;
                /// Security parameter: seed and hash length in bytes.
                pub const N: usize = $n;
                pub const PK_BYTES: usize = 2 * N;
                pub const SK_BYTES: usize = 4 * N;
                /// The random bytes key generation consumes: `SK.seed ‖ SK.prf ‖ PK.seed`.
                pub const SEED_BYTES: usize = 3 * N;
                pub const SIG_BYTES: usize = PARAMS.n
                    + (PARAMS.k * (1 + PARAMS.a)) as usize * PARAMS.n
                    + PARAMS.d as usize * (2 * PARAMS.n + crate::params::LEN2 + PARAMS.hp as usize) * PARAMS.n;
                /// Length of the PKCS#8 encoding of a private key, and of the
                /// SubjectPublicKeyInfo encoding of a public key.
                pub const PKCS8_BYTES: usize = super::PKCS8_PREFIX.len() + SK_BYTES;
                pub const SPKI_BYTES: usize = super::SPKI_PREFIX.len() + PK_BYTES;
            }

            use params::{N, PARAMS, PK_BYTES, SEED_BYTES, SK_BYTES};

            /// Algorithm 18, `slh_keygen_internal`. Returns `(SK, PK)`.
            #[inline(never)]
            pub fn slh_keygen_internal(
                sk_seed: &[u8; N],
                sk_prf: &[u8; N],
                pk_seed: &[u8; N],
            ) -> ([u8; SK_BYTES], [u8; PK_BYTES]) {
                let mut sk = [0u8; SK_BYTES];
                let mut pk = [0u8; PK_BYTES];
                slh::slh_keygen_internal::<N>(&PARAMS, sk_seed, sk_prf, pk_seed, &mut sk, &mut pk);
                (sk, pk)
            }

            /// Algorithm 19, `slh_sign_internal`. `addrnd` is the per-signature
            /// randomness; pass `PK.seed` for the deterministic variant.
            #[inline(never)]
            pub fn slh_sign_internal(m: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Vec<u8> {
                slh::slh_sign_internal::<N>(&PARAMS, m, sk, addrnd)
            }

            /// Algorithm 19 with recomputation (see [`crate::slh::slh_sign_internal_checked`]).
            #[inline(never)]
            pub fn slh_sign_internal_checked(m: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
                slh::slh_sign_internal_checked::<N>(&PARAMS, m, sk, addrnd)
            }

            /// Algorithm 20, `slh_verify_internal`.
            pub fn slh_verify_internal(m: &[u8], sig: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                slh::slh_verify_internal::<N>(&PARAMS, m, sig, pk)
            }

            /// Algorithm 22, `slh_sign` (pure signing), with caller-supplied
            /// randomness. `None` if the context is longer than 255 bytes.
            pub fn slh_sign(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
                slh::slh_sign::<N>(&PARAMS, m, ctx, sk, addrnd)
            }

            /// Algorithm 22 with recomputation. `None` if the context is
            /// longer than 255 bytes or a recomputation disagreed.
            pub fn slh_sign_checked(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
                slh::slh_sign_checked::<N>(&PARAMS, m, ctx, sk, addrnd)
            }

            /// Algorithm 24, `slh_verify` (pure verification).
            pub fn slh_verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                slh::slh_verify::<N>(&PARAMS, m, sig, ctx, pk)
            }

            // The interface functions and the encodings are defined here, at
            // the level of the set's module, and `api` and `encoding` below
            // re-export them under the paths of the single-set crate. (Defining
            // them inside submodules named `api` and `encoding` would give the
            // Lean translation names such as `sets.sha2_128s.api.keygen` that
            // shadow the generic `api.keygen` they call.)

            /// Algorithm 21, `slh_keygen`, given its random bytes
            /// `SK.seed ‖ SK.prf ‖ PK.seed`. Writes the private key to `sk`
            /// and the public key to `pk`.
            #[inline(never)]
            pub fn keygen(seeds: &[u8; SEED_BYTES], sk: &mut [u8; SK_BYTES], pk: &mut [u8; PK_BYTES]) {
                crate::api::keygen::<N>(&PARAMS, seeds, sk, pk)
            }

            /// The public key held in a private key: `PK.seed ‖ PK.root`.
            pub fn public_key(sk: &[u8; SK_BYTES]) -> [u8; PK_BYTES] {
                let mut pk = [0u8; PK_BYTES];
                crate::api::public_key::<N>(sk, &mut pk);
                pk
            }

            /// Algorithm 22, `slh_sign`, hedged. `None` if `ctx` is longer than 255 bytes.
            pub fn sign(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
                crate::api::sign::<N>(&PARAMS, m, ctx, sk, addrnd)
            }

            /// Algorithm 22, `slh_sign`, deterministic variant.
            pub fn sign_deterministic(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES]) -> Option<Vec<u8>> {
                crate::api::sign_deterministic::<N>(&PARAMS, m, ctx, sk)
            }

            /// [`sign`] with recomputation.
            pub fn sign_checked(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
                crate::api::sign_checked::<N>(&PARAMS, m, ctx, sk, addrnd)
            }

            /// [`sign_deterministic`] with recomputation.
            pub fn sign_deterministic_checked(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES]) -> Option<Vec<u8>> {
                crate::api::sign_deterministic_checked::<N>(&PARAMS, m, ctx, sk)
            }

            /// Algorithm 24, `slh_verify`.
            pub fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
                crate::api::verify::<N>(&PARAMS, m, sig, ctx, pk)
            }

            /// `SEQUENCE { INTEGER 0, SEQUENCE { OID }, OCTET STRING(4n) …`
            pub const PKCS8_PREFIX: [u8; [$($pk8),*].len()] = [$($pk8),*];
            /// `SEQUENCE { SEQUENCE { OID }, BIT STRING(2n + 1), 0 unused bits …`
            pub const SPKI_PREFIX: [u8; [$($spki),*].len()] = [$($spki),*];

            use params::{PKCS8_BYTES, SPKI_BYTES};

            /// A private key from its bytes: any `4n` bytes, and nothing else.
            pub fn secret_key_from(bytes: &[u8]) -> Option<[u8; SK_BYTES]> {
                let mut sk = [0u8; SK_BYTES];
                if crate::encoding::secret_key_from(bytes, &mut sk) {
                    Some(sk)
                } else {
                    None
                }
            }

            /// A public key from its bytes: any `2n` bytes, and nothing else.
            pub fn public_key_from(bytes: &[u8]) -> Option<[u8; PK_BYTES]> {
                let mut pk = [0u8; PK_BYTES];
                if crate::encoding::public_key_from(bytes, &mut pk) {
                    Some(pk)
                } else {
                    None
                }
            }

            /// Whether `bytes` has the length of a signature.
            pub fn signature_len_ok(bytes: &[u8]) -> bool {
                crate::encoding::signature_len_ok(&PARAMS, bytes)
            }

            /// Whether two private keys are equal. Looks at every byte.
            pub fn secret_keys_equal(a: &[u8; SK_BYTES], b: &[u8; SK_BYTES]) -> bool {
                crate::encoding::secret_keys_equal(a, b)
            }

            /// The PKCS#8 (`OneAsymmetricKey`) DER encoding of a private key, written to `out`.
            pub fn pkcs8_encode(sk: &[u8; SK_BYTES], out: &mut [u8; PKCS8_BYTES]) {
                crate::encoding::der_encode(&PKCS8_PREFIX, sk, out)
            }

            /// The private key in a PKCS#8 DER encoding, written to `sk`.
            /// `false`, with `sk` untouched, unless `der` is exactly an
            /// encoding [`pkcs8_encode`] produces.
            pub fn pkcs8_decode(der: &[u8], sk: &mut [u8; SK_BYTES]) -> bool {
                crate::encoding::der_decode(&PKCS8_PREFIX, der, sk)
            }

            /// The `SubjectPublicKeyInfo` DER encoding of a public key.
            pub fn spki_encode(pk: &[u8; PK_BYTES]) -> [u8; SPKI_BYTES] {
                let mut out = [0u8; SPKI_BYTES];
                crate::encoding::der_encode(&SPKI_PREFIX, pk, &mut out);
                out
            }

            /// The public key in a `SubjectPublicKeyInfo` DER encoding, if
            /// `der` is exactly an encoding [`spki_encode`] produces.
            pub fn spki_decode(der: &[u8]) -> Option<[u8; PK_BYTES]> {
                let mut pk = [0u8; PK_BYTES];
                if crate::encoding::der_decode(&SPKI_PREFIX, der, &mut pk) {
                    Some(pk)
                } else {
                    None
                }
            }

            /// The interface to use (see [`crate::api`]), at this parameter set.
            pub mod api {
                pub use super::{keygen, public_key, sign, sign_checked, sign_deterministic, sign_deterministic_checked, verify};
            }

            /// Byte encodings at this parameter set (see [`crate::encoding`]).
            pub mod encoding {
                pub use super::{
                    pkcs8_decode, pkcs8_encode, public_key_from, secret_key_from, secret_keys_equal, signature_len_ok,
                    spki_decode, spki_encode, PKCS8_PREFIX, SPKI_PREFIX,
                };
            }
        }
    };
}

parameter_set!(sha2_128s, SHA2_128S, 16, "SLH-DSA-SHA2-128s.",
    pkcs8: [0x30, 0x52, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x14, 0x04, 0x40],
    spki: [0x30, 0x30, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x14, 0x03, 0x21, 0x00]);
parameter_set!(sha2_128f, SHA2_128F, 16, "SLH-DSA-SHA2-128f.",
    pkcs8: [0x30, 0x52, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x15, 0x04, 0x40],
    spki: [0x30, 0x30, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x15, 0x03, 0x21, 0x00]);
parameter_set!(sha2_192s, SHA2_192S, 24, "SLH-DSA-SHA2-192s.",
    pkcs8: [0x30, 0x72, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x16, 0x04, 0x60],
    spki: [0x30, 0x40, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x16, 0x03, 0x31, 0x00]);
parameter_set!(sha2_192f, SHA2_192F, 24, "SLH-DSA-SHA2-192f.",
    pkcs8: [0x30, 0x72, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x17, 0x04, 0x60],
    spki: [0x30, 0x40, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x17, 0x03, 0x31, 0x00]);
parameter_set!(sha2_256s, SHA2_256S, 32, "SLH-DSA-SHA2-256s.",
    pkcs8: [0x30, 0x81, 0x93, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x18, 0x04, 0x81, 0x80],
    spki: [0x30, 0x50, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x18, 0x03, 0x41, 0x00]);
parameter_set!(sha2_256f, SHA2_256F, 32, "SLH-DSA-SHA2-256f.",
    pkcs8: [0x30, 0x81, 0x93, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x19, 0x04, 0x81, 0x80],
    spki: [0x30, 0x50, 0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x19, 0x03, 0x41, 0x00]);
