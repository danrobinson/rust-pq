//! The interface to use: key generation, signing and verification as FIPS 205
//! §10 defines them, with the random bytes supplied by the caller.
//!
//! [`sign`] and [`sign_deterministic`] are the signer of the standard and do
//! exactly its work. [`sign_checked`] and [`sign_deterministic_checked`]
//! return the same signature after computing every value a one-time key
//! signs a second time by another route and comparing
//! ([`crate::slh::slh_sign_checked`]); that guards against a fault during
//! signing and costs a little under twice the time.
//!
//! Nothing here returns a secret by value: key generation writes the private
//! key into the caller's buffer. The functions that work with the secret seed
//! are not inlined, so all their working storage lies below the caller's
//! frame when they return, where the caller can overwrite it.

use crate::params::{N, PK_BYTES, SEED_BYTES, SK_BYTES};
use crate::slh::{slh_keygen_internal, slh_sign, slh_sign_checked, slh_verify};
use crate::util::block;

/// Algorithm 21, `slh_keygen`, given its random bytes: `seeds` is
/// `SK.seed ‖ SK.prf ‖ PK.seed`, three fresh random `n`-byte strings in the
/// order the standard draws them. Writes the private key to `sk` and the
/// public key to `pk`.
#[inline(never)]
pub fn keygen(seeds: &[u8; SEED_BYTES], sk: &mut [u8; SK_BYTES], pk: &mut [u8; PK_BYTES]) {
    let sk_seed = block(seeds, 0);
    let sk_prf = block(seeds, 1);
    let pk_seed = block(seeds, 2);
    let (s, p) = slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
    sk.copy_from_slice(&s);
    pk.copy_from_slice(&p);
}

/// The public key held in a private key: its last two blocks,
/// `PK.seed ‖ PK.root`.
pub fn public_key(sk: &[u8; SK_BYTES]) -> [u8; PK_BYTES] {
    let mut pk = [0u8; PK_BYTES];
    pk.copy_from_slice(&sk[2 * N..4 * N]);
    pk
}

/// Algorithm 22, `slh_sign`, hedged: `addrnd` is `n` fresh random bytes.
/// `None` if `ctx` is longer than 255 bytes.
pub fn sign(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
    slh_sign(m, ctx, sk, addrnd)
}

/// Algorithm 22, `slh_sign`, deterministic variant: `PK.seed` takes the place
/// of the random bytes.
pub fn sign_deterministic(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES]) -> Option<Vec<u8>> {
    let pk_seed = block(sk, 2);
    slh_sign(m, ctx, sk, &pk_seed)
}

/// [`sign`] with recomputation: the same signature, or `None` if `ctx` is
/// longer than 255 bytes or a recomputation disagreed (the key is not one
/// that key generation produces, or the computation was disturbed).
pub fn sign_checked(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES], addrnd: &[u8; N]) -> Option<Vec<u8>> {
    slh_sign_checked(m, ctx, sk, addrnd)
}

/// [`sign_deterministic`] with recomputation; see [`sign_checked`].
pub fn sign_deterministic_checked(m: &[u8], ctx: &[u8], sk: &[u8; SK_BYTES]) -> Option<Vec<u8>> {
    let pk_seed = block(sk, 2);
    slh_sign_checked(m, ctx, sk, &pk_seed)
}

/// Algorithm 24, `slh_verify`.
pub fn verify(m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8; PK_BYTES]) -> bool {
    slh_verify(m, sig, ctx, pk)
}
