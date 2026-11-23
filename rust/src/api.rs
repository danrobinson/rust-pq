//! The interface to use: key generation, signing and verification as FIPS 205
//! §10 defines them, with the random bytes supplied by the caller. Generic
//! over the parameter set; the modules `sha2_128s` … `sha2_256f` give each
//! set these functions with fixed-size key types (`sha2_128s::api`, …).
//!
//! [`sign`] and [`sign_deterministic`] are the signer of the standard and do
//! exactly its work.
//!
//! Nothing here returns a secret by value: key generation writes the private
//! key into the caller's buffer. The functions that work with the secret seed
//! are not inlined, so all their working storage lies below the caller's
//! frame when they return, where the caller can overwrite it.

use alloc::vec::Vec;
use crate::params::Params;
use super::slh::{slh_keygen_internal, slh_sign, slh_verify};
use crate::util::block;

/// Algorithm 21, `slh_keygen`, given its random bytes: `seeds` is
/// `SK.seed ‖ SK.prf ‖ PK.seed`, three fresh random `n`-byte strings in the
/// order the standard draws them. Writes the private key (4n bytes) to `sk`
/// and the public key (2n bytes) to `pk`.
#[inline(never)]
pub fn keygen<const N: usize>(p: &Params, seeds: &[u8], sk: &mut [u8], pk: &mut [u8]) {
    let sk_seed = block::<N>(seeds, 0);
    let sk_prf = block::<N>(seeds, 1);
    let pk_seed = block::<N>(seeds, 2);
    slh_keygen_internal::<N>(p, &sk_seed, &sk_prf, &pk_seed, sk, pk);
}

/// The public key held in a private key: its last two blocks,
/// `PK.seed ‖ PK.root`, written to `pk` (2n bytes).
#[inline]
pub fn public_key<const N: usize>(sk: &[u8], pk: &mut [u8]) {
    pk.copy_from_slice(&sk[2 * N..4 * N]);
}

/// Algorithm 22, `slh_sign`, hedged: `addrnd` is `n` fresh random bytes.
/// `None` if `ctx` is longer than 255 bytes.
pub fn sign<const N: usize>(p: &Params, m: &[u8], ctx: &[u8], sk: &[u8], addrnd: &[u8; N]) -> Option<Vec<u8>> {
    slh_sign::<N>(p, m, ctx, sk, addrnd)
}

/// Algorithm 22, `slh_sign`, deterministic variant: `PK.seed` takes the place
/// of the random bytes.
pub fn sign_deterministic<const N: usize>(p: &Params, m: &[u8], ctx: &[u8], sk: &[u8]) -> Option<Vec<u8>> {
    let pk_seed = block::<N>(sk, 2);
    slh_sign::<N>(p, m, ctx, sk, &pk_seed)
}

/// Algorithm 24, `slh_verify`.
pub fn verify<const N: usize>(p: &Params, m: &[u8], sig: &[u8], ctx: &[u8], pk: &[u8]) -> bool {
    slh_verify::<N>(p, m, sig, ctx, pk)
}
