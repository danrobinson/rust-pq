//! The decisions of the RustCrypto-style adapter (`../compat`), made here so
//! that they are translated and proved with the rest of the crate.
//!
//! The adapter's types hold byte arrays of the set's lengths; its methods
//! forward to these functions. Everything that decides something is here:
//! appending the parts of a multi-part message, the order of the argument checks (a context
//! over 255 bytes is refused before a randomizer of the wrong length is
//! noticed), which randomness the deterministic variants use, writing the
//! signature into the caller's buffer, reading the three seeds of key
//! generation, which bytes are accepted as keys and signatures and which part
//! of a private key is its public key, and the comparisons of keys,
//! signatures and algorithm identifiers. What the adapter keeps is the trait
//! plumbing, the random source, the calls into the `pkcs8` crate, and the
//! wiping (`../compat/README.md`).
//!
//! `N` must be `p.n`, and every buffer must have the length its comment
//! says, as for the functions of [`crate::slh`].

use alloc::vec::Vec;
use super::api::public_key;
use crate::encoding::{secret_key_from, secret_keys_equal, signature_len_ok};
use crate::params::Params;
use super::slh::{slh_keygen_internal, slh_sign_internal, with_context};
use crate::util::block;

/// One part of a multi-part message appended to the parts before it: the
/// adapter joins a message by calling this on each part in turn. (A function
/// that takes all the parts, `&[&[u8]]`, has nested borrows, which Aeneas
/// does not translate; so the loop over the parts stays in the adapter.)
pub fn append(m: &mut Vec<u8>, part: &[u8]) {
    m.extend_from_slice(part);
}

/// The randomizer: `addrnd` if `has_addrnd` (it must then be `n` bytes;
/// panics otherwise), else `PK.seed`, the third block of the private key.
/// (The adapter's `Option<&[u8]>` is passed as the pair `has_addrnd, addrnd`.)
fn randomizer<const N: usize>(sk: &[u8], has_addrnd: bool, addrnd: &[u8]) -> [u8; N] {
    if has_addrnd {
        assert!(addrnd.len() == N);
        block::<N>(addrnd, 0)
    } else {
        block::<N>(sk, 2)
    }
}

/// Algorithm 22 on the message `m`, hedged with `addrnd` or, if
/// `has_addrnd` is false, deterministic. `false` (and `sig` untouched) if
/// `ctx` is longer than 255 bytes; a randomizer that is not `n` bytes long
/// panics, after that test. Otherwise the signature is written to `sig`
/// (`p.sig_bytes()` bytes).
pub fn sign_into<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sk: &[u8],
    has_addrnd: bool,
    addrnd: &[u8],
    sig: &mut [u8],
) -> bool {
    if ctx.len() > 255 {
        return false;
    }
    let rand = randomizer::<N>(sk, has_addrnd, addrnd);
    #[cfg(feature = "platform-sha2")]
    if m.len() >= 1024 {
        let s = crate::slh::slh_sign(p, m, ctx, sk, &rand).unwrap();
        sig.copy_from_slice(&s);
        return true;
    }
    let mp = with_context(m, ctx);
    let s = slh_sign_internal::<N>(p, &mp, sk, &rand);
    sig.copy_from_slice(&s);
    true
}

/// Algorithm 19 on the message `m`, with `addrnd` (`n` bytes; panics
/// otherwise) or `PK.seed`. The signature is written to `sig`.
pub fn sign_internal_into<const N: usize>(
    p: &Params,
    m: &[u8],
    sk: &[u8],
    has_addrnd: bool,
    addrnd: &[u8],
    sig: &mut [u8],
) {
    let rand = randomizer::<N>(sk, has_addrnd, addrnd);
    let s = slh_sign_internal::<N>(p, m, sk, &rand);
    sig.copy_from_slice(&s);
}

/// Algorithm 18 on three seeds given separately, each `n` bytes (panics
/// otherwise): `SK` to `sk` (4n bytes), `PK` to `pk` (2n bytes).
#[inline(never)]
pub fn keygen_seeds<const N: usize>(
    p: &Params,
    sk_seed: &[u8],
    sk_prf: &[u8],
    pk_seed: &[u8],
    sk: &mut [u8],
    pk: &mut [u8],
) {
    assert!(sk_seed.len() == N && sk_prf.len() == N && pk_seed.len() == N);
    let a = block::<N>(sk_seed, 0);
    let b = block::<N>(sk_prf, 0);
    let c = block::<N>(pk_seed, 0);
    slh_keygen_internal::<N>(p, &a, &b, &c, sk, pk);
}

/// A private key and the public key it holds, from the caller's bytes: any
/// `4n` bytes and nothing else. `false`, with `sk` and `pk` untouched, if the
/// length is wrong.
pub fn signing_key_from<const N: usize>(bytes: &[u8], sk: &mut [u8], pk: &mut [u8]) -> bool {
    if !secret_key_from(bytes, sk) {
        return false;
    }
    public_key::<N>(sk, pk);
    true
}

/// A signature from the caller's bytes: any `p.sig_bytes()` bytes, and
/// nothing else. `false`, with `sig` untouched, otherwise.
pub fn signature_from(p: &Params, bytes: &[u8], sig: &mut [u8]) -> bool {
    if !signature_len_ok(p, bytes) {
        return false;
    }
    sig.copy_from_slice(bytes);
    true
}

/// Whether two byte strings are equal: the same length and the same bytes.
/// Used for public keys, signatures and algorithm identifiers (public data);
/// private keys are compared with [`secret_keys_equal`], which this also uses.
pub fn bytes_equal(a: &[u8], b: &[u8]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    secret_keys_equal(a, b)
}
