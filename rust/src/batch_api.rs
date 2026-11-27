//! Parallel batch signature verification across all twelve SLH-DSA parameter sets.
//!
//! Distributes independent pure SLH-DSA verifications (`Algorithm 24, slh_verify`)
//! across the shared worker pool via a lock-free work-stealing counter.

use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use crate::params::Params;
use crate::pool;

/// One signature verification input for parallel batch verification.
#[derive(Clone, Copy)]
pub struct VerifyItem<'a> {
    /// Message bytes.
    pub msg: &'a [u8],
    /// Candidate signature bytes.
    pub sig: &'a [u8],
    /// Context string (at most 255 bytes per FIPS 205).
    pub ctx: &'a [u8],
    /// Public key bytes (`2 * N` bytes).
    pub pk: &'a [u8],
}

impl<'a> VerifyItem<'a> {
    /// Construct a verification item from borrowed message, signature, context,
    /// and public key slices.
    #[inline]
    pub const fn new(msg: &'a [u8], sig: &'a [u8], ctx: &'a [u8], pk: &'a [u8]) -> Self {
        Self { msg, sig, ctx, pk }
    }
}

fn verify_batch_with<F>(items: &[VerifyItem<'_>], verify_one: F) -> Vec<bool>
where
    F: Fn(&VerifyItem<'_>) -> bool + Sync,
{
    if items.is_empty() {
        return Vec::new();
    }
    if items.len() == 1 {
        return alloc::vec![verify_one(&items[0])];
    }
    let threads = pool::available_threads().min(items.len());
    if threads < 2 {
        return items.iter().map(&verify_one).collect();
    }

    let results: Vec<AtomicBool> = (0..items.len()).map(|_| AtomicBool::new(false)).collect();
    let next = AtomicUsize::new(0);
    let work = || loop {
        let idx = next.fetch_add(1, Ordering::Relaxed);
        let Some(item) = items.get(idx) else { break };
        let ok = verify_one(item);
        results[idx].store(ok, Ordering::Relaxed);
    };
    // Public verification handles no secret key material, so stack scrubbing is unnecessary.
    pool::execute(threads, false, &work);
    results.into_iter().map(AtomicBool::into_inner).collect()
}

fn verify_batch_all_with<F>(items: &[VerifyItem<'_>], verify_one: F) -> bool
where
    F: Fn(&VerifyItem<'_>) -> bool + Sync,
{
    if items.is_empty() {
        return true;
    }
    if items.len() == 1 {
        return verify_one(&items[0]);
    }
    let threads = pool::available_threads().min(items.len());
    if threads < 2 {
        return items.iter().all(&verify_one);
    }

    let all_ok = AtomicBool::new(true);
    let next = AtomicUsize::new(0);
    let work = || loop {
        if !all_ok.load(Ordering::Relaxed) {
            break;
        }
        let idx = next.fetch_add(1, Ordering::Relaxed);
        let Some(item) = items.get(idx) else { break };
        if !verify_one(item) {
            all_ok.store(false, Ordering::Relaxed);
            break;
        }
    };
    pool::execute(threads, false, &work);
    all_ok.load(Ordering::Relaxed)
}

/// Verify a batch of SHA-2 SLH-DSA signatures in parallel, returning one `bool`
/// verdict per input item in matching order.
pub fn verify_batch_sha2<const N: usize>(p: &Params, items: &[VerifyItem<'_>]) -> Vec<bool> {
    verify_batch_with(items, |item| {
        item.pk.len() == 2 * N && crate::api::verify::<N>(p, item.msg, item.sig, item.ctx, item.pk)
    })
}

/// Verify a batch of SHA-2 SLH-DSA signatures in parallel, returning `true` iff
/// every signature is valid (short-circuiting on the first invalid item).
pub fn verify_batch_all_sha2<const N: usize>(p: &Params, items: &[VerifyItem<'_>]) -> bool {
    verify_batch_all_with(items, |item| {
        item.pk.len() == 2 * N && crate::api::verify::<N>(p, item.msg, item.sig, item.ctx, item.pk)
    })
}

/// Verify a batch of SHAKE SLH-DSA signatures in parallel, returning one `bool`
/// verdict per input item in matching order.
pub fn verify_batch_shake<const N: usize>(p: &Params, items: &[VerifyItem<'_>]) -> Vec<bool> {
    verify_batch_with(items, |item| {
        item.pk.len() == 2 * N
            && crate::shake::api::verify::<N>(p, item.msg, item.sig, item.ctx, item.pk)
    })
}

/// Verify a batch of SHAKE SLH-DSA signatures in parallel, returning `true` iff
/// every signature is valid (short-circuiting on the first invalid item).
pub fn verify_batch_all_shake<const N: usize>(p: &Params, items: &[VerifyItem<'_>]) -> bool {
    verify_batch_all_with(items, |item| {
        item.pk.len() == 2 * N
            && crate::shake::api::verify::<N>(p, item.msg, item.sig, item.ctx, item.pk)
    })
}

macro_rules! set_batch_verify {
    ($verify_fn:ident, $verify_all_fn:ident, $generic:ident, $generic_all:ident, $set:ident, $doc:expr) => {
        #[doc = concat!("Verify a batch of ", $doc, " signatures in parallel.")]
        pub fn $verify_fn(items: &[VerifyItem<'_>]) -> Vec<bool> {
            $generic::<{ crate::$set::params::N }>(&crate::$set::params::PARAMS, items)
        }

        #[doc = concat!("Verify that every ", $doc, " signature in `items` is valid, in parallel.")]
        pub fn $verify_all_fn(items: &[VerifyItem<'_>]) -> bool {
            $generic_all::<{ crate::$set::params::N }>(&crate::$set::params::PARAMS, items)
        }
    };
}

set_batch_verify!(verify_sha2_128s, verify_all_sha2_128s, verify_batch_sha2, verify_batch_all_sha2, sha2_128s, "SLH-DSA-SHA2-128s");
set_batch_verify!(verify_sha2_128f, verify_all_sha2_128f, verify_batch_sha2, verify_batch_all_sha2, sha2_128f, "SLH-DSA-SHA2-128f");
set_batch_verify!(verify_sha2_192s, verify_all_sha2_192s, verify_batch_sha2, verify_batch_all_sha2, sha2_192s, "SLH-DSA-SHA2-192s");
set_batch_verify!(verify_sha2_192f, verify_all_sha2_192f, verify_batch_sha2, verify_batch_all_sha2, sha2_192f, "SLH-DSA-SHA2-192f");
set_batch_verify!(verify_sha2_256s, verify_all_sha2_256s, verify_batch_sha2, verify_batch_all_sha2, sha2_256s, "SLH-DSA-SHA2-256s");
set_batch_verify!(verify_sha2_256f, verify_all_sha2_256f, verify_batch_sha2, verify_batch_all_sha2, sha2_256f, "SLH-DSA-SHA2-256f");

set_batch_verify!(verify_shake_128s, verify_all_shake_128s, verify_batch_shake, verify_batch_all_shake, shake_128s, "SLH-DSA-SHAKE-128s");
set_batch_verify!(verify_shake_128f, verify_all_shake_128f, verify_batch_shake, verify_batch_all_shake, shake_128f, "SLH-DSA-SHAKE-128f");
set_batch_verify!(verify_shake_192s, verify_all_shake_192s, verify_batch_shake, verify_batch_all_shake, shake_192s, "SLH-DSA-SHAKE-192s");
set_batch_verify!(verify_shake_192f, verify_all_shake_192f, verify_batch_shake, verify_batch_all_shake, shake_192f, "SLH-DSA-SHAKE-192f");
set_batch_verify!(verify_shake_256s, verify_all_shake_256s, verify_batch_shake, verify_batch_all_shake, shake_256s, "SLH-DSA-SHAKE-256s");
set_batch_verify!(verify_shake_256f, verify_all_shake_256f, verify_batch_shake, verify_batch_all_shake, shake_256f, "SLH-DSA-SHAKE-256f");
