//! Is anything derived from the secret seed left in freed heap memory?
//!
//! This test binary's allocator looks through every block as it is freed
//! (and so also every block that is moved by a reallocation) for the two
//! secret seeds and HMAC's two key blocks. Key generation, signing, cloning
//! and dropping keys must free nothing that contains them.
//!
//! Controls: copying the private key into a `Vec` and dropping it, and an
//! HMAC that builds its key block in a `Vec`, must both be caught.

use slh_dsa::{Sha2_128s, SigningKey};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};

const PATTERNS: usize = 4;
const LEN: usize = 16;

static WATCHING: AtomicBool = AtomicBool::new(false);
static FOUND: AtomicUsize = AtomicUsize::new(0);
#[allow(clippy::declare_interior_mutable_const)]
const ZERO: AtomicU8 = AtomicU8::new(0);
#[allow(clippy::declare_interior_mutable_const)]
const ROW: [AtomicU8; LEN] = [ZERO; LEN];
static WANTED: [[AtomicU8; LEN]; PATTERNS] = [ROW; PATTERNS];

struct Watching;

// SAFETY: every call is passed on to the system allocator unchanged; the
// block being freed is only read, while it is still allocated.
unsafe impl GlobalAlloc for Watching {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if WATCHING.load(Ordering::Relaxed) && layout.size() >= LEN {
            let block = unsafe { std::slice::from_raw_parts(ptr, layout.size()) };
            for pattern in &WANTED {
                let mut want = [0u8; LEN];
                for (w, p) in want.iter_mut().zip(pattern.iter()) {
                    *w = p.load(Ordering::Relaxed);
                }
                if block.windows(LEN).any(|w| w == want) {
                    FOUND.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
        unsafe { System.dealloc(ptr, layout) }
    }
    // `realloc` is the default: allocate, copy, and free the old block
    // through `dealloc` above, so a block that grows is looked through too.
}

#[global_allocator]
static ALLOCATOR: Watching = Watching;

/// Run `f` with the allocator watching for `patterns`; how many freed blocks
/// held one.
fn freed_with(patterns: &[[u8; LEN]; PATTERNS], f: impl FnOnce()) -> usize {
    for (slot, pattern) in WANTED.iter().zip(patterns.iter()) {
        for (s, p) in slot.iter().zip(pattern.iter()) {
            s.store(*p, Ordering::Relaxed);
        }
    }
    FOUND.store(0, Ordering::Relaxed);
    WATCHING.store(true, Ordering::Relaxed);
    f();
    WATCHING.store(false, Ordering::Relaxed);
    FOUND.load(Ordering::Relaxed)
}

#[test]
fn nothing_secret_is_freed_unwiped() {
    let mut seeds = [0u8; 48];
    for (i, b) in seeds.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(0x65).wrapping_add(0x11);
    }
    let sk_seed: [u8; 16] = seeds[0..16].try_into().unwrap();
    let sk_prf: [u8; 16] = seeds[16..32].try_into().unwrap();
    let inner: [u8; 16] = core::array::from_fn(|i| sk_prf[i] ^ 0x36);
    let outer: [u8; 16] = core::array::from_fn(|i| sk_prf[i] ^ 0x5c);
    let patterns = [sk_seed, sk_prf, inner, outer];
    let message = vec![0x5au8; 3000];

    let leaked = freed_with(&patterns, || {
        let key = SigningKey::<Sha2_128s>::slh_keygen_internal(&seeds[0..16], &seeds[16..32], &seeds[32..48]);
        let sig = key.try_sign_with_context(&message, b"context", Some(&[9u8; 16])).unwrap();
        std::hint::black_box(&sig);
        let sig = key.try_sign_with_context(&message, b"", None).unwrap();
        std::hint::black_box(&sig);
        let sig = key.try_sign_checked(&message, b"", None).unwrap();
        std::hint::black_box(&sig);
        let copy = key.clone();
        let parsed = SigningKey::<Sha2_128s>::try_from(&key.to_bytes()[..]).unwrap();
        drop(key);
        drop(copy);
        drop(parsed);
    });
    assert_eq!(leaked, 0, "blocks freed with a secret still in them");

    // Control: a copy of the private key in a `Vec`, dropped as it is.
    let key = SigningKey::<Sha2_128s>::slh_keygen_internal(&seeds[0..16], &seeds[16..32], &seeds[32..48]);
    let leaked = freed_with(&patterns, || drop(std::hint::black_box(key.to_vec())));
    assert!(leaked > 0, "the allocator did not notice a freed copy of the key");

    // Control: HMAC with its key blocks in growing `Vec`s, as `prf_msg` used
    // to compute it.
    let leaked = freed_with(&patterns, || {
        std::hint::black_box(slhdsa::sha256::hmac_sha256(&sk_prf, &message));
    });
    assert!(leaked > 0, "the allocator did not notice HMAC's key block");
}
