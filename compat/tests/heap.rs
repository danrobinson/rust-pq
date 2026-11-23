//! Is anything derived from the secret seed left in freed heap memory? For
//! each of the six SHA-2 parameter sets.
//!
//! This test binary's allocator looks through every block as it is freed
//! (and so also every block that is moved by a reallocation) for the two
//! secret seeds, HMAC's two key blocks, and the inner HMAC digest of
//! `PRF_msg` for each message signed (it depends on `SK.prf`). Key
//! generation, signing, cloning and dropping keys must free nothing that
//! contains them.
//!
//! Controls: copying the private key into a `Vec` and dropping it, and an
//! HMAC that builds its key block and inner digest in `Vec`s, must both be
//! caught, the second for the inner digest in particular.

use slh_dsa::{ParameterSet, SigningKey};
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering};
use std::sync::Mutex;

/// `SK.seed`, `SK.prf`, the two key blocks, and two inner digests.
const PATTERNS: usize = 6;
const NAMES: [&str; PATTERNS] = [
    "SK.seed",
    "SK.prf",
    "HMAC inner key block",
    "HMAC outer key block",
    "PRF_msg inner digest (hedged, with context)",
    "PRF_msg inner digest (deterministic)",
];
const LEN: usize = 16;

static WATCHING: AtomicBool = AtomicBool::new(false);
#[allow(clippy::declare_interior_mutable_const)]
const NONE: AtomicUsize = AtomicUsize::new(0);
static FOUND: [AtomicUsize; PATTERNS] = [NONE; PATTERNS];
#[allow(clippy::declare_interior_mutable_const)]
const ZERO: AtomicU8 = AtomicU8::new(0);
#[allow(clippy::declare_interior_mutable_const)]
const ROW: [AtomicU8; LEN] = [ZERO; LEN];
static WANTED: [[AtomicU8; LEN]; PATTERNS] = [ROW; PATTERNS];
/// One set at a time: the allocator is shared by the whole binary.
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

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
            for (pattern, count) in WANTED.iter().zip(FOUND.iter()) {
                let mut want = [0u8; LEN];
                for (w, p) in want.iter_mut().zip(pattern.iter()) {
                    *w = p.load(Ordering::Relaxed);
                }
                if block.windows(LEN).any(|w| w == want) {
                    count.fetch_add(1, Ordering::Relaxed);
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
/// held each.
fn freed_with(patterns: &[[u8; LEN]; PATTERNS], f: impl FnOnce()) -> [usize; PATTERNS] {
    for (slot, pattern) in WANTED.iter().zip(patterns.iter()) {
        for (s, p) in slot.iter().zip(pattern.iter()) {
            s.store(*p, Ordering::Relaxed);
        }
    }
    for count in &FOUND {
        count.store(0, Ordering::Relaxed);
    }
    WATCHING.store(true, Ordering::Relaxed);
    f();
    WATCHING.store(false, Ordering::Relaxed);
    core::array::from_fn(|i| FOUND[i].load(Ordering::Relaxed))
}

fn report(found: &[usize; PATTERNS]) -> Vec<String> {
    NAMES.iter().zip(found).filter(|(_, c)| **c > 0).map(|(n, c)| format!("{n}: {c} blocks")).collect()
}

/// HMAC-SHA-256 (n = 16) or HMAC-SHA-512 (otherwise) as the test's own
/// `Vec`-based code computes it, with the inner digest: `(inner, outer)`.
fn hmac(n: usize, sk_prf: &[u8], text: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let blk = if n == 16 { 64 } else { 128 };
    let mut ipad = vec![0x36u8; blk];
    let mut opad = vec![0x5cu8; blk];
    for i in 0..n {
        ipad[i] ^= sk_prf[i];
        opad[i] ^= sk_prf[i];
    }
    let hash = |m: &[u8]| -> Vec<u8> {
        if n == 16 {
            slhdsa::sha256::sha256(m).to_vec()
        } else {
            slhdsa::sha512::sha512(m).to_vec()
        }
    };
    ipad.extend_from_slice(text);
    let inner = hash(&ipad);
    opad.extend_from_slice(&inner);
    let outer = hash(&opad);
    (inner, outer)
}

/// `opt_rand ‖ 0 ‖ |ctx| ‖ ctx ‖ M`, the text `PRF_msg` authenticates.
fn prf_text(opt_rand: &[u8], ctx: &[u8], msg: &[u8]) -> Vec<u8> {
    let mut t = opt_rand.to_vec();
    t.extend_from_slice(&[0, ctx.len() as u8]);
    t.extend_from_slice(ctx);
    t.extend_from_slice(msg);
    t
}

fn first(bytes: &[u8]) -> [u8; LEN] {
    bytes[..LEN].try_into().unwrap()
}

fn check<P: ParameterSet>(name: &str, n: usize) {
    let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
    let mut seeds = vec![0u8; 3 * n];
    for (i, b) in seeds.iter_mut().enumerate() {
        *b = (i as u8).wrapping_mul(0x65).wrapping_add(0x11 + n as u8);
    }
    let (sk_seed, sk_prf, pk_seed) = (&seeds[0..n], &seeds[n..2 * n], &seeds[2 * n..3 * n]);
    let inner: [u8; LEN] = core::array::from_fn(|i| sk_prf[i] ^ 0x36);
    let outer: [u8; LEN] = core::array::from_fn(|i| sk_prf[i] ^ 0x5c);
    let message = vec![0x5au8; 3000];
    let rand = vec![9u8; n];
    let hedged_text = prf_text(&rand, b"context", &message);
    let det_text = prf_text(pk_seed, b"", &message);
    let (hedged_inner, hedged_r) = hmac(n, sk_prf, &hedged_text);
    let (det_inner, det_r) = hmac(n, sk_prf, &det_text);
    let patterns = [first(sk_seed), first(sk_prf), inner, outer, first(&hedged_inner), first(&det_inner)];

    let leaked = freed_with(&patterns, || {
        let key = SigningKey::<P>::slh_keygen_internal(sk_seed, sk_prf, pk_seed);
        let sig = key.try_sign_with_context(&message, b"context", Some(&rand)).unwrap();
        assert_eq!(&sig.to_bytes()[..n], &hedged_r[..n], "{name}: R is not the HMAC computed here");
        std::hint::black_box(&sig);
        let sig = key.try_sign_with_context(&message, b"", None).unwrap();
        assert_eq!(&sig.to_bytes()[..n], &det_r[..n], "{name}: R is not the HMAC computed here");
        std::hint::black_box(&sig);
        let copy = key.clone();
        let parsed = SigningKey::<P>::try_from(&key.to_bytes()[..]).unwrap();
        drop(key);
        drop(copy);
        drop(parsed);
    });
    assert!(leaked.iter().all(|c| *c == 0), "{name}: blocks freed with a secret still in them: {:?}", report(&leaked));

    // Control: a copy of the private key in a `Vec`, dropped as it is.
    let key = SigningKey::<P>::slh_keygen_internal(sk_seed, sk_prf, pk_seed);
    let leaked = freed_with(&patterns, || drop(std::hint::black_box(key.to_vec())));
    assert!(leaked[0] > 0 && leaked[1] > 0, "{name}: the allocator did not notice a freed copy of the key");

    // Control: HMAC with its key blocks and inner digest in growing `Vec`s,
    // as the verified crate's general HMAC computes it (and as `prf_msg`
    // used to): both key blocks and the inner digest must be caught.
    let leaked = freed_with(&patterns, || {
        if n == 16 {
            std::hint::black_box(slhdsa::sha256::hmac_sha256(sk_prf, &hedged_text));
        } else {
            std::hint::black_box(slhdsa::sha512::hmac_sha512(sk_prf, &hedged_text));
        }
    });
    assert!(leaked[2] > 0 && leaked[3] > 0, "{name}: the allocator did not notice HMAC's key blocks: {:?}", report(&leaked));
    assert!(leaked[4] > 0, "{name}: the allocator did not notice HMAC's inner digest: {:?}", report(&leaked));
    println!("{name}: nothing secret freed unwiped; controls caught: {:?}", report(&leaked));
}

#[test]
fn sha2_128s() {
    check::<slh_dsa::Sha2_128s>("SHA2-128s", 16);
}

#[test]
fn sha2_128f() {
    check::<slh_dsa::Sha2_128f>("SHA2-128f", 16);
}

#[test]
fn sha2_192s() {
    check::<slh_dsa::Sha2_192s>("SHA2-192s", 24);
}

#[test]
fn sha2_192f() {
    check::<slh_dsa::Sha2_192f>("SHA2-192f", 24);
}

#[test]
fn sha2_256s() {
    check::<slh_dsa::Sha2_256s>("SHA2-256s", 32);
}

#[test]
fn sha2_256f() {
    check::<slh_dsa::Sha2_256f>("SHA2-256f", 32);
}
