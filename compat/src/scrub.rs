//! Overwriting the stack that a secret computation used.
//!
//! The verified functions keep everything derived from the secret seed on
//! the stack (nothing secret is written to the heap), and the ones that work
//! with the seed are never inlined into their caller. So when one of them
//! returns, all its working storage lies directly below the caller's frame,
//! and a function called next from the same frame, with a local array at
//! least as large, lands on top of it.
//!
//! This cannot reach processor registers, and it relies on the compiler
//! laying frames out in the usual way; `tests/wipe.rs` checks the result on
//! the machine it runs on by searching the stack for the secrets afterwards.

use zeroize::Zeroize;

/// Bytes overwritten. Key generation followed by signing with the
/// recomputation was measured at about 14 KiB of stack in an optimised
/// AArch64 build; `tests/wipe.rs` prints the figure for the build it runs in
/// and fails if this is no longer enough. An unoptimised build uses more
/// stack and may not be covered.
pub const SCRUB_BYTES: usize = 64 * 1024;

/// Overwrite `SCRUB_BYTES` of stack below the caller's frame with zeros.
#[inline(never)]
pub(crate) fn scrub_stack() {
    let mut region = [0u8; SCRUB_BYTES];
    // Volatile writes: the compiler may not drop them although `region` is
    // never read.
    region.zeroize();
}
