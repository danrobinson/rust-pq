//! Small byte-manipulation helpers.

use alloc::vec::Vec;
use crate::params::N;

/// The `i`-th `N`-byte block of `s`.
pub fn block(s: &[u8], i: usize) -> [u8; N] {
    let mut out = [0u8; N];
    out.copy_from_slice(&s[i * N..i * N + N]);
    out
}

/// FIPS 205 Algorithm 2, `toInt`: big-endian bytes to integer (at most 8 bytes).
pub fn to_int(x: &[u8]) -> u64 {
    let mut total: u64 = 0;
    let mut i = 0;
    while i < x.len() {
        total = (total << 8) | (x[i] as u64);
        i += 1;
    }
    total
}

/// FIPS 205 Algorithm 4, `base_2^b`, for `b <= 16`.
///
/// The standard keeps `total` as an unbounded integer; only its low
/// `bits <= b + 7` bits are ever read, so a `u32` suffices.
pub fn base_2b(x: &[u8], b: u32, out_len: usize) -> Vec<u32> {
    let mut input: usize = 0;
    let mut bits: u32 = 0;
    let mut total: u32 = 0;
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < out_len {
        while bits < b {
            total = (total << 8) | (x[input] as u32);
            input += 1;
            bits += 8;
        }
        bits -= b;
        out.push((total >> bits) & ((1u32 << b) - 1));
        i += 1;
    }
    out
}
