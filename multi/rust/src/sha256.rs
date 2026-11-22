//! SHA-256 (FIPS 180-4) and HMAC-SHA-256 (FIPS 198-1).
//!
//! Written to mirror the standard as directly as possible: pad the whole
//! message, then compress block by block.

use alloc::vec::Vec;
const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

pub const H0: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

fn load_be32(data: &[u8], off: usize) -> u32 {
    ((data[off] as u32) << 24)
        | ((data[off + 1] as u32) << 16)
        | ((data[off + 2] as u32) << 8)
        | (data[off + 3] as u32)
}

/// The message schedule W[0..64] for the block at `data[off..off + 64]`.
fn schedule(data: &[u8], off: usize) -> [u32; 64] {
    let mut w = [0u32; 64];
    let mut i = 0;
    while i < 16 {
        w[i] = load_be32(data, off + 4 * i);
        i += 1;
    }
    while i < 64 {
        let x = w[i - 15];
        let y = w[i - 2];
        let s0 = x.rotate_right(7) ^ x.rotate_right(18) ^ (x >> 3);
        let s1 = y.rotate_right(17) ^ y.rotate_right(19) ^ (y >> 10);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        i += 1;
    }
    w
}

/// The SHA-256 compression function on the block at `data[off..off + 64]`.
///
/// With the opt-in `hw-sha2` feature, on a CPU that has the ARMv8 SHA-256
/// instructions, the result comes from [`hw`]; otherwise from
/// [`compress_portable`].
#[inline]
pub fn compress(state: &[u32; 8], data: &[u8], off: usize) -> [u32; 8] {
    #[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
    {
        if let Some(out) = hw::compress(state, data, off) {
            return out;
        }
    }
    compress_portable(state, data, off)
}

/// The compression function in portable code, as FIPS 180-4 writes it.
#[inline]
pub fn compress_portable(state: &[u32; 8], data: &[u8], off: usize) -> [u32; 8] {
    let w = schedule(data, off);
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];
    let mut i = 0;
    while i < 64 {
        let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
        let ch = (e & f) ^ (!e & g);
        let t1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
        let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
        let maj = (a & b) ^ (a & c) ^ (b & c);
        let t2 = s0.wrapping_add(maj);
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
        i += 1;
    }
    [
        state[0].wrapping_add(a),
        state[1].wrapping_add(b),
        state[2].wrapping_add(c),
        state[3].wrapping_add(d),
        state[4].wrapping_add(e),
        state[5].wrapping_add(f),
        state[6].wrapping_add(g),
        state[7].wrapping_add(h),
    ]
}

/// Append the SHA-256 padding to `msg`, for a message whose first `pre`
/// bytes (a multiple of 64) have already been compressed: the bit length
/// written at the end is that of the whole message, `pre + msg.len()`.
fn pad(msg: &[u8], pre: usize) -> Vec<u8> {
    let mut p: Vec<u8> = Vec::new();
    p.extend_from_slice(msg);
    p.push(0x80);
    while p.len() % 64 != 56 {
        p.push(0);
    }
    let bitlen = ((pre + msg.len()) as u64) * 8;
    p.push((bitlen >> 56) as u8);
    p.push((bitlen >> 48) as u8);
    p.push((bitlen >> 40) as u8);
    p.push((bitlen >> 32) as u8);
    p.push((bitlen >> 24) as u8);
    p.push((bitlen >> 16) as u8);
    p.push((bitlen >> 8) as u8);
    p.push(bitlen as u8);
    p
}

/// The big-endian serialisation of a hash state.
pub fn digest(state: &[u32; 8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut i = 0;
    while i < 8 {
        let s = state[i];
        out[4 * i] = (s >> 24) as u8;
        out[4 * i + 1] = (s >> 16) as u8;
        out[4 * i + 2] = (s >> 8) as u8;
        out[4 * i + 3] = s as u8;
        i += 1;
    }
    out
}

/// SHA-256 of `X ‖ msg`, given the state `state` reached after compressing
/// the `pre` bytes of `X` (a multiple of 64).
///
/// Whole blocks are compressed straight from `msg`; only what is left over
/// (under 64 bytes) is copied, together with the padding.
pub fn sha256_from(state: &[u32; 8], pre: usize, msg: &[u8]) -> [u8; 32] {
    let mut st = *state;
    let mut off = 0;
    while off + 64 <= msg.len() {
        st = compress(&st, msg, off);
        off += 64;
    }
    let p = pad(&msg[off..msg.len()], pre + off);
    let mut o = 0;
    while o < p.len() {
        st = compress(&st, &p, o);
        o += 64;
    }
    digest(&st)
}

pub fn sha256(msg: &[u8]) -> [u8; 32] {
    sha256_from(&H0, 0, msg)
}

/// HMAC-SHA-256 with a key of at most 64 bytes.
pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    let mut inner: Vec<u8> = Vec::new();
    let mut outer: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < 64 {
        let k = if i < key.len() { key[i] } else { 0 };
        inner.push(k ^ 0x36);
        outer.push(k ^ 0x5c);
        i += 1;
    }
    inner.extend_from_slice(msg);
    let ih = sha256(&inner);
    outer.extend_from_slice(&ih);
    sha256(&outer)
}

/// Whether [`compress`] is running on hardware SHA-256 instructions.
///
/// Exists only with the `hw-sha2` feature. `false` means the feature is on
/// but this CPU (or this architecture) has no backend, so the portable code
/// is in use.
#[cfg(feature = "hw-sha2")]
pub fn hw_active() -> bool {
    #[cfg(all(target_arch = "aarch64", target_endian = "little"))]
    {
        hw::arm::available()
    }
    #[cfg(not(all(target_arch = "aarch64", target_endian = "little")))]
    {
        false
    }
}

/// SHA-256 on the ARMv8 SHA-256 instructions.
///
/// Compiled only with the opt-in `hw-sha2` feature. It stands in for two
/// functions of the portable code, and everything else is the same code
/// either way. The build with the feature has its own translation and proofs
/// (`lean-hw/`), which show that
///
/// > whenever `hw::compress` returns `Some`, it holds what the portable code
/// > of [`compress`] returns for the same arguments, and whenever
/// > `hw::chain_blocks` returns `true`, it has left in `blocks` what the
/// > portable loops of [`crate::hash::chain_blocks`] leave there.
///
/// (That describes `../rust` and `../lean-hw`. The proofs for this tree's
/// kernel, which is generic in the hash length, are not written yet.)
///
/// The proofs cover this module except its submodule `arm`, the eighteen
/// functions that call the intrinsics; what those compute is taken from a
/// model of the instructions (`lean-hw/Arm.lean`). The crate's `unsafe` is in
/// those wrappers and at the two places below that enter the kernel after
/// testing that the CPU has the instructions.
///
/// `chain_blocks` is where the time goes: nearly every hash of SLH-DSA is one
/// step of it. The processor has a single unit for the SHA-256 round
/// instructions, each occupying it for two cycles, and one hash on its own
/// keeps that unit waiting, because each step needs the result of the one
/// before. So four chains are worked on at once, staggered a quarter of a
/// hash apart, and the unit always has a step ready. Two more savings apply
/// to a chain step: the first four rounds use only the first sixteen bytes of
/// the block, which a chain never changes, so they are done once per chain;
/// and for n = 16 only the first sixteen bytes of the result are kept,
/// which do not depend on the last update of the second half of the state.
///
/// In this tree the chain kernel is generic in the hash length `N` (16, 24
/// or 32): the value occupies block bytes 22..22 + N, so N/4 words of the
/// result are kept and, for N > 16, words 4.. of the value are carried in a
/// second vector. The wrappers in `arm` are the same as in `../rust`.
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
#[allow(unsafe_code)]
pub(crate) mod hw {
    use arm::V;

    /// A function of the kernel: compiled with the SHA-2 instructions enabled
    /// and inlined into its caller. Where the target has the instructions
    /// unconditionally that is `inline(always)`; elsewhere the function is
    /// marked `target_feature`, which rules `inline(always)` out, and its
    /// callers are responsible for the CPU having the features.
    macro_rules! kernel {
        ($($item:item)*) => {
            $(
                #[cfg_attr(target_feature = "sha2", inline(always))]
                #[cfg_attr(not(target_feature = "sha2"), inline, target_feature(enable = "neon,sha2"))]
                $item
            )*
        };
    }

    /// The instructions: each function is one to three intrinsics and nothing
    /// else. This is the only code Aeneas does not translate; the proofs take
    /// the meaning of these functions from the definitions in
    /// `lean-hw/Slhdsa/FunsExternal.lean`.
    #[allow(unused_unsafe)]
    pub(crate) mod arm {
        use core::arch::aarch64::*;

        /// Four 32-bit words; word 0 is the lowest lane.
        pub type V = uint32x4_t;

        /// Whether this CPU has the instructions. A compile-time `true` where
        /// the target guarantees them (as `aarch64-apple-darwin` does);
        /// otherwise `std` asks the operating system once and caches the answer.
        /// A target without an operating system has no way to ask: there the
        /// answer is whether the build itself was told the CPU has them
        /// (`-C target-feature=+sha2`), and `std` is not needed.
        #[inline]
        pub fn available() -> bool {
            #[cfg(any(target_os = "none", all(target_feature = "neon", target_feature = "sha2")))]
            {
                cfg!(all(target_feature = "neon", target_feature = "sha2"))
            }
            #[cfg(not(any(target_os = "none", all(target_feature = "neon", target_feature = "sha2"))))]
            {
                std::arch::is_aarch64_feature_detected!("neon") && std::arch::is_aarch64_feature_detected!("sha2")
            }
        }

        // SAFETY, for every function below: the caller has established that
        // the CPU has `neon` and `sha2` (see `kernel!`). The functions that
        // touch memory check their bounds first, and NEON loads and stores
        // have no alignment requirement.
        kernel! {
            /// `[0, 0, 0, 0]`.
            pub fn zero() -> V {
                unsafe { vdupq_n_u32(0) }
            }

            /// `[a, b, 0, 0]`.
            pub fn pair(a: u32, b: u32) -> V {
                unsafe { vsetq_lane_u32(b, vsetq_lane_u32(a, vdupq_n_u32(0), 0), 1) }
            }

            /// The words `w[at..at + 4]`.
            pub fn load_words(w: &[u32], at: usize) -> V {
                assert!(w.len() >= 4 && at <= w.len() - 4);
                unsafe { vld1q_u32(w.as_ptr().add(at)) }
            }

            /// The words of `a` followed by the words of `e`.
            pub fn store_words(a: V, e: V) -> [u32; 8] {
                let mut out = [0u32; 8];
                unsafe {
                    vst1q_u32(out.as_mut_ptr(), a);
                    vst1q_u32(out.as_mut_ptr().add(4), e);
                }
                out
            }

            /// The bytes `b[at..at + 16]` as four big-endian words.
            pub fn load_be(b: &[u8], at: usize) -> V {
                assert!(b.len() >= 16 && at <= b.len() - 16);
                unsafe { vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(b.as_ptr().add(at)))) }
            }

            /// Four words as sixteen big-endian bytes into `b[at..at + 16]`.
            pub fn store_be(b: &mut [u8], at: usize, v: V) {
                assert!(b.len() >= 16 && at <= b.len() - 16);
                unsafe { vst1q_u8(b.as_mut_ptr().add(at), vrev32q_u8(vreinterpretq_u8_u32(v))) }
            }

            /// Word-wise sum modulo 2^32.
            pub fn add(a: V, b: V) -> V {
                unsafe { vaddq_u32(a, b) }
            }

            /// Bitwise or.
            pub fn or(a: V, b: V) -> V {
                unsafe { vorrq_u32(a, b) }
            }

            /// Bitwise and.
            pub fn and(a: V, b: V) -> V {
                unsafe { vandq_u32(a, b) }
            }

            /// Every word shifted right by 16 bits.
            pub fn shr16(a: V) -> V {
                unsafe { vshrq_n_u32(a, 16) }
            }

            /// Every word shifted left by 16 bits.
            pub fn shl16(a: V) -> V {
                unsafe { vshlq_n_u32(a, 16) }
            }

            /// `[a[2], a[3], b[0], b[1]]`.
            pub fn ext2(a: V, b: V) -> V {
                unsafe { vextq_u32(a, b, 2) }
            }

            /// `[a[3], b[0], b[1], b[2]]`.
            pub fn ext3(a: V, b: V) -> V {
                unsafe { vextq_u32(a, b, 3) }
            }

            /// `SHA256H`: the first four working variables after four rounds.
            pub fn sha256h(abcd: V, efgh: V, wk: V) -> V {
                unsafe { vsha256hq_u32(abcd, efgh, wk) }
            }

            /// `SHA256H2`: the last four working variables after four rounds.
            pub fn sha256h2(efgh: V, abcd: V, wk: V) -> V {
                unsafe { vsha256h2q_u32(efgh, abcd, wk) }
            }

            /// `SHA256SU0`: the first half of four new schedule words.
            pub fn sha256su0(w0_3: V, w4_7: V) -> V {
                unsafe { vsha256su0q_u32(w0_3, w4_7) }
            }

            /// `SHA256SU1`: the second half of four new schedule words.
            pub fn sha256su1(tw0_3: V, w8_11: V, w12_15: V) -> V {
                unsafe { vsha256su1q_u32(tw0_3, w8_11, w12_15) }
            }
        }
    }

    /// The compression function on the block at `data[off..off + 64]`, or
    /// `None` if this CPU lacks the instructions.
    #[inline]
    #[allow(unused_unsafe)]
    pub fn compress(state: &[u32; 8], data: &[u8], off: usize) -> Option<[u32; 8]> {
        if !arm::available() {
            return None;
        }
        // The same bounds check, so the same panic, as the portable code.
        let mut block = [0u8; 64];
        block.copy_from_slice(&data[off..off + 64]);
        // SAFETY: `neon` and `sha2` were detected just above.
        Some(unsafe { compress_block(state, &block) })
    }

    kernel! {
        /// The compression function: sixteen steps of four rounds each.
        /// `abcd` and `efgh` hold the working variables, `m` the four most
        /// recent schedule vectors.
        fn compress_block(state: &[u32; 8], block: &[u8; 64]) -> [u32; 8] {
            let abcd0 = arm::load_words(state, 0);
            let efgh0 = arm::load_words(state, 4);
            let mut abcd = abcd0;
            let mut efgh = efgh0;
            let m0 = arm::load_be(block, 0);
            let m1 = arm::load_be(block, 16);
            let m2 = arm::load_be(block, 32);
            let m3 = arm::load_be(block, 48);
            let mut m = [m0, m1, m2, m3];
            let mut i = 0;
            while i < 16 {
                // Rounds 4i .. 4i+3, on W[4i..4i+4] + K[4i..4i+4].
                let w = arm::add(m[i % 4], arm::load_words(&super::K, 4 * i));
                let prev = abcd;
                abcd = arm::sha256h(abcd, efgh, w);
                efgh = arm::sha256h2(efgh, prev, w);
                // W[4i+16..4i+20], needed from step i + 4 on.
                if i < 12 {
                    m[i % 4] = arm::sha256su1(arm::sha256su0(m[i % 4], m[(i + 1) % 4]), m[(i + 2) % 4], m[(i + 3) % 4]);
                }
                i += 1;
            }
            arm::store_words(arm::add(abcd, abcd0), arm::add(efgh, efgh0))
        }
    }

    /// One chain being worked on: the parts of its block that stay fixed, the
    /// current `N`-byte value as big-endian words, and where it is.
    ///
    /// The value occupies bytes 22..22 + N: W5..W9 for N = 16, W5..W11 for
    /// N = 24, W5..W13 for N = 32, each time starting and ending in the middle
    /// of a word. The fixed words are the rest of the block with the value
    /// and the step counter cleared.
    #[derive(Clone, Copy)]
    struct Slot {
        /// W0..W3.
        m0: V,
        /// W4 with its low half (the top of the step counter) cleared; W5..W7 zero.
        c1: V,
        /// The fixed part of W8..W11 (for N = 16: W9's low half and W10, W11;
        /// for N = 24: W11's low half; for N = 32: nothing).
        c2: V,
        /// The fixed part of W12..W15 (for N = 32: W13's low half, W14, W15).
        c3: V,
        /// The value: block bytes 22..38.
        x: V,
        /// The rest of the value for N > 16: block bytes 38..38 + (N − 16),
        /// in the first N/4 − 4 words, the other words zero. Zero for N = 16.
        xb: V,
        /// For N = 24, the block bytes 46..54 that follow the value, in words
        /// 2 and 3 (words 0, 1 zero); zero otherwise. Written back with `xb`.
        tail: V,
        /// The working variables after rounds 0..3, which use only W0..W3
        /// and so are the same for every step of this chain.
        a1: V,
        e1: V,
        /// Next step to do, and the step to stop before.
        t: u32,
        end: u32,
        lane: usize,
    }

    /// Rounds 0..3 of the last block entered, with the bytes they came from.
    #[derive(Clone, Copy)]
    struct First {
        known: bool,
        head: [u8; 16],
        a1: V,
        e1: V,
    }

    /// The working variables of the four lanes during a run.
    struct Lanes {
        /// The value going into each lane's current step.
        x: [V; 4],
        /// Its words 4..N/4 (N > 16).
        xb: [V; 4],
        abcd: [V; 4],
        efgh: [V; 4],
        /// The four most recent schedule vectors of each lane.
        m: [[V; 4]; 4],
    }

    const MASK1: [u32; 4] = [0xffff_0000, 0, 0, 0];
    /// The fixed part of W8..W11 for N = 16, and of W12..W15 for N = 32.
    const MASK2: [u32; 4] = [0, 0x0000_ffff, 0xffff_ffff, 0xffff_ffff];
    /// The fixed part of W8..W11 for N = 24.
    const MASK2_24: [u32; 4] = [0, 0, 0, 0x0000_ffff];
    const ALL: [u32; 4] = [0xffff_ffff; 4];
    const LOW2: [u32; 4] = [0xffff_ffff, 0xffff_ffff, 0, 0];
    const HIGH2: [u32; 4] = [0, 0, 0xffff_ffff, 0xffff_ffff];

    /// [`crate::hash::chain_blocks`], four chains at a time, or `false` if
    /// this CPU lacks the instructions (or the arguments are ones the
    /// portable code panics on, which is then left to it, or `N` is not one
    /// of 16, 24, 32).
    #[inline]
    #[allow(unused_unsafe)]
    pub fn chain_blocks<const N: usize>(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) -> bool {
        if !(N == 16 || N == 24 || N == 32) || !arm::available() || start.len() < blocks.len() || end.len() < blocks.len() {
            return false;
        }
        // SAFETY: `neon` and `sha2` were detected just above.
        unsafe { chain_all::<N>(state, blocks, start, end) };
        true
    }

    kernel! {
        /// Chains are taken in order into four slots. The slots run until the
        /// first of them has no steps left; finished chains are written back
        /// to their blocks and the free slots take the next chains.
        fn chain_all<const N: usize>(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) {
            let z = arm::zero();
            let mut slots = [Slot { m0: z, c1: z, c2: z, c3: z, x: z, xb: z, tail: z, a1: z, e1: z, t: 0, end: 0, lane: 0 }; 4];
            let mut first = First { known: false, head: [0u8; 16], a1: z, e1: z };
            let mut n = 0;
            let mut next = 0;
            loop {
                // Give every free slot the next chain that has steps to do.
                while n < 4 && next < blocks.len() {
                    if start[next] < end[next] {
                        slots[n] = enter::<N>(state, &blocks[next], start[next], end[next], next, &mut first);
                        n += 1;
                    }
                    next += 1;
                }
                if n == 0 {
                    break;
                }
                // Run until the first of them is finished.
                let mut r = slots[0].end - slots[0].t;
                let mut j = 1;
                while j < n {
                    let left = slots[j].end - slots[j].t;
                    if left < r {
                        r = left;
                    }
                    j += 1;
                }
                if n == 4 {
                    run::<N, 4>(state, &mut slots, r);
                } else if n == 3 {
                    run::<N, 3>(state, &mut slots, r);
                } else if n == 2 {
                    run::<N, 2>(state, &mut slots, r);
                } else {
                    run::<N, 1>(state, &mut slots, r);
                }
                // Write back the finished chains and close the gaps.
                let mut k = 0;
                let mut j = 0;
                while j < n {
                    if slots[j].t < slots[j].end {
                        slots[k] = slots[j];
                        k += 1;
                    } else {
                        leave::<N>(&slots[j], &mut blocks[slots[j].lane]);
                    }
                    j += 1;
                }
                n = k;
            }
        }

        /// A chain into a slot: the fixed words of its block, its value, and
        /// rounds 0..3, which are taken from `first` if the block starts with
        /// the same sixteen bytes as the last one entered.
        fn enter<const N: usize>(state: &[u32; 8], block: &[u8; 64], t: u32, end: u32, lane: usize, first: &mut First) -> Slot {
            let m0 = arm::load_be(block, 0);
            let mut head = [0u8; 16];
            head.copy_from_slice(&block[0..16]);
            if !(first.known && first.head == head) {
                let abcd0 = arm::load_words(state, 0);
                let efgh0 = arm::load_words(state, 4);
                let w = arm::add(m0, arm::load_words(&super::K, 0));
                first.known = true;
                first.head = head;
                first.a1 = arm::sha256h(abcd0, efgh0, w);
                first.e1 = arm::sha256h2(efgh0, abcd0, w);
            }
            let z = arm::zero();
            // Masks of the fixed parts of W8..W11 and W12..W15, of the value's
            // words in bytes 38..54, and of what follows the value there.
            let (k2, k3, kb, kt) = if N == 16 {
                (MASK2, ALL, [0u32; 4], [0u32; 4])
            } else if N == 24 {
                (MASK2_24, ALL, LOW2, HIGH2)
            } else {
                ([0u32; 4], MASK2, ALL, [0u32; 4])
            };
            let (xb, tail) = if N == 16 {
                (z, z)
            } else {
                let b = arm::load_be(block, 38);
                (arm::and(b, arm::load_words(&kb, 0)), arm::and(b, arm::load_words(&kt, 0)))
            };
            Slot {
                m0,
                c1: arm::and(arm::load_be(block, 16), arm::load_words(&MASK1, 0)),
                c2: arm::and(arm::load_be(block, 32), arm::load_words(&k2, 0)),
                c3: arm::and(arm::load_be(block, 48), arm::load_words(&k3, 0)),
                x: arm::load_be(block, 22),
                xb,
                tail,
                a1: first.a1,
                e1: first.e1,
                t,
                end,
                lane,
            }
        }

        /// A finished chain back to its block: the value, and the counter of
        /// the last step done (which is what the portable code leaves there).
        /// The slot has done at least one step.
        fn leave<const N: usize>(slot: &Slot, block: &mut [u8; 64]) {
            let t = slot.t - 1;
            block[18] = (t >> 24) as u8;
            block[19] = (t >> 16) as u8;
            block[20] = (t >> 8) as u8;
            block[21] = t as u8;
            if N > 16 {
                arm::store_be(block, 38, arm::or(slot.xb, slot.tail));
            }
            arm::store_be(block, 22, slot.x);
        }

        /// One lane's share of one tick, if the lane is running. Lane `LANE`
        /// of `L` runs `15·LANE/L` ticks behind lane 0. `PHASE` 0 is the first
        /// period of a run (a lane joins at its offset), 1 a middle period, 2
        /// the last (a lane that joined late finishes its last hash).
        fn lane_tick<const N: usize, const L: usize, const PHASE: usize, const J: usize, const LANE: usize>(
            abcd0: V,
            efgh0: V,
            slots: &[Slot; 4],
            p: u32,
            s: &mut Lanes,
        ) {
            if LANE < L {
                let off = (15 * LANE) / L;
                if PHASE == 0 {
                    if J >= off {
                        lane_step::<N, L, J, LANE>(abcd0, efgh0, slots, p, s);
                    }
                } else if PHASE == 1 {
                    lane_step::<N, L, J, LANE>(abcd0, efgh0, slots, p, s);
                } else if J < off {
                    lane_step::<N, L, J, LANE>(abcd0, efgh0, slots, p, s);
                }
            }
        }

        /// Step `i` (1..=15) of a lane's current hash, with the work that
        /// starts a hash before step 1 and the work that ends one after step
        /// 15. `p` is the number of the period, which is the number of the
        /// hash a lane starts in it.
        fn lane_step<const N: usize, const L: usize, const J: usize, const LANE: usize>(
            abcd0: V,
            efgh0: V,
            slots: &[Slot; 4],
            p: u32,
            s: &mut Lanes,
        ) {
            let off = (15 * LANE) / L;
            let i = (J + 15 - off) % 15 + 1;
            if i == 1 {
                // A new hash. The value sits 16 bits off the word boundaries
                // (bytes 22..22 + N), after the step counter.
                let z = arm::zero();
                let t = slots[LANE].t + p;
                let hi = arm::shr16(s.x[LANE]);
                let lo = arm::shl16(s.x[LANE]);
                let m1 = arm::or(
                    arm::or(slots[LANE].c1, arm::pair(t >> 16, t << 16)),
                    arm::or(arm::ext3(z, hi), arm::ext2(z, lo)),
                );
                // W8..W11 and W12..W15. For N > 16 the value's words 4..
                // continue into W9..W11 (N = 24) or W9..W13 (N = 32).
                let (m2, m3) = if N == 16 {
                    (arm::or(slots[LANE].c2, arm::or(arm::ext2(lo, z), arm::ext3(hi, z))), slots[LANE].c3)
                } else {
                    let hib = arm::shr16(s.xb[LANE]);
                    let lob = arm::shl16(s.xb[LANE]);
                    let m2 = arm::or(slots[LANE].c2, arm::or(arm::ext2(lo, lob), arm::ext3(hi, hib)));
                    if N == 24 {
                        (m2, slots[LANE].c3)
                    } else {
                        (m2, arm::or(slots[LANE].c3, arm::or(arm::ext2(lob, z), arm::ext3(hib, z))))
                    }
                };
                // Rounds 0..3 are already done; W16..W19 are still wanted.
                s.abcd[LANE] = slots[LANE].a1;
                s.efgh[LANE] = slots[LANE].e1;
                s.m[LANE] = [arm::sha256su1(arm::sha256su0(slots[LANE].m0, m1), m2, m3), m1, m2, m3];
            }
            let w = arm::add(s.m[LANE][i % 4], arm::load_words(&super::K, 4 * i));
            let prev = s.abcd[LANE];
            s.abcd[LANE] = arm::sha256h(prev, s.efgh[LANE], w);
            // For N = 16 only the first four words of the result are kept, so
            // the last update of the other four is not needed.
            if i < 15 || N > 16 {
                s.efgh[LANE] = arm::sha256h2(s.efgh[LANE], prev, w);
            }
            if i < 12 {
                s.m[LANE][i % 4] = arm::sha256su1(
                    arm::sha256su0(s.m[LANE][i % 4], s.m[LANE][(i + 1) % 4]),
                    s.m[LANE][(i + 2) % 4],
                    s.m[LANE][(i + 3) % 4],
                );
            }
            if i == 15 {
                s.x[LANE] = arm::add(s.abcd[LANE], abcd0);
                if N == 24 {
                    s.xb[LANE] = arm::and(arm::add(s.efgh[LANE], efgh0), arm::load_words(&LOW2, 0));
                } else if N > 24 {
                    s.xb[LANE] = arm::add(s.efgh[LANE], efgh0);
                }
            }
        }

        /// One tick: every lane takes one step.
        fn tick<const N: usize, const L: usize, const PHASE: usize, const J: usize>(
            abcd0: V,
            efgh0: V,
            slots: &[Slot; 4],
            p: u32,
            s: &mut Lanes,
        ) {
            lane_tick::<N, L, PHASE, J, 0>(abcd0, efgh0, slots, p, s);
            lane_tick::<N, L, PHASE, J, 1>(abcd0, efgh0, slots, p, s);
            lane_tick::<N, L, PHASE, J, 2>(abcd0, efgh0, slots, p, s);
            lane_tick::<N, L, PHASE, J, 3>(abcd0, efgh0, slots, p, s);
        }

        /// One period of fifteen ticks.
        fn period<const N: usize, const L: usize, const PHASE: usize>(
            abcd0: V,
            efgh0: V,
            slots: &[Slot; 4],
            p: u32,
            s: &mut Lanes,
        ) {
            tick::<N, L, PHASE, 0>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 1>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 2>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 3>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 4>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 5>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 6>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 7>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 8>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 9>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 10>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 11>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 12>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 13>(abcd0, efgh0, slots, p, s);
            tick::<N, L, PHASE, 14>(abcd0, efgh0, slots, p, s);
        }
    }

    /// `steps` steps of the first `L` slots (`1 <= L <= 4`, `steps >= 1`,
    /// each slot with at least `steps` steps left), entirely in registers:
    /// each step rebuilds the words W4.. that hold the counter and the value
    /// (W4..W9 for N = 16, W4..W11 for N = 24, W4..W13 for N = 32),
    /// compresses, and keeps the first N/4 words of the result as the next
    /// value.
    ///
    /// The round instructions of all lanes go through one execution unit, and
    /// a lane has nothing for it while it turns one hash into the next. So
    /// the lanes are staggered: lane `l` runs `15·l/L` steps behind lane 0,
    /// and no two lanes are between hashes at the same time.
    #[inline]
    #[cfg_attr(not(target_feature = "sha2"), target_feature(enable = "neon,sha2"))]
    fn run<const N: usize, const L: usize>(state: &[u32; 8], slots: &mut [Slot; 4], steps: u32) {
        let abcd0 = arm::load_words(state, 0);
        let efgh0 = arm::load_words(state, 4);
        let z = arm::zero();
        let mut s = Lanes {
            x: [slots[0].x, slots[1].x, slots[2].x, slots[3].x],
            xb: [slots[0].xb, slots[1].xb, slots[2].xb, slots[3].xb],
            abcd: [z; 4],
            efgh: [z; 4],
            m: [[z; 4]; 4],
        };
        period::<N, L, 0>(abcd0, efgh0, slots, 0, &mut s);
        let mut p: u32 = 1;
        while p < steps {
            period::<N, L, 1>(abcd0, efgh0, slots, p, &mut s);
            p += 1;
        }
        period::<N, L, 2>(abcd0, efgh0, slots, p, &mut s);
        if 0 < L {
            slots[0] = advanced(&slots[0], s.x[0], s.xb[0], steps);
        }
        if 1 < L {
            slots[1] = advanced(&slots[1], s.x[1], s.xb[1], steps);
        }
        if 2 < L {
            slots[2] = advanced(&slots[2], s.x[2], s.xb[2], steps);
        }
        if 3 < L {
            slots[3] = advanced(&slots[3], s.x[3], s.xb[3], steps);
        }
    }

    /// The slot after `steps` more steps that left it at value `x`, `xb`.
    #[inline]
    fn advanced(slot: &Slot, x: V, xb: V, steps: u32) -> Slot {
        Slot { x, xb, t: slot.t + steps, ..*slot }
    }

    /// What each wrapper of [`arm`] returns on this processor, against the
    /// record in `vectors/arm-wrappers.txt`. The Lean model of the wrappers
    /// (`lean-hw/Slhdsa/FunsExternal.lean`) is run on the same file
    /// (`lean-hw/ArmTest.lean`), so the two agree on every case recorded.
    /// `ARM_VECTORS_WRITE=1` rewrites the file from this processor.
    #[cfg(test)]
    mod vectors {
        use super::arm::{self, V};
        use std::fmt::Write as _;
        use std::{format, string::String, vec::Vec};

        /// SplitMix64, so the cases are the same on every run.
        struct Rng(u64);
        impl Rng {
            fn next(&mut self) -> u64 {
                self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
                let mut z = self.0;
                z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
                z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
                z ^ (z >> 31)
            }
            /// A word that is often all zeros, all ones or a single bit.
            fn word(&mut self) -> u32 {
                match self.next() % 8 {
                    0 => 0,
                    1 => u32::MAX,
                    2 => 1 << (self.next() % 32),
                    _ => self.next() as u32,
                }
            }
            fn v(&mut self) -> [u32; 4] {
                [self.word(), self.word(), self.word(), self.word()]
            }
        }

        // The vector type is four `u32` in lane order; these two do not go
        // through the wrappers under test.
        fn v(w: [u32; 4]) -> V {
            unsafe { core::mem::transmute(w) }
        }
        fn w(v: V) -> [u32; 4] {
            unsafe { core::mem::transmute(v) }
        }
        fn words(ws: &[u32]) -> String {
            ws.iter().map(|x| format!("{x:08x}")).collect::<Vec<_>>().join(",")
        }
        fn hex(bs: &[u8]) -> String {
            bs.iter().map(|x| format!("{x:02x}")).collect()
        }

        /// Every case as a line `name args = result`.
        #[allow(unused_unsafe)]
        fn cases() -> String {
            let mut rng = Rng(0x41524d5f56454353);
            let mut out = String::new();
            unsafe {
                writeln!(out, "zero = {}", words(&w(arm::zero()))).unwrap();
                for _ in 0..48 {
                    let (a, b) = (rng.word(), rng.word());
                    writeln!(out, "pair {a:08x} {b:08x} = {}", words(&w(arm::pair(a, b)))).unwrap();
                }
                for _ in 0..48 {
                    let len = 4 + (rng.next() % 9) as usize;
                    let ws: Vec<u32> = (0..len).map(|_| rng.word()).collect();
                    let at = (rng.next() as usize) % (len - 3);
                    writeln!(out, "load_words {} {at} = {}", words(&ws), words(&w(arm::load_words(&ws, at)))).unwrap();
                }
                for _ in 0..48 {
                    let (a, e) = (rng.v(), rng.v());
                    writeln!(out, "store_words {} {} = {}", words(&a), words(&e), words(&arm::store_words(v(a), v(e)))).unwrap();
                }
                for _ in 0..64 {
                    let len = 16 + (rng.next() % 49) as usize;
                    let bs: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
                    let at = (rng.next() as usize) % (len - 15);
                    writeln!(out, "load_be {} {at} = {}", hex(&bs), words(&w(arm::load_be(&bs, at)))).unwrap();
                }
                for _ in 0..64 {
                    let len = 16 + (rng.next() % 49) as usize;
                    let mut bs: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
                    let at = (rng.next() as usize) % (len - 15);
                    let x = rng.v();
                    let before = hex(&bs);
                    arm::store_be(&mut bs, at, v(x));
                    writeln!(out, "store_be {before} {at} {} = {}", words(&x), hex(&bs)).unwrap();
                }
                for _ in 0..64 {
                    let a = rng.v();
                    writeln!(out, "shr16 {} = {}", words(&a), words(&w(arm::shr16(v(a))))).unwrap();
                    writeln!(out, "shl16 {} = {}", words(&a), words(&w(arm::shl16(v(a))))).unwrap();
                }
                for _ in 0..96 {
                    let (a, b) = (rng.v(), rng.v());
                    writeln!(out, "add {} {} = {}", words(&a), words(&b), words(&w(arm::add(v(a), v(b))))).unwrap();
                    writeln!(out, "or {} {} = {}", words(&a), words(&b), words(&w(arm::or(v(a), v(b))))).unwrap();
                    writeln!(out, "and {} {} = {}", words(&a), words(&b), words(&w(arm::and(v(a), v(b))))).unwrap();
                    writeln!(out, "ext2 {} {} = {}", words(&a), words(&b), words(&w(arm::ext2(v(a), v(b))))).unwrap();
                    writeln!(out, "ext3 {} {} = {}", words(&a), words(&b), words(&w(arm::ext3(v(a), v(b))))).unwrap();
                    writeln!(out, "sha256su0 {} {} = {}", words(&a), words(&b), words(&w(arm::sha256su0(v(a), v(b))))).unwrap();
                }
                for _ in 0..256 {
                    let (a, b, c) = (rng.v(), rng.v(), rng.v());
                    writeln!(out, "sha256h {} {} {} = {}", words(&a), words(&b), words(&c), words(&w(arm::sha256h(v(a), v(b), v(c))))).unwrap();
                    writeln!(out, "sha256h2 {} {} {} = {}", words(&a), words(&b), words(&c), words(&w(arm::sha256h2(v(a), v(b), v(c))))).unwrap();
                    writeln!(out, "sha256su1 {} {} {} = {}", words(&a), words(&b), words(&c), words(&w(arm::sha256su1(v(a), v(b), v(c))))).unwrap();
                }
            }
            out
        }

        #[test]
        fn arm_wrappers_match_the_record() {
            assert!(arm::available(), "this test needs a CPU with the SHA-256 instructions");
            let path = concat!(env!("CARGO_MANIFEST_DIR"), "/../../vectors/arm-wrappers.txt");
            let now = cases();
            if std::env::var_os("ARM_VECTORS_WRITE").is_some() {
                std::fs::write(path, &now).unwrap();
            }
            let recorded = std::fs::read_to_string(path).unwrap();
            assert_eq!(recorded.lines().count(), now.lines().count());
            for (i, (r, n)) in recorded.lines().zip(now.lines()).enumerate() {
                assert_eq!(r, n, "line {}", i + 1);
            }
        }
    }
}
