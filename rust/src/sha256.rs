//! SHA-256 (FIPS 180-4) and HMAC-SHA-256 (FIPS 198-1).
//!
//! Written to mirror the standard as directly as possible: pad the whole
//! message, then compress block by block.

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
/// instructions, the result comes from [`hw`] instead of the code below.
#[inline]
pub fn compress(state: &[u32; 8], data: &[u8], off: usize) -> [u32; 8] {
    #[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
    {
        if let Some(out) = hw::compress(state, data, off) {
            return out;
        }
    }
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
        hw::available()
    }
    #[cfg(not(all(target_arch = "aarch64", target_endian = "little")))]
    {
        false
    }
}

/// SHA-256 on the ARMv8 SHA-256 instructions.
///
/// Compiled only with the opt-in `hw-sha2` feature. This module is the only
/// `unsafe` code in the crate and is **not covered by the Lean proofs**:
/// Aeneas translates the default build, in which this module does not exist.
/// It stands in for two functions of the verified code, and everything else
/// is the same code either way. So a build with the feature computes what the
/// verified build computes provided that
///
/// > whenever `hw::compress` returns `Some`, it holds what the portable code
/// > of [`compress`] returns for the same arguments, and whenever
/// > `hw::chain_blocks` returns `true`, it has left in `blocks` what the
/// > portable loops of [`crate::hash::chain_blocks`] leave there.
///
/// That statement is tested (`tests/compress.rs` and the ACVP vectors, run
/// with the feature on) but not proved.
///
/// `chain_blocks` is where the time goes: nearly every hash of SLH-DSA is one
/// step of it. The processor has a single unit for the SHA-256 round
/// instructions, each occupying it for two cycles, and one hash on its own
/// keeps that unit waiting, because each step needs the result of the one
/// before. So four chains are worked on at once, staggered a quarter of a
/// hash apart, and the unit always has a step ready. Two more savings apply
/// to a chain step: the first four rounds use only the first sixteen bytes of
/// the block, which a chain never changes, so they are done once per chain;
/// and only the first sixteen bytes of the result are kept, which do not
/// depend on the last update of the second half of the state.
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
#[allow(unsafe_code)]
pub(crate) mod hw {
    use core::arch::aarch64::*;

    /// Whether this CPU has the instructions. A compile-time `true` where the
    /// target guarantees them (as `aarch64-apple-darwin` does); otherwise
    /// `std` asks the operating system once and caches the answer.
    #[inline]
    pub fn available() -> bool {
        std::arch::is_aarch64_feature_detected!("neon") && std::arch::is_aarch64_feature_detected!("sha2")
    }

    /// The compression function on the block at `data[off..off + 64]`, or
    /// `None` if this CPU lacks the instructions.
    #[inline]
    pub fn compress(state: &[u32; 8], data: &[u8], off: usize) -> Option<[u32; 8]> {
        if !available() {
            return None;
        }
        // The same bounds check, so the same panic, as the portable code.
        let block: &[u8; 64] = data[off..off + 64].try_into().unwrap();
        // SAFETY: `neon` and `sha2` were detected just above.
        Some(unsafe { compress_block(state, block) })
    }

    /// The compression function: sixteen steps of four rounds each. `abcd`
    /// and `efgh` hold the working variables, `m` the four most recent
    /// schedule vectors.
    ///
    /// # Safety
    /// The CPU must support the `neon` and `sha2` target features.
    #[inline]
    #[target_feature(enable = "neon,sha2")]
    unsafe fn compress_block(state: &[u32; 8], block: &[u8; 64]) -> [u32; 8] {
        // SAFETY, for every load and store below: each touches 16 bytes that
        // lie inside a fixed-size array borrowed for the whole call (`state`
        // and `out` are 32 bytes, `block` is 64, `K` is 256), and NEON loads
        // and stores have no alignment requirement.
        unsafe {
            let abcd0 = vld1q_u32(state.as_ptr());
            let efgh0 = vld1q_u32(state.as_ptr().add(4));
            let mut abcd = abcd0;
            let mut efgh = efgh0;
            // Big-endian words from little-endian memory: reverse each 4 bytes.
            let p = block.as_ptr();
            let mut m = [
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(16)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(32)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(48)))),
            ];
            let mut i = 0;
            while i < 16 {
                // Rounds 4i .. 4i+3, on W[4i..4i+4] + K[4i..4i+4].
                let w = vaddq_u32(m[i % 4], vld1q_u32(super::K.as_ptr().add(4 * i)));
                let prev = abcd;
                abcd = vsha256hq_u32(abcd, efgh, w);
                efgh = vsha256h2q_u32(efgh, prev, w);
                // W[4i+16..4i+20], needed from step i + 4 on.
                if i < 12 {
                    m[i % 4] = vsha256su1q_u32(vsha256su0q_u32(m[i % 4], m[(i + 1) % 4]), m[(i + 2) % 4], m[(i + 3) % 4]);
                }
                i += 1;
            }
            let mut out = [0u32; 8];
            vst1q_u32(out.as_mut_ptr(), vaddq_u32(abcd, abcd0));
            vst1q_u32(out.as_mut_ptr().add(4), vaddq_u32(efgh, efgh0));
            out
        }
    }

    /// One chain being worked on: the parts of its block that stay fixed, the
    /// current 16-byte value as four big-endian words, and where it is.
    #[derive(Clone, Copy)]
    struct Slot {
        /// W0..W3.
        m0: uint32x4_t,
        /// W4 with its low half (the top of the step counter) cleared; W5..W7 zero.
        c1: uint32x4_t,
        /// W9's low half and W10, W11: the padding after the value; W8 zero.
        c2: uint32x4_t,
        /// W12..W15.
        m3: uint32x4_t,
        /// The value: block bytes 22..38.
        x: uint32x4_t,
        /// The working variables after rounds 0..3, which use only W0..W3
        /// and so are the same for every step of this chain.
        a1: uint32x4_t,
        e1: uint32x4_t,
        /// Next step to do, and the step to stop before.
        t: u32,
        end: u32,
        lane: usize,
    }

    /// [`crate::hash::chain_blocks`], four chains at a time, or `false` if
    /// this CPU lacks the instructions (or the arguments are ones the
    /// portable code panics on, which is then left to it).
    ///
    /// Chains are taken in order into four slots. The slots run until the
    /// first of them has no steps left; finished chains are written back to
    /// their blocks and the free slots take the next chains.
    #[inline]
    #[allow(non_snake_case)]
    pub fn chain_blocks(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) -> bool {
        let M = blocks.len();
        if !available() || start.len() < M || end.len() < M {
            return false;
        }
        // SAFETY: `neon` was detected just above.
        let zero = unsafe { vdupq_n_u32(0) };
        let mut slots = [Slot { m0: zero, c1: zero, c2: zero, m3: zero, x: zero, a1: zero, e1: zero, t: 0, end: 0, lane: 0 }; 4];
        // Rounds 0..3 of the last block entered, with the bytes they came from.
        let mut first: Option<([u8; 16], uint32x4_t, uint32x4_t)> = None;
        let mut n = 0;
        let mut next = 0;
        loop {
            // Give every free slot the next chain that has steps to do.
            while n < 4 && next < M {
                if start[next] < end[next] {
                    // SAFETY: `neon` detected; `blocks[next]` is 64 bytes.
                    slots[n] = unsafe { enter(state, &blocks[next], start[next], end[next], next, &mut first) };
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
                r = r.min(slots[j].end - slots[j].t);
                j += 1;
            }
            // SAFETY: `neon` and `sha2` detected; the first `n` slots are in use.
            unsafe {
                match n {
                    4 => run::<4>(state, &mut slots, r),
                    3 => run::<3>(state, &mut slots, r),
                    2 => run::<2>(state, &mut slots, r),
                    _ => run::<1>(state, &mut slots, r),
                }
            }
            // Write back the finished chains and close the gaps.
            let mut k = 0;
            let mut j = 0;
            while j < n {
                if slots[j].t < slots[j].end {
                    slots[k] = slots[j];
                    k += 1;
                } else {
                    // SAFETY: `neon` detected; `lane < M`.
                    unsafe { leave(&slots[j], &mut blocks[slots[j].lane]) };
                }
                j += 1;
            }
            n = k;
        }
        true
    }

    /// # Safety
    /// `neon` and `sha2` are available.
    #[inline]
    #[target_feature(enable = "neon,sha2")]
    unsafe fn enter(
        state: &[u32; 8],
        block: &[u8; 64],
        t: u32,
        end: u32,
        lane: usize,
        first: &mut Option<([u8; 16], uint32x4_t, uint32x4_t)>,
    ) -> Slot {
        // SAFETY: every load is 16 bytes inside the 64-byte block, `state` or `K`.
        unsafe {
            let p = block.as_ptr();
            let be = |q: *const u8| vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(q)));
            let mask1 = vld1q_u32([0xffff_0000u32, 0, 0, 0].as_ptr());
            let mask2 = vld1q_u32([0u32, 0x0000_ffff, 0xffff_ffff, 0xffff_ffff].as_ptr());
            let m0 = be(p);
            let head: [u8; 16] = block[0..16].try_into().unwrap();
            let (a1, e1) = match *first {
                Some((h, a1, e1)) if h == head => (a1, e1),
                _ => {
                    let abcd0 = vld1q_u32(state.as_ptr());
                    let efgh0 = vld1q_u32(state.as_ptr().add(4));
                    let w = vaddq_u32(m0, vld1q_u32(super::K.as_ptr()));
                    let a1 = vsha256hq_u32(abcd0, efgh0, w);
                    let e1 = vsha256h2q_u32(efgh0, abcd0, w);
                    *first = Some((head, a1, e1));
                    (a1, e1)
                }
            };
            Slot {
                m0,
                c1: vandq_u32(be(p.add(16)), mask1),
                c2: vandq_u32(be(p.add(32)), mask2),
                m3: be(p.add(48)),
                x: be(p.add(22)),
                a1,
                e1,
                t,
                end,
                lane,
            }
        }
    }

    /// A finished chain back to its block: the value, and the counter of the
    /// last step done (which is what the portable code leaves there).
    ///
    /// # Safety
    /// `neon` is available; the slot has done at least one step.
    #[inline]
    #[target_feature(enable = "neon")]
    unsafe fn leave(slot: &Slot, block: &mut [u8; 64]) {
        block[18..22].copy_from_slice(&(slot.t - 1).to_be_bytes());
        // SAFETY: 16 bytes at offset 22 of a 64-byte block.
        unsafe { vst1q_u8(block.as_mut_ptr().add(22), vrev32q_u8(vreinterpretq_u8_u32(slot.x))) };
    }

    /// One lane's share of one tick: step `i` (1..=15) of its current hash,
    /// with the work that starts a hash before step 1 and the work that ends
    /// one after step 15. `$phase` 0 is the first period of a run (a lane
    /// joins at its offset), 1 a middle period, 2 the last (a lane that
    /// joined late finishes its last hash).
    macro_rules! lane_tick {
        ($L:expr, $phase:expr, $j:expr, $lane:expr,
         ($slots:ident, $p:ident, $abcd0:ident, $zero:ident, $x:ident, $abcd:ident, $efgh:ident, $m:ident)) => {
            if $lane < $L {
                let off: usize = (15 * $lane) / $L;
                let live = match $phase {
                    0 => $j >= off,
                    1 => true,
                    _ => $j < off,
                };
                if live {
                    let i: usize = ($j + 15 - off) % 15 + 1;
                    if i == 1 {
                        // A new hash. The value sits 16 bits off the word
                        // boundaries (bytes 22..38), after the step counter.
                        let t = $slots[$lane].t + $p;
                        let tv = vsetq_lane_u32(t << 16, vsetq_lane_u32(t >> 16, $zero, 0), 1);
                        let hi = vshrq_n_u32($x[$lane], 16);
                        let lo = vshlq_n_u32($x[$lane], 16);
                        let m1 = vorrq_u32(
                            vorrq_u32($slots[$lane].c1, tv),
                            vorrq_u32(vextq_u32($zero, hi, 3), vextq_u32($zero, lo, 2)),
                        );
                        let m2 = vorrq_u32($slots[$lane].c2, vorrq_u32(vextq_u32(lo, $zero, 2), vextq_u32(hi, $zero, 3)));
                        let m3 = $slots[$lane].m3;
                        // Rounds 0..3 are already done; W16..W19 are still wanted.
                        $abcd[$lane] = $slots[$lane].a1;
                        $efgh[$lane] = $slots[$lane].e1;
                        $m[$lane] = [vsha256su1q_u32(vsha256su0q_u32($slots[$lane].m0, m1), m2, m3), m1, m2, m3];
                    }
                    let w = vaddq_u32($m[$lane][i % 4], vld1q_u32(super::K.as_ptr().add(4 * i)));
                    let prev = $abcd[$lane];
                    $abcd[$lane] = vsha256hq_u32($abcd[$lane], $efgh[$lane], w);
                    // Only the first four words of the result are kept, so
                    // the last update of the other four is not needed.
                    if i < 15 {
                        $efgh[$lane] = vsha256h2q_u32($efgh[$lane], prev, w);
                    }
                    if i < 12 {
                        $m[$lane][i % 4] = vsha256su1q_u32(
                            vsha256su0q_u32($m[$lane][i % 4], $m[$lane][(i + 1) % 4]),
                            $m[$lane][(i + 2) % 4],
                            $m[$lane][(i + 3) % 4],
                        );
                    }
                    if i == 15 {
                        $x[$lane] = vaddq_u32($abcd[$lane], $abcd0);
                    }
                }
            }
        };
    }

    /// One period of fifteen ticks; in each, every lane takes one step.
    macro_rules! period {
        ($L:expr, $phase:expr, $args:tt; $($j:literal)*) => {
            $(
                lane_tick!($L, $phase, $j, 0, $args);
                lane_tick!($L, $phase, $j, 1, $args);
                lane_tick!($L, $phase, $j, 2, $args);
                lane_tick!($L, $phase, $j, 3, $args);
            )*
        };
    }

    /// `steps` steps of the first `L` slots, entirely in registers: each step
    /// rebuilds W4..W9 from the counter and the previous value, compresses,
    /// and keeps the first four words of the result as the next value.
    ///
    /// The round instructions of all lanes go through one execution unit, and
    /// a lane has nothing for it while it turns one hash into the next. So
    /// the lanes are staggered: lane `l` runs `15·l/L` steps behind lane 0,
    /// and no two lanes are between hashes at the same time.
    ///
    /// # Safety
    /// `neon` and `sha2` are available; `1 <= L <= 4`; `steps >= 1`; each of
    /// the first `L` slots has at least `steps` steps left.
    #[inline]
    #[allow(unused_assignments)]
    #[target_feature(enable = "neon,sha2")]
    unsafe fn run<const L: usize>(state: &[u32; 8], slots: &mut [Slot; 4], steps: u32) {
        // SAFETY: loads of 16 bytes from `state` (32 bytes) and `K` (256 bytes).
        unsafe {
            let abcd0 = vld1q_u32(state.as_ptr());
            let zero = vdupq_n_u32(0);
            let mut x = [slots[0].x, slots[1].x, slots[2].x, slots[3].x];
            let mut abcd = [zero; 4];
            let mut efgh = [zero; 4];
            let mut m = [[zero; 4]; 4];
            let mut p: u32 = 0;
            period!(L, 0, (slots, p, abcd0, zero, x, abcd, efgh, m); 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14);
            p = 1;
            while p < steps {
                period!(L, 1, (slots, p, abcd0, zero, x, abcd, efgh, m); 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14);
                p += 1;
            }
            period!(L, 2, (slots, p, abcd0, zero, x, abcd, efgh, m); 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14);
            let mut l = 0;
            while l < L {
                slots[l].x = x[l];
                slots[l].t += steps;
                l += 1;
            }
        }
    }
}
