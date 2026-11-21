//! SHA-256 (FIPS 180-4) and HMAC-SHA-256 (FIPS 198-1).
//!
//! Written to mirror the standard as directly as possible: pad the whole
//! message, then compress block by block.

/// Benchmark-only: number of compression-function calls (feature `count`).
#[cfg(feature = "count")]
pub static COMPRESSIONS: core::sync::atomic::AtomicU64 = core::sync::atomic::AtomicU64::new(0);

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
pub fn compress(state: &[u32; 8], data: &[u8], off: usize) -> [u32; 8] {
    #[cfg(feature = "count")]
    COMPRESSIONS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
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

/// The compression function from one state on each of several blocks:
/// `out[i] = compress(state, &blocks[i], 0)` for every `i < blocks.len()`.
/// Panics if `out` is shorter than `blocks`.
///
/// The blocks do not depend on each other. With the opt-in `hw-sha2` feature
/// that lets [`hw`] work on four of them at a time, which is about twice as
/// fast as one after the other.
pub fn compress_many(state: &[u32; 8], blocks: &[[u8; 64]], out: &mut [[u32; 8]]) {
    assert!(blocks.len() <= out.len());
    #[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
    {
        if hw::compress_many(state, blocks, out) {
            return;
        }
    }
    let mut i = 0;
    while i < blocks.len() {
        out[i] = compress(state, &blocks[i], 0);
        i += 1;
    }
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

/// The compression function on the ARMv8 SHA-256 instructions.
///
/// Compiled only with the opt-in `hw-sha2` feature. This module is the only
/// `unsafe` code in the crate and is **not covered by the Lean proofs**:
/// Aeneas translates the default build, in which this module does not exist.
/// Everything outside [`compress`] and [`compress_many`] is the same code
/// either way, and those two only hand their arguments to this module. So a
/// build with the feature computes what the verified build computes provided
/// that
///
/// > whenever `hw::compress` returns `Some`, it holds what the portable code
/// > of `compress` returns for the same arguments, and whenever
/// > `hw::compress_many` returns `true`, it has left in `out` what the
/// > portable loop of `compress_many` leaves there.
///
/// Both come down to [`hw::lanes`]: for 1, 2, 3 or 4 blocks, its result for
/// each block is the portable compression of that block. That statement is
/// tested (`tests/compress.rs` and the ACVP vectors, run with the feature on)
/// but not proved.
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
#[allow(unsafe_code)]
mod hw {
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
        let [out] = unsafe { lanes(state, core::array::from_ref(block)) };
        Some(out)
    }

    /// [`super::compress_many`], four blocks at a time, or `false` if this
    /// CPU lacks the instructions. The caller has checked that `out` is at
    /// least as long as `blocks`.
    #[inline]
    pub fn compress_many(state: &[u32; 8], blocks: &[[u8; 64]], out: &mut [[u32; 8]]) -> bool {
        if !available() {
            return false;
        }
        let (quads, rest) = blocks.as_chunks::<4>();
        let (out_quads, out_rest) = out[..blocks.len()].as_chunks_mut::<4>();
        let mut i = 0;
        while i < quads.len() {
            // SAFETY, here and below: `neon` and `sha2` were detected above.
            out_quads[i] = unsafe { lanes(state, &quads[i]) };
            i += 1;
        }
        if let Ok(three) = <&[[u8; 64]; 3]>::try_from(rest) {
            out_rest.copy_from_slice(&unsafe { lanes(state, three) });
        } else if let Ok(two) = <&[[u8; 64]; 2]>::try_from(rest) {
            out_rest.copy_from_slice(&unsafe { lanes(state, two) });
        } else if let Ok(one) = <&[[u8; 64]; 1]>::try_from(rest) {
            out_rest.copy_from_slice(&unsafe { lanes(state, one) });
        }
        true
    }

    /// The compression function on `L` blocks at once, all from the same
    /// state: sixteen steps of four rounds, each step done for every block
    /// before the next step. For block `l`, `abcd[l]` and `efgh[l]` hold the
    /// working variables and `m[l]` the four most recent schedule vectors.
    ///
    /// One compression is a chain of instructions each waiting for the one
    /// before, so a processor has room to run several chains side by side;
    /// that is the whole point of `L > 1`.
    ///
    /// # Safety
    /// The CPU must support the `neon` and `sha2` target features.
    #[inline]
    #[target_feature(enable = "neon,sha2")]
    unsafe fn lanes<const L: usize>(state: &[u32; 8], blocks: &[[u8; 64]; L]) -> [[u32; 8]; L] {
        // SAFETY, for every load and store below: each touches 16 bytes that
        // lie inside a fixed-size array borrowed for the whole call (`state`
        // and each `out[l]` are 32 bytes, each block is 64, `K` is 256), and
        // NEON loads and stores have no alignment requirement.
        unsafe {
            let abcd0 = vld1q_u32(state.as_ptr());
            let efgh0 = vld1q_u32(state.as_ptr().add(4));
            let mut abcd = [abcd0; L];
            let mut efgh = [efgh0; L];
            let mut m = [[abcd0; 4]; L];
            let mut l = 0;
            while l < L {
                // Big-endian words from little-endian memory: reverse each 4 bytes.
                let p = blocks[l].as_ptr();
                m[l] = [
                    vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p))),
                    vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(16)))),
                    vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(32)))),
                    vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(48)))),
                ];
                l += 1;
            }
            let mut i = 0;
            while i < 16 {
                let k = vld1q_u32(super::K.as_ptr().add(4 * i));
                let mut l = 0;
                while l < L {
                    // Rounds 4i .. 4i+3, on W[4i..4i+4] + K[4i..4i+4].
                    let t = vaddq_u32(m[l][i % 4], k);
                    let prev = abcd[l];
                    abcd[l] = vsha256hq_u32(abcd[l], efgh[l], t);
                    efgh[l] = vsha256h2q_u32(efgh[l], prev, t);
                    // W[4i+16..4i+20], needed from step i + 4 on.
                    if i < 12 {
                        m[l][i % 4] = vsha256su1q_u32(
                            vsha256su0q_u32(m[l][i % 4], m[l][(i + 1) % 4]),
                            m[l][(i + 2) % 4],
                            m[l][(i + 3) % 4],
                        );
                    }
                    l += 1;
                }
                i += 1;
            }
            let mut out = [[0u32; 8]; L];
            let mut l = 0;
            while l < L {
                vst1q_u32(out[l].as_mut_ptr(), vaddq_u32(abcd[l], abcd0));
                vst1q_u32(out[l].as_mut_ptr().add(4), vaddq_u32(efgh[l], efgh0));
                l += 1;
            }
            out
        }
    }
}
