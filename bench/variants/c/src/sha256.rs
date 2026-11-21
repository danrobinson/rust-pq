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

pub(crate) const H0: [u32; 8] = [
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
pub(crate) fn compress(state: &[u32; 8], data: &[u8], off: usize) -> [u32; 8] {
    #[cfg(feature = "count")]
    COMPRESSIONS.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    #[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
    {
        let blk: &[u8; 64] = data[off..off + 64].try_into().unwrap();
        return hw::compress(state, blk);
    }
    #[allow(unreachable_code)]
    compress_soft(state, data, off)
}

/// Variant C: the compression function with the ARMv8 SHA-256 instructions.
/// Selected at compile time; `sha2` is in the baseline of aarch64-apple-darwin.
#[cfg(all(target_arch = "aarch64", target_feature = "sha2"))]
#[allow(unsafe_code)]
mod hw {
    use core::arch::aarch64::*;

    pub fn compress(state: &[u32; 8], blk: &[u8; 64]) -> [u32; 8] {
        // SAFETY: the `sha2` and `neon` target features are enabled at compile
        // time (cfg above); all loads/stores are from in-bounds fixed-size arrays.
        unsafe {
            let mut abcd = vld1q_u32(state.as_ptr());
            let mut efgh = vld1q_u32(state.as_ptr().add(4));
            let abcd0 = abcd;
            let efgh0 = efgh;
            let p = blk.as_ptr();
            let mut m = [
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(16)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(32)))),
                vreinterpretq_u32_u8(vrev32q_u8(vld1q_u8(p.add(48)))),
            ];
            let mut i = 0;
            while i < 16 {
                let t = vaddq_u32(m[i % 4], vld1q_u32(super::K.as_ptr().add(4 * i)));
                let prev = abcd;
                abcd = vsha256hq_u32(abcd, efgh, t);
                efgh = vsha256h2q_u32(efgh, prev, t);
                if i < 12 {
                    m[i % 4] = vsha256su1q_u32(
                        vsha256su0q_u32(m[i % 4], m[(i + 1) % 4]),
                        m[(i + 2) % 4],
                        m[(i + 3) % 4],
                    );
                }
                i += 1;
            }
            abcd = vaddq_u32(abcd, abcd0);
            efgh = vaddq_u32(efgh, efgh0);
            let mut out = [0u32; 8];
            vst1q_u32(out.as_mut_ptr(), abcd);
            vst1q_u32(out.as_mut_ptr().add(4), efgh);
            out
        }
    }
}

#[allow(dead_code)]
fn compress_soft(state: &[u32; 8], data: &[u8], off: usize) -> [u32; 8] {
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

/// Variant B: streaming SHA-256 with a fixed 64-byte stack buffer; no heap.
pub struct Sha256 {
    state: [u32; 8],
    buf: [u8; 64],
    buflen: usize,
    total: u64,
}

impl Sha256 {
    pub fn new() -> Sha256 {
        Sha256 { state: H0, buf: [0u8; 64], buflen: 0, total: 0 }
    }

    /// Continue from a midstate after `prefix_len` bytes (a multiple of 64).
    pub fn from_mid(mid: &[u32; 8], prefix_len: u64) -> Sha256 {
        Sha256 { state: *mid, buf: [0u8; 64], buflen: 0, total: prefix_len }
    }

    pub fn update(&mut self, data: &[u8]) {
        let mut i = 0;
        self.total += data.len() as u64;
        if self.buflen > 0 {
            while self.buflen < 64 && i < data.len() {
                self.buf[self.buflen] = data[i];
                self.buflen += 1;
                i += 1;
            }
            if self.buflen < 64 {
                return;
            }
            self.state = compress(&self.state, &self.buf, 0);
            self.buflen = 0;
        }
        while i + 64 <= data.len() {
            self.state = compress(&self.state, data, i);
            i += 64;
        }
        while i < data.len() {
            self.buf[self.buflen] = data[i];
            self.buflen += 1;
            i += 1;
        }
    }

    pub fn finalize(mut self) -> [u8; 32] {
        let bitlen = self.total * 8;
        let mut n = self.buflen;
        self.buf[n] = 0x80;
        n += 1;
        if n > 56 {
            while n < 64 {
                self.buf[n] = 0;
                n += 1;
            }
            self.state = compress(&self.state, &self.buf, 0);
            n = 0;
        }
        while n < 56 {
            self.buf[n] = 0;
            n += 1;
        }
        let mut j = 0;
        while j < 8 {
            self.buf[56 + j] = (bitlen >> (56 - 8 * j)) as u8;
            j += 1;
        }
        self.state = compress(&self.state, &self.buf, 0);
        let mut out = [0u8; 32];
        let mut i = 0;
        while i < 8 {
            let s = self.state[i];
            out[4 * i] = (s >> 24) as u8;
            out[4 * i + 1] = (s >> 16) as u8;
            out[4 * i + 2] = (s >> 8) as u8;
            out[4 * i + 3] = s as u8;
            i += 1;
        }
        out
    }
}

pub fn sha256(msg: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(msg);
    h.finalize()
}

/// HMAC-SHA-256 with a key of at most 64 bytes (stack buffers only).
pub fn hmac_sha256(key: &[u8], msg: &[u8]) -> [u8; 32] {
    hmac_sha256_parts(key, msg, &[])
}

/// HMAC-SHA-256 of `a ‖ b`, without concatenating them.
pub fn hmac_sha256_parts(key: &[u8], a: &[u8], b: &[u8]) -> [u8; 32] {
    let mut inner = [0u8; 64];
    let mut outer = [0u8; 64];
    let mut i = 0;
    while i < 64 {
        let k = if i < key.len() { key[i] } else { 0 };
        inner[i] = k ^ 0x36;
        outer[i] = k ^ 0x5c;
        i += 1;
    }
    let mut h = Sha256::new();
    h.update(&inner);
    h.update(a);
    h.update(b);
    let ih = h.finalize();
    let mut o = Sha256::new();
    o.update(&outer);
    o.update(&ih);
    o.finalize()
}
