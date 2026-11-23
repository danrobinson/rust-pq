//! SHA-512 (FIPS 180-4) and HMAC-SHA-512 (FIPS 198-1).
//!
//! Written to mirror the standard as directly as possible. Used by the
//! parameter sets with n = 24 and n = 32 for `H`, `T_l`, `H_msg` and
//! `PRF_msg` (FIPS 205 §11.2.2).

use alloc::vec::Vec;

const K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc,
    0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65,
    0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df,
    0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30,
    0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec,
    0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178,
    0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];

/// The initial hash value of SHA-512.
pub const H0: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1,
    0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

#[inline]
fn load_be64(data: &[u8], off: usize) -> u64 {
    ((data[off] as u64) << 56)
        | ((data[off + 1] as u64) << 48)
        | ((data[off + 2] as u64) << 40)
        | ((data[off + 3] as u64) << 32)
        | ((data[off + 4] as u64) << 24)
        | ((data[off + 5] as u64) << 16)
        | ((data[off + 6] as u64) << 8)
        | (data[off + 7] as u64)
}

/// The message schedule W[0..80] for the block at `data[off..off + 128]`.
#[inline]
fn schedule(data: &[u8], off: usize) -> [u64; 80] {
    let mut w = [0u64; 80];
    let mut i = 0;
    while i < 16 {
        w[i] = load_be64(data, off + 8 * i);
        i += 1;
    }
    while i < 80 {
        let x = w[i - 15];
        let y = w[i - 2];
        let s0 = x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7);
        let s1 = y.rotate_right(19) ^ y.rotate_right(61) ^ (y >> 6);
        w[i] = w[i - 16].wrapping_add(s0).wrapping_add(w[i - 7]).wrapping_add(s1);
        i += 1;
    }
    w
}

/// The SHA-512 compression function on the block at `data[off..off + 128]`.
///
/// With the opt-in `hw-sha2` feature, on a CPU that has the ARMv8.2
/// SHA-512 instructions, the result comes from [`hw`]; otherwise from
/// [`compress_portable`].
#[inline]
pub fn compress(state: &[u64; 8], data: &[u8], off: usize) -> [u64; 8] {
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
pub fn compress_portable(state: &[u64; 8], data: &[u8], off: usize) -> [u64; 8] {
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
    while i < 80 {
        let s1 = e.rotate_right(14) ^ e.rotate_right(18) ^ e.rotate_right(41);
        let ch = (e & f) ^ (!e & g);
        let t1 = h.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]);
        let s0 = a.rotate_right(28) ^ a.rotate_right(34) ^ a.rotate_right(39);
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

/// Append the SHA-512 padding to `msg`, for a message whose first `pre`
/// bytes (a multiple of 128) have already been compressed: 0x80, zeros up to
/// 112 mod 128, then the bit length of the whole message, `pre + msg.len()`,
/// as a 128-bit big-endian integer.
fn pad(msg: &[u8], pre: usize) -> Vec<u8> {
    let mut p: Vec<u8> = Vec::new();
    p.extend_from_slice(msg);
    p.push(0x80);
    while p.len() % 128 != 112 {
        p.push(0);
    }
    let bitlen = ((pre + msg.len()) as u128) * 8;
    let mut i: u32 = 0;
    while i < 16 {
        p.push((bitlen >> (120 - 8 * i)) as u8);
        i += 1;
    }
    p
}

/// The big-endian serialisation of a hash state.
pub fn digest(state: &[u64; 8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    let mut i = 0;
    while i < 8 {
        let s = state[i];
        out[8 * i] = (s >> 56) as u8;
        out[8 * i + 1] = (s >> 48) as u8;
        out[8 * i + 2] = (s >> 40) as u8;
        out[8 * i + 3] = (s >> 32) as u8;
        out[8 * i + 4] = (s >> 24) as u8;
        out[8 * i + 5] = (s >> 16) as u8;
        out[8 * i + 6] = (s >> 8) as u8;
        out[8 * i + 7] = s as u8;
        i += 1;
    }
    out
}

/// SHA-512 of `X ‖ msg`, given the state `state` reached after compressing
/// the `pre` bytes of `X` (a multiple of 128).
///
/// Whole blocks are compressed straight from `msg`; only what is left over
/// (under 128 bytes) is copied, together with the padding.
pub fn sha512_from(state: &[u64; 8], pre: usize, msg: &[u8]) -> [u8; 64] {
    let mut st = *state;
    let mut off = 0;
    while off + 128 <= msg.len() {
        st = compress(&st, msg, off);
        off += 128;
    }
    let p = pad(&msg[off..msg.len()], pre + off);
    let mut o = 0;
    while o < p.len() {
        st = compress(&st, &p, o);
        o += 128;
    }
    digest(&st)
}

pub fn sha512(msg: &[u8]) -> [u8; 64] {
    sha512_from(&H0, 0, msg)
}

/// HMAC-SHA-512 with a key of at most 128 bytes.
pub fn hmac_sha512(key: &[u8], msg: &[u8]) -> [u8; 64] {
    let mut inner: Vec<u8> = Vec::new();
    let mut outer: Vec<u8> = Vec::new();
    let mut i = 0;
    while i < 128 {
        let k = if i < key.len() { key[i] } else { 0 };
        inner.push(k ^ 0x36);
        outer.push(k ^ 0x5c);
        i += 1;
    }
    inner.extend_from_slice(msg);
    let ih = sha512(&inner);
    outer.extend_from_slice(&ih);
    sha512(&outer)
}

/// Whether [`compress`] is running on hardware SHA-512 instructions.
///
/// Exists only with the `hw-sha2` feature. `false` means the feature is on
/// but this CPU (or this architecture) lacks the SHA-512 instructions, so the
/// portable code is in use.
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

/// SHA-512 on the ARMv8.2 SHA-512 instructions (FEAT_SHA512).
///
/// Compiled with the opt-in `hw-sha2` feature, like `sha256::hw`, and tested
/// for separately at run time: a CPU may have the SHA-256 instructions and
/// not these. It stands in for one function of the portable code, the
/// compression function, one block at a time. The build with the feature
/// has its own translation and proofs (`lean-hw/`), which show that
///
/// > whenever `hw::compress` returns `Some`, it holds what
/// > [`compress_portable`] returns for the same arguments,
///
/// on the model of the instructions in `lean-hw/Arm.lean`
/// (`lean-hw/Slhdsa/Proofs/Hw512/`). The proofs cover this module except its
/// submodule `arm`, the functions that call the intrinsics.
///
/// The state is held as four vectors of two words, (a, b), (c, d), (e, f),
/// (g, h); each of the forty steps does two rounds.
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64", target_endian = "little"))]
#[allow(unsafe_code)]
pub(crate) mod hw {
    /// As `sha256::hw`'s `kernel!`: compiled with the SHA-512 instructions
    /// enabled (Rust's target feature `sha3` covers FEAT_SHA512) and inlined.
    macro_rules! kernel {
        ($($item:item)*) => {
            $(
                #[cfg_attr(target_feature = "sha3", inline(always))]
                #[cfg_attr(not(target_feature = "sha3"), inline, target_feature(enable = "neon,sha3"))]
                $item
            )*
        };
    }

    /// The instructions: each function is one to three intrinsics and nothing
    /// else. This is the only code of this module Aeneas does not translate;
    /// the proofs take the meaning of these functions from the definitions in
    /// `lean-hw/Slhdsa/FunsExternal.lean`.
    #[allow(unused_unsafe)]
    pub(crate) mod arm {
        use core::arch::aarch64::*;

        /// Two 64-bit words; word 0 is the lower lane.
        pub type V = uint64x2_t;

        /// Whether this CPU has the SHA-512 instructions: as
        /// `sha256::hw::arm::available`, for `neon` and `sha3`.
        #[inline]
        pub fn available() -> bool {
            #[cfg(any(target_os = "none", all(target_feature = "neon", target_feature = "sha3")))]
            {
                cfg!(all(target_feature = "neon", target_feature = "sha3"))
            }
            #[cfg(not(any(target_os = "none", all(target_feature = "neon", target_feature = "sha3"))))]
            {
                std::arch::is_aarch64_feature_detected!("neon") && std::arch::is_aarch64_feature_detected!("sha3")
            }
        }

        // SAFETY, for every function below: the caller has established that
        // the CPU has `neon` and `sha3` (see `kernel!`). The functions that
        // touch memory check their bounds first, and NEON loads and stores
        // have no alignment requirement.
        kernel! {
            /// The words `w[at..at + 2]`.
            pub fn load_words(w: &[u64], at: usize) -> V {
                assert!(w.len() >= 2 && at <= w.len() - 2);
                unsafe { vld1q_u64(w.as_ptr().add(at)) }
            }

            /// The words of `a` followed by the words of `b`.
            pub fn store_words(a: V, b: V) -> [u64; 4] {
                let mut out = [0u64; 4];
                unsafe {
                    vst1q_u64(out.as_mut_ptr(), a);
                    vst1q_u64(out.as_mut_ptr().add(2), b);
                }
                out
            }

            /// The bytes `b[at..at + 16]` as two big-endian words.
            pub fn load_be(b: &[u8], at: usize) -> V {
                assert!(b.len() >= 16 && at <= b.len() - 16);
                unsafe { vreinterpretq_u64_u8(vrev64q_u8(vld1q_u8(b.as_ptr().add(at)))) }
            }

            /// Word-wise sum modulo 2^64.
            pub fn add(a: V, b: V) -> V {
                unsafe { vaddq_u64(a, b) }
            }

            /// `[a[1], b[0]]`.
            pub fn ext1(a: V, b: V) -> V {
                unsafe { vextq_u64(a, b, 1) }
            }

            /// `SHA512H`: the sums of two rounds that reach `e`.
            pub fn sha512h(sum: V, fg: V, de: V) -> V {
                unsafe { vsha512hq_u64(sum, fg, de) }
            }

            /// `SHA512H2`: the two new values of `a`.
            pub fn sha512h2(t: V, cd: V, ab: V) -> V {
                unsafe { vsha512h2q_u64(t, cd, ab) }
            }

            /// `SHA512SU0`: the first part of two new schedule words.
            pub fn sha512su0(w0_1: V, w2_3: V) -> V {
                unsafe { vsha512su0q_u64(w0_1, w2_3) }
            }

            /// `SHA512SU1`: two new schedule words.
            pub fn sha512su1(s: V, w14_15: V, w9_10: V) -> V {
                unsafe { vsha512su1q_u64(s, w14_15, w9_10) }
            }
        }
    }

    /// The compression function on the block at `data[off..off + 128]`, or
    /// `None` if this CPU lacks the instructions.
    #[inline]
    #[allow(unused_unsafe)]
    pub fn compress(state: &[u64; 8], data: &[u8], off: usize) -> Option<[u64; 8]> {
        if !arm::available() {
            return None;
        }
        // The same bounds check, so the same panic, as the portable code.
        let mut block = [0u8; 128];
        block.copy_from_slice(&data[off..off + 128]);
        // SAFETY: `neon` and `sha3` were detected just above.
        Some(unsafe { compress_block(state, &block) })
    }

    kernel! {
        /// Forty steps of two rounds. `ab`, `cd`, `ef`, `gh` hold the working
        /// variables in pairs, `m` the eight most recent schedule vectors.
        fn compress_block(state: &[u64; 8], block: &[u8; 128]) -> [u64; 8] {
            let ab0 = arm::load_words(state, 0);
            let cd0 = arm::load_words(state, 2);
            let ef0 = arm::load_words(state, 4);
            let gh0 = arm::load_words(state, 6);
            let mut m = [
                arm::load_be(block, 0),
                arm::load_be(block, 16),
                arm::load_be(block, 32),
                arm::load_be(block, 48),
                arm::load_be(block, 64),
                arm::load_be(block, 80),
                arm::load_be(block, 96),
                arm::load_be(block, 112),
            ];
            let mut ab = ab0;
            let mut cd = cd0;
            let mut ef = ef0;
            let mut gh = gh0;
            let mut i = 0;
            while i < 40 {
                // Rounds 2i, 2i + 1 on W[2i..2i + 2] + K[2i..2i + 2].
                let wk = arm::add(m[i % 8], arm::load_words(&super::K, 2 * i));
                let sum = arm::add(arm::ext1(wk, wk), gh);
                let t = arm::sha512h(sum, arm::ext1(ef, gh), arm::ext1(cd, ef));
                let ab2 = arm::sha512h2(t, cd, ab);
                let ef2 = arm::add(cd, t);
                gh = ef;
                ef = ef2;
                cd = ab;
                ab = ab2;
                // W[2i + 16..2i + 18], needed from step i + 8 on.
                if i < 32 {
                    m[i % 8] = arm::sha512su1(
                        arm::sha512su0(m[i % 8], m[(i + 1) % 8]),
                        m[(i + 7) % 8],
                        arm::ext1(m[(i + 4) % 8], m[(i + 5) % 8]),
                    );
                }
                i += 1;
            }
            let lo = arm::store_words(arm::add(ab, ab0), arm::add(cd, cd0));
            let hi = arm::store_words(arm::add(ef, ef0), arm::add(gh, gh0));
            [lo[0], lo[1], lo[2], lo[3], hi[0], hi[1], hi[2], hi[3]]
        }
    }
}
