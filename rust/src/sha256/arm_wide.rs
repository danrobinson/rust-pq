//! Lockstep 4-lane Armv8 SHA-256 kernels for batched XMSS, WOTS+, and FORS.
//!
//! All functions check `super::hw::arm::available()` before entering hardware
//! SHA-256 code. Packing of bytes 22..22+N uses `vrev32q_u16` + `vextq_u16::<5>`
//! so each chain step rebuilds `W4..W15` in 5-8 NEON instructions with zero
//! intermediate 64-byte stack buffers. Computing `W16..W19` is deferred until
//! after step 1's `sha256h`/`sha256h2` so round 4 begins immediately after
//! packing, and round constants are loaded through an opaque base pointer
//! inside each block so LLVM never hoists all 16 `K` vectors and spills active
//! schedule registers.
use super::hw::arm::{self, V};
use crate::address::{Adrs, FORS_PRF, FORS_TREE, WOTS_HASH, WOTS_PRF};
use crate::params::{LEN2, LEN_MAX};
use core::arch::aarch64::*;

/// Check whether Armv8 SHA-256 instructions are available.
#[inline]
pub(crate) fn available() -> bool {
    arm::available()
}

macro_rules! kernel {
    ($($item:item)*) => {
        $(
            #[cfg_attr(target_feature = "sha2", inline(always))]
            #[cfg_attr(not(target_feature = "sha2"), inline, target_feature(enable = "neon,sha2"))]
            #[allow(unused_unsafe)]
            $item
        )*
    };
}

/// Precomputed rounds-0..3 state stored in memory so outer loops never compete
/// for the 32 NEON registers during the 60-round 4-lane inner core.
#[derive(Clone, Copy)]
struct Head {
    m0: [u32; 4],
    a1: [u32; 4],
    e1: [u32; 4],
}

kernel! {
    unsafe fn load_n<const N: usize>(src: &[u8]) -> (V, V) {
        let x = arm::load_be(src, 0);
        let xb = if N == 16 {
            vdupq_n_u32(0)
        } else if N == 24 {
            let lo = vld1_u8(src.as_ptr().add(16));
            vreinterpretq_u32_u8(vrev32q_u8(vcombine_u8(lo, vdup_n_u8(0))))
        } else {
            arm::load_be(src, 16)
        };
        (x, xb)
    }

    unsafe fn store_n<const N: usize>(dst: &mut [u8], x: V, xb: V) {
        vst1q_u8(dst.as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x)));
        if N == 24 {
            let b = vrev32q_u8(vreinterpretq_u8_u32(xb));
            vst1_u8(dst.as_mut_ptr().add(16), vget_low_u8(b));
        } else if N == 32 {
            vst1q_u8(dst.as_mut_ptr().add(16), vrev32q_u8(vreinterpretq_u8_u32(xb)));
        }
    }

    /// Build `[0, 0, 0, 0, 0, word2_lo16, t_hi, t_lo]` as `uint16x8_t`.
    unsafe fn make_hdr(word2: u32, t: u32) -> uint16x8_t {
        let hi: u64 = ((word2 as u64 & 0xffff) << 16)
            | (((t >> 16) as u64) << 32)
            | (((t & 0xffff) as u64) << 48);
        vreinterpretq_u16_u64(vcombine_u64(vdup_n_u64(0), vdup_n_u64(hi)))
    }

    /// Precompute `(m0, a1, e1)` for an address's first 16 bytes (rounds 0..3).
    unsafe fn make_head(state: &[u32; 8], adrs: Adrs) -> Head {
        let abcd0 = arm::load_words(state, 0);
        let efgh0 = arm::load_words(state, 4);
        let bytes = adrs.compress();
        let m0 = arm::load_be(&bytes, 0);
        let w = vaddq_u32(m0, arm::load_words(&super::K, 0));
        let a1 = vsha256hq_u32(abcd0, efgh0, w);
        let e1 = vsha256h2q_u32(efgh0, abcd0, w);
        let mut h = Head { m0: [0; 4], a1: [0; 4], e1: [0; 4] };
        vst1q_u32(h.m0.as_mut_ptr(), m0);
        vst1q_u32(h.a1.as_mut_ptr(), a1);
        vst1q_u32(h.e1.as_mut_ptr(), e1);
        h
    }

    /// Pack `(hdr, x, xb)` into SHA-256 schedule vectors `(m1, m2, m3)` for a
    /// `short_block` of length `N` (16, 24, or 32) or a `pair_block` (N=32).
    unsafe fn pack_short<const N: usize>(hdr: uint16x8_t, x: V, xb: V) -> (V, V, V) {
        let xr = vrev32q_u16(vreinterpretq_u16_u32(x));
        let m1 = vreinterpretq_u32_u16(vrev32q_u16(vextq_u16::<5>(hdr, xr)));
        if N == 16 {
            let pad16: uint16x8_t = vreinterpretq_u16_u64(vcombine_u64(vdup_n_u64(0x8000), vdup_n_u64(0)));
            let m2 = vreinterpretq_u32_u16(vrev32q_u16(vextq_u16::<5>(xr, pad16)));
            let m3 = vsetq_lane_u32::<3>(0x0330, vdupq_n_u32(0));
            (m1, m2, m3)
        } else if N == 24 {
            let xbr = vsetq_lane_u16::<4>(0x8000, vrev32q_u16(vreinterpretq_u16_u32(xb)));
            let m2 = vreinterpretq_u32_u16(vrev32q_u16(vextq_u16::<5>(xr, xbr)));
            let m3 = vsetq_lane_u32::<3>(0x0370, vdupq_n_u32(0));
            (m1, m2, m3)
        } else {
            let xbr = vrev32q_u16(vreinterpretq_u16_u32(xb));
            let m2 = vreinterpretq_u32_u16(vrev32q_u16(vextq_u16::<5>(xr, xbr)));
            let pad32: uint16x8_t = vreinterpretq_u16_u64(vcombine_u64(vdup_n_u64(0x8000), vdup_n_u64(0x03b0)));
            let m3 = vreinterpretq_u32_u16(vrev32q_u16(vextq_u16::<5>(xbr, pad32)));
            (m1, m2, m3)
        }
    }

    /// Execute one 4-round step `I` (0..=15) across `L` lanes in lockstep.
    unsafe fn step_lanes<const L: usize, const I: usize, const NEED_EFGH: bool>(
        abcd: &mut [V; L],
        efgh: &mut [V; L],
        m: &mut [[V; 4]; L],
        k_ptr: *const u32,
    ) {
        let k = vld1q_u32(k_ptr.add(4 * I));
        let mut l = 0;
        while l < L {
            let w = vaddq_u32(m[l][I % 4], k);
            let prev = abcd[l];
            abcd[l] = vsha256hq_u32(prev, efgh[l], w);
            if I < 15 || NEED_EFGH {
                efgh[l] = vsha256h2q_u32(efgh[l], prev, w);
            }
            if I < 12 {
                let s0 = vsha256su0q_u32(m[l][I % 4], m[l][(I + 1) % 4]);
                m[l][I % 4] = vsha256su1q_u32(s0, m[l][(I + 2) % 4], m[l][(I + 3) % 4]);
            }
            l += 1;
        }
    }

    /// Run rounds 4..63 (steps 1..=15) on `L` lanes with deferred `W16..W19`
    /// so step 1 starts immediately after packing without waiting on `sha256su`.
    unsafe fn finish_from_r4<const L: usize, const NEED_EFGH: bool>(
        state: &[u32; 8],
        a1: [V; L],
        e1: [V; L],
        m0: [V; L],
        m1: [V; L],
        m2: [V; L],
        m3: [V; L],
        k_ptr: *const u32,
    ) -> ([V; L], [V; L]) {
        let mut abcd = a1;
        let mut efgh = e1;
        let z = vdupq_n_u32(0);
        let mut m = [[z; 4]; L];
        let k1 = vld1q_u32(k_ptr.add(4));
        let mut l = 0;
        while l < L {
            let w = vaddq_u32(m1[l], k1);
            let prev = abcd[l];
            abcd[l] = vsha256hq_u32(prev, efgh[l], w);
            efgh[l] = vsha256h2q_u32(efgh[l], prev, w);
            let w16 = vsha256su1q_u32(vsha256su0q_u32(m0[l], m1[l]), m2[l], m3[l]);
            let w20 = vsha256su1q_u32(vsha256su0q_u32(m1[l], m2[l]), m3[l], w16);
            m[l] = [w16, w20, m2[l], m3[l]];
            l += 1;
        }
        step_lanes::<L, 2, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 3, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 4, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 5, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 6, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 7, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 8, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 9, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 10, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 11, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 12, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 13, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 14, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        step_lanes::<L, 15, NEED_EFGH>(&mut abcd, &mut efgh, &mut m, k_ptr);
        let abcd0 = arm::load_words(state, 0);
        let efgh0 = if NEED_EFGH { arm::load_words(state, 4) } else { z };
        let mut l = 0;
        while l < L {
            abcd[l] = vaddq_u32(abcd[l], abcd0);
            if NEED_EFGH {
                efgh[l] = vaddq_u32(efgh[l], efgh0);
            }
            l += 1;
        }
        (abcd, efgh)
    }

    /// Run all 64 rounds (steps 0..=15) on `L` lanes from per-lane states.
    unsafe fn compress_block_lanes<const L: usize, const NEED_EFGH: bool>(
        abcd: &mut [V; L],
        efgh: &mut [V; L],
        m: &mut [[V; 4]; L],
        k_ptr: *const u32,
    ) {
        step_lanes::<L, 0, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 1, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 2, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 3, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 4, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 5, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 6, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 7, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 8, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 9, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 10, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 11, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 12, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 13, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 14, NEED_EFGH>(abcd, efgh, m, k_ptr);
        step_lanes::<L, 15, NEED_EFGH>(abcd, efgh, m, k_ptr);
    }

    /// Load `L` lane heads from memory.
    unsafe fn load_heads<const L: usize>(heads: &[Head; L]) -> ([V; L], [V; L], [V; L]) {
        let z = vdupq_n_u32(0);
        let mut m0 = [z; L];
        let mut a1 = [z; L];
        let mut e1 = [z; L];
        let mut l = 0;
        while l < L {
            m0[l] = vld1q_u32(heads[l].m0.as_ptr());
            a1[l] = vld1q_u32(heads[l].a1.as_ptr());
            e1[l] = vld1q_u32(heads[l].e1.as_ptr());
            l += 1;
        }
        (m0, a1, e1)
    }

    /// Load a single shared head for all `L` lanes.
    unsafe fn load_shared_head<const L: usize>(head: &Head) -> ([V; L], [V; L], [V; L]) {
        let m0 = vld1q_u32(head.m0.as_ptr());
        let a1 = vld1q_u32(head.a1.as_ptr());
        let e1 = vld1q_u32(head.e1.as_ptr());
        ([m0; L], [a1; L], [e1; L])
    }
}

/// Out-of-line 4-lane rounds-4..63 core with distinct per-lane heads.
#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn step4_distinct_heads<const N: usize>(
    state: &[u32; 8],
    heads: &[Head; 4],
    hdrs: &[uint16x8_t; 4],
    x: &mut [V; 4],
    xb: &mut [V; 4],
) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let (m0, a1, e1) = unsafe { load_heads::<4>(heads) };
    let z = vdupq_n_u32(0);
    let mut m1 = [z; 4];
    let mut m2 = [z; 4];
    let mut m3 = [z; 4];
    for l in 0..4 {
        let (a, b, d) = unsafe { pack_short::<N>(hdrs[l], x[l], xb[l]) };
        m1[l] = a;
        m2[l] = b;
        m3[l] = d;
    }
    let (nx, nxb) = if N == 16 {
        unsafe { finish_from_r4::<4, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
    } else {
        unsafe { finish_from_r4::<4, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
    };
    *x = nx;
    *xb = nxb;
}

/// Out-of-line 4-lane rounds-4..63 core with a single shared head (3 vector
/// loads instead of 12).
#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn step4_shared_head<const N: usize>(
    state: &[u32; 8],
    head: &Head,
    hdrs: &[uint16x8_t; 4],
    x: &mut [V; 4],
    xb: &mut [V; 4],
) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let (m0, a1, e1) = unsafe { load_shared_head::<4>(head) };
    let z = vdupq_n_u32(0);
    let mut m1 = [z; 4];
    let mut m2 = [z; 4];
    let mut m3 = [z; 4];
    for l in 0..4 {
        let (a, b, d) = unsafe { pack_short::<N>(hdrs[l], x[l], xb[l]) };
        m1[l] = a;
        m2[l] = b;
        m3[l] = d;
    }
    let (nx, nxb) = if N == 16 {
        unsafe { finish_from_r4::<4, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
    } else {
        unsafe { finish_from_r4::<4, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
    };
    *x = nx;
    *xb = nxb;
}

/// Run `steps` consecutive WOTS chain steps for 4 chains sharing ONE `head`
/// completely in registers (used by `wots_recover` with `min_left` steps and
/// `wots_endpoints_1` with 15 steps).
#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn run_shared4_steps<const N: usize>(
    state: &[u32; 8],
    head: &Head,
    chains: [u32; 4],
    cur_t: [u32; 4],
    steps: u32,
    x: &mut [V; 4],
    xb: &mut [V; 4],
) {
    let mut lx = *x;
    let mut lxb = *xb;
    let mut t0 = cur_t[0];
    let mut t1 = cur_t[1];
    let mut t2 = cur_t[2];
    let mut t3 = cur_t[3];
    let z = vdupq_n_u32(0);
    let mut s = 0u32;
    while s < steps {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let mut m1 = [z; 4];
        let mut m2 = [z; 4];
        let mut m3 = [z; 4];
        let (a0, b0, d0) = unsafe { pack_short::<N>(make_hdr(chains[0], t0), lx[0], lxb[0]) };
        let (a1, b1, d1) = unsafe { pack_short::<N>(make_hdr(chains[1], t1), lx[1], lxb[1]) };
        let (a2, b2, d2) = unsafe { pack_short::<N>(make_hdr(chains[2], t2), lx[2], lxb[2]) };
        let (a3, b3, d3) = unsafe { pack_short::<N>(make_hdr(chains[3], t3), lx[3], lxb[3]) };
        m1[0] = a0; m2[0] = b0; m3[0] = d0;
        m1[1] = a1; m2[1] = b1; m3[1] = d1;
        m1[2] = a2; m2[2] = b2; m3[2] = d2;
        m1[3] = a3; m2[3] = b3; m3[3] = d3;
        let (m0, ha1, he1) = unsafe { load_shared_head::<4>(head) };
        (lx, lxb) = if N == 16 {
            unsafe { finish_from_r4::<4, false>(state, ha1, he1, m0, m1, m2, m3, k_ptr) }
        } else {
            unsafe { finish_from_r4::<4, true>(state, ha1, he1, m0, m1, m2, m3, k_ptr) }
        };
        t0 += 1;
        t1 += 1;
        t2 += 1;
        t3 += 1;
        s += 1;
    }
    *x = lx;
    *xb = lxb;
}

/// Run 15 WOTS chain steps (`t = 0..15`) for chain `chain` across 4 keys
/// completely in registers: pack FIRST (consuming `lx, lxb`) before loading
/// `hash_heads` to minimize peak NEON register pressure.
#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn run_wots4_15steps<const N: usize>(
    state: &[u32; 8],
    hash_heads: &[Head; 4],
    chain: u32,
    x: &mut [V; 4],
    xb: &mut [V; 4],
) {
    let mut lx = *x;
    let mut lxb = *xb;
    let z = vdupq_n_u32(0);
    let mut t = 0u32;
    while t < 15 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let hdr = unsafe { make_hdr(chain, t) };
        let mut m1 = [z; 4];
        let mut m2 = [z; 4];
        let mut m3 = [z; 4];
        for l in 0..4 {
            let (a, b, d) = unsafe { pack_short::<N>(hdr, lx[l], lxb[l]) };
            m1[l] = a;
            m2[l] = b;
            m3[l] = d;
        }
        let (m0, a1, e1) = unsafe { load_heads::<4>(hash_heads) };
        (lx, lxb) = if N == 16 {
            unsafe { finish_from_r4::<4, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
        } else {
            unsafe { finish_from_r4::<4, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
        };
        t += 1;
    }
    *x = lx;
    *xb = lxb;
}

/// Single-pack 4-key WOTS PRF step (identical `m1, m2, m3` across all 4 keys).
#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn step4_wots_prf<const N: usize>(
    state: &[u32; 8],
    prf_heads: &[Head; 4],
    sk_seed: &[u8; N],
    chain: u32,
) -> ([V; 4], [V; 4]) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let (sk_x, sk_xb) = unsafe { load_n::<N>(sk_seed) };
    let (m1p, m2p, m3p) = unsafe { pack_short::<N>(make_hdr(chain, 0), sk_x, sk_xb) };
    let (m0, a1, e1) = unsafe { load_heads::<4>(prf_heads) };
    if N == 16 {
        unsafe { finish_from_r4::<4, false>(state, a1, e1, m0, [m1p; 4], [m2p; 4], [m3p; 4], k_ptr) }
    } else {
        unsafe { finish_from_r4::<4, true>(state, a1, e1, m0, [m1p; 4], [m2p; 4], [m3p; 4], k_ptr) }
    }
}

/// Run 15 WOTS chain steps for 2 keys × 2 chains `(c, c+1)` completely in registers.
#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn run_wots2_15steps<const N: usize>(
    state: &[u32; 8],
    hash_heads: &[Head; 4],
    c: u32,
    x: &mut [V; 4],
    xb: &mut [V; 4],
) {
    let mut lx = *x;
    let mut lxb = *xb;
    let z = vdupq_n_u32(0);
    let mut t = 0u32;
    while t < 15 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let h0 = unsafe { make_hdr(c, t) };
        let h1 = unsafe { make_hdr(c + 1, t) };
        let (a0, b0, d0) = unsafe { pack_short::<N>(h0, lx[0], lxb[0]) };
        let (a1, b1, d1) = unsafe { pack_short::<N>(h1, lx[1], lxb[1]) };
        let (a2, b2, d2) = unsafe { pack_short::<N>(h0, lx[2], lxb[2]) };
        let (a3, b3, d3) = unsafe { pack_short::<N>(h1, lx[3], lxb[3]) };
        let m1 = [a0, a1, a2, a3];
        let m2 = [b0, b1, b2, b3];
        let m3 = [d0, d1, d2, d3];
        let (m0, ha1, he1) = unsafe { load_heads::<4>(hash_heads) };
        (lx, lxb) = if N == 16 {
            unsafe { finish_from_r4::<4, false>(state, ha1, he1, m0, m1, m2, m3, k_ptr) }
        } else {
            unsafe { finish_from_r4::<4, true>(state, ha1, he1, m0, m1, m2, m3, k_ptr) }
        };
        let _ = z;
        t += 1;
    }
    *x = lx;
    *xb = lxb;
}

/// Fused WOTS+ PRF + 15 chain steps for 4 consecutive keys (`first..first+4`),
/// writing all `len` endpoints of key `k` into `msgs[k][22 + c * N ..]`.
pub(crate) fn wots_endpoints_4<const N: usize, const L: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    first: u32,
    msgs: &mut [[u8; L]; 4],
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { wots_endpoints_4_active::<N, L>(state, sk_seed, adrs, first, msgs) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn wots_endpoints_4_active<const N: usize, const L: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    first: u32,
    msgs: &mut [[u8; L]; 4],
) {
    let prf_base = adrs.with_type(WOTS_PRF);
    let hash_base = adrs.with_type(WOTS_HASH);
    let prf_heads = [
        unsafe { make_head(state, prf_base.with_keypair(first)) },
        unsafe { make_head(state, prf_base.with_keypair(first + 1)) },
        unsafe { make_head(state, prf_base.with_keypair(first + 2)) },
        unsafe { make_head(state, prf_base.with_keypair(first + 3)) },
    ];
    let hash_heads = [
        unsafe { make_head(state, hash_base.with_keypair(first)) },
        unsafe { make_head(state, hash_base.with_keypair(first + 1)) },
        unsafe { make_head(state, hash_base.with_keypair(first + 2)) },
        unsafe { make_head(state, hash_base.with_keypair(first + 3)) },
    ];
    let (sk_x, sk_xb) = unsafe { load_n::<N>(sk_seed) };
    let len = 2 * N + LEN2; // 35, 51, 67
    let main_end = len & !3; // 32, 48, 64

    // 91-96% of chains run 4 chains of the SAME keypair together so all 4 lanes
    // share a single Head (3 vector loads instead of 12, minimal register pressure).
    for k in 0..4 {
        let mut c = 0usize;
        while c < main_end {
            let mut x = [sk_x; 4];
            let mut xb = [sk_xb; 4];
            let hdrs = [
                unsafe { make_hdr(c as u32, 0) },
                unsafe { make_hdr((c + 1) as u32, 0) },
                unsafe { make_hdr((c + 2) as u32, 0) },
                unsafe { make_hdr((c + 3) as u32, 0) },
            ];
            step4_shared_head::<N>(state, &prf_heads[k], &hdrs, &mut x, &mut xb);
            run_shared4_steps::<N>(
                state,
                &hash_heads[k],
                [c as u32, (c + 1) as u32, (c + 2) as u32, (c + 3) as u32],
                [0, 0, 0, 0],
                15,
                &mut x,
                &mut xb,
            );
            for l in 0..4 {
                unsafe { store_n::<N>(&mut msgs[k][22 + (c + l) * N..], x[l], xb[l]) };
            }
            c += 4;
        }
    }

    // Remaining 3 tail chains (len % 4 == 3) run across all 4 keys -> zero wasted lanes!
    let mut c = main_end;
    while c < len {
        let (mut x, mut xb) = step4_wots_prf::<N>(state, &prf_heads, sk_seed, c as u32);
        run_wots4_15steps::<N>(state, &hash_heads, c as u32, &mut x, &mut xb);
        let off = 22 + c * N;
        for l in 0..4 {
            unsafe { store_n::<N>(&mut msgs[l][off..], x[l], xb[l]) };
        }
        c += 1;
    }
}

/// Fused WOTS+ PRF + 15 chain steps for 2 consecutive keys (`first..first+2`),
/// running 4 chains at a time across the pair (only the final 2 chains run 2-way).
pub(crate) fn wots_endpoints_2<const N: usize, const L: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    first: u32,
    msgs: &mut [[u8; L]; 2],
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { wots_endpoints_2_active::<N, L>(state, sk_seed, adrs, first, msgs) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn wots_endpoints_2_active<const N: usize, const L: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    first: u32,
    msgs: &mut [[u8; L]; 2],
) {
    let prf_base = adrs.with_type(WOTS_PRF);
    let hash_base = adrs.with_type(WOTS_HASH);
    let p0 = unsafe { make_head(state, prf_base.with_keypair(first)) };
    let p1 = unsafe { make_head(state, prf_base.with_keypair(first + 1)) };
    let h0 = unsafe { make_head(state, hash_base.with_keypair(first)) };
    let h1 = unsafe { make_head(state, hash_base.with_keypair(first + 1)) };
    let prf_heads = [p0, p0, p1, p1];
    let hash_heads = [h0, h0, h1, h1];
    let (sk_x, sk_xb) = unsafe { load_n::<N>(sk_seed) };
    let len = 2 * N + LEN2; // 35, 51, 67
    let mut c = 0usize;
    while c + 1 < len {
        let mut x = [sk_x; 4];
        let mut xb = [sk_xb; 4];
        let hdrs = [
            unsafe { make_hdr(c as u32, 0) },
            unsafe { make_hdr((c + 1) as u32, 0) },
            unsafe { make_hdr(c as u32, 0) },
            unsafe { make_hdr((c + 1) as u32, 0) },
        ];
        step4_distinct_heads::<N>(state, &prf_heads, &hdrs, &mut x, &mut xb);
        run_wots2_15steps::<N>(state, &hash_heads, c as u32, &mut x, &mut xb);
        unsafe {
            store_n::<N>(&mut msgs[0][22 + c * N..], x[0], xb[0]);
            store_n::<N>(&mut msgs[0][22 + (c + 1) * N..], x[1], xb[1]);
            store_n::<N>(&mut msgs[1][22 + c * N..], x[2], xb[2]);
            store_n::<N>(&mut msgs[1][22 + (c + 1) * N..], x[3], xb[3]);
        }
        c += 2;
    }
    // Final chain `len - 1` across the 2 keys in 2-way.
    let hdr0 = unsafe { make_hdr((len - 1) as u32, 0) };
    let (m1p, m2p, m3p) = unsafe { pack_short::<N>(hdr0, sk_x, sk_xb) };
    let (m0p, a1p, e1p) = unsafe { load_heads::<2>(&[p0, p1]) };
    let k_ptr0 = core::hint::black_box(super::K.as_ptr());
    let (mut x, mut xb) = if N == 16 {
        unsafe { finish_from_r4::<2, false>(state, a1p, e1p, m0p, [m1p; 2], [m2p; 2], [m3p; 2], k_ptr0) }
    } else {
        unsafe { finish_from_r4::<2, true>(state, a1p, e1p, m0p, [m1p; 2], [m2p; 2], [m3p; 2], k_ptr0) }
    };
    let mut t = 0u32;
    while t < 15 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let hdr = unsafe { make_hdr((len - 1) as u32, t) };
        let (a0, b0, d0) = unsafe { pack_short::<N>(hdr, x[0], xb[0]) };
        let (a1, b1, d1) = unsafe { pack_short::<N>(hdr, x[1], xb[1]) };
        let (m0, a1h, e1h) = unsafe { load_heads::<2>(&[h0, h1]) };
        (x, xb) = if N == 16 {
            unsafe { finish_from_r4::<2, false>(state, a1h, e1h, m0, [a0, a1], [b0, b1], [d0, d1], k_ptr) }
        } else {
            unsafe { finish_from_r4::<2, true>(state, a1h, e1h, m0, [a0, a1], [b0, b1], [d0, d1], k_ptr) }
        };
        t += 1;
    }
    let off = 22 + (len - 1) * N;
    unsafe {
        store_n::<N>(&mut msgs[0][off..], x[0], xb[0]);
        store_n::<N>(&mut msgs[1][off..], x[1], xb[1]);
    }
}

/// Fused WOTS+ PRF + 15 chain steps for 1 key, writing all `len` endpoints
/// directly into `msg[22 + c * N ..]`.
pub(crate) fn wots_endpoints_1<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    msg: &mut [u8],
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { wots_endpoints_1_active::<N>(state, sk_seed, adrs, msg) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn wots_endpoints_1_active<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    msg: &mut [u8],
) {
    let prf_adrs = adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair);
    let hash_adrs = adrs.with_type(WOTS_HASH).with_keypair(adrs.keypair);
    let p_head = unsafe { make_head(state, prf_adrs) };
    let h_head = unsafe { make_head(state, hash_adrs) };
    let (sk_x, sk_xb) = unsafe { load_n::<N>(sk_seed) };
    let len = 2 * N + LEN2; // 35, 51, 67 -> len % 4 == 3
    let mut c = 0usize;
    while c + 4 <= len {
        let mut x = [sk_x; 4];
        let mut xb = [sk_xb; 4];
        let hdrs = [
            unsafe { make_hdr(c as u32, 0) },
            unsafe { make_hdr((c + 1) as u32, 0) },
            unsafe { make_hdr((c + 2) as u32, 0) },
            unsafe { make_hdr((c + 3) as u32, 0) },
        ];
        step4_shared_head::<N>(state, &p_head, &hdrs, &mut x, &mut xb);
        run_shared4_steps::<N>(
            state,
            &h_head,
            [c as u32, (c + 1) as u32, (c + 2) as u32, (c + 3) as u32],
            [0, 0, 0, 0],
            15,
            &mut x,
            &mut xb,
        );
        for l in 0..4 {
            unsafe { store_n::<N>(&mut msg[22 + (c + l) * N..], x[l], xb[l]) };
        }
        c += 4;
    }
    // Tail 3 chains (35 % 4 == 51 % 4 == 67 % 4 == 3) in 3-way.
    debug_assert_eq!(len - c, 3);
    let z = vdupq_n_u32(0);
    let mut m1p = [z; 3];
    let mut m2p = [z; 3];
    let mut m3p = [z; 3];
    for l in 0..3 {
        let (a, b, d) = unsafe { pack_short::<N>(make_hdr((c + l) as u32, 0), sk_x, sk_xb) };
        m1p[l] = a;
        m2p[l] = b;
        m3p[l] = d;
    }
    let (m0p, a1p, e1p) = unsafe { load_shared_head::<3>(&p_head) };
    let k_ptr0 = core::hint::black_box(super::K.as_ptr());
    let (mut x, mut xb) = if N == 16 {
        unsafe { finish_from_r4::<3, false>(state, a1p, e1p, m0p, m1p, m2p, m3p, k_ptr0) }
    } else {
        unsafe { finish_from_r4::<3, true>(state, a1p, e1p, m0p, m1p, m2p, m3p, k_ptr0) }
    };
    let mut t = 0u32;
    while t < 15 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let mut m1 = [z; 3];
        let mut m2 = [z; 3];
        let mut m3 = [z; 3];
        for l in 0..3 {
            let (a, b, d) = unsafe { pack_short::<N>(make_hdr((c + l) as u32, t), x[l], xb[l]) };
            m1[l] = a;
            m2[l] = b;
            m3[l] = d;
        }
        let (m0, a1, e1) = unsafe { load_shared_head::<3>(&h_head) };
        (x, xb) = if N == 16 {
            unsafe { finish_from_r4::<3, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
        } else {
            unsafe { finish_from_r4::<3, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
        };
        t += 1;
    }
    for l in 0..3 {
        unsafe { store_n::<N>(&mut msg[22 + (c + l) * N..], x[l], xb[l]) };
    }
}

/// Multi-block 4-way SHA-256 compression for 4 equal-length padded messages
/// (used for N = 16 `T_len`, `L = 640`).
pub(crate) fn compress_multi_4<const L: usize>(
    state: &[u32; 8],
    msgs: &[[u8; L]; 4],
    out: &mut [[u8; 16]],
) {
    debug_assert!(available() && L > 0 && L % 64 == 0 && out.len() >= 4);
    // SAFETY: caller verified arm::available().
    unsafe { compress_multi_lanes::<4, L>(state, msgs, out) };
}

/// Multi-block 2-way SHA-256 compression for 2 equal-length padded messages.
pub(crate) fn compress_multi_2<const L: usize>(
    state: &[u32; 8],
    msgs: &[[u8; L]; 2],
    out: &mut [[u8; 16]],
) {
    debug_assert!(available() && L > 0 && L % 64 == 0 && out.len() >= 2);
    // SAFETY: caller verified arm::available().
    unsafe { compress_multi_lanes::<2, L>(state, msgs, out) };
}

/// Multi-block 1-way SHA-256 compression keeping the state in NEON registers
/// across all blocks, returning the first 16 digest bytes.
pub(crate) fn compress_multi_1(state: &[u32; 8], msg: &[u8]) -> [u8; 16] {
    debug_assert!(available() && !msg.is_empty() && msg.len() % 64 == 0);
    // SAFETY: caller verified arm::available().
    unsafe { compress_multi_1_active(state, msg) }
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn compress_multi_1_active(state: &[u32; 8], msg: &[u8]) -> [u8; 16] {
    let mut abcd_acc = arm::load_words(state, 0);
    let mut efgh_acc = arm::load_words(state, 4);
    let len = msg.len();
    let mut off = 0usize;
    while off < len {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        let mut abcd = [abcd_acc];
        let mut efgh = [efgh_acc];
        let mut m = [[
            arm::load_be(msg, off),
            arm::load_be(msg, off + 16),
            arm::load_be(msg, off + 32),
            arm::load_be(msg, off + 48),
        ]];
        unsafe { compress_block_lanes::<1, true>(&mut abcd, &mut efgh, &mut m, k_ptr) };
        abcd_acc = vaddq_u32(abcd_acc, abcd[0]);
        efgh_acc = vaddq_u32(efgh_acc, efgh[0]);
        off += 64;
    }
    let mut out = [0u8; 16];
    unsafe { vst1q_u8(out.as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(abcd_acc))) };
    out
}

#[inline(never)]
#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn compress_block_lanes_in_place<const K_LANES: usize, const L: usize>(
    acc: &mut [[u32; 8]; K_LANES],
    msgs: &[[u8; L]; K_LANES],
    off: usize,
) {
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    let z = vdupq_n_u32(0);
    let mut abcd = [z; K_LANES];
    let mut efgh = [z; K_LANES];
    let mut m = [[z; 4]; K_LANES];
    for l in 0..K_LANES {
        abcd[l] = arm::load_words(&acc[l], 0);
        efgh[l] = arm::load_words(&acc[l], 4);
        m[l] = [
            arm::load_be(&msgs[l], off),
            arm::load_be(&msgs[l], off + 16),
            arm::load_be(&msgs[l], off + 32),
            arm::load_be(&msgs[l], off + 48),
        ];
    }
    unsafe { compress_block_lanes::<K_LANES, true>(&mut abcd, &mut efgh, &mut m, k_ptr) };
    for l in 0..K_LANES {
        unsafe {
            let ptr = acc[l].as_mut_ptr();
            vst1q_u32(ptr, vaddq_u32(vld1q_u32(ptr), abcd[l]));
            vst1q_u32(ptr.add(4), vaddq_u32(vld1q_u32(ptr.add(4)), efgh[l]));
        }
    }
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn compress_multi_lanes<const K_LANES: usize, const L: usize>(
    state: &[u32; 8],
    msgs: &[[u8; L]; K_LANES],
    out: &mut [[u8; 16]],
) {
    let mut acc = [*state; K_LANES];
    let mut off = 0usize;
    while off < L {
        compress_block_lanes_in_place::<K_LANES, L>(&mut acc, msgs, off);
        off += 64;
    }
    for l in 0..K_LANES {
        let d = arm::load_words(&acc[l], 0);
        unsafe { vst1q_u8(out[l].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(d))) };
    }
}

/// Batch `count` SHA-256 parent hashes (`H` for N = 16) in place:
/// `vals[j] = H(state, adrs.with_word3(first + j), vals[2*j] || vals[2*j+1])`.
pub(crate) fn parents_16(
    state: &[u32; 8],
    adrs: Adrs,
    first: u32,
    vals: &mut [[u8; 16]],
    count: usize,
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { parents_16_active(state, adrs, first, vals, count) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn parents_16_active(
    state: &[u32; 8],
    adrs: Adrs,
    first: u32,
    vals: &mut [[u8; 16]],
    count: usize,
) {
    let head = unsafe { make_head(state, adrs) };
    let word2 = adrs.word2;
    let z = vdupq_n_u32(0);

    let mut j = 0usize;
    while j + 4 <= count {
        let mut x = [z; 4];
        let mut xb = [z; 4];
        let mut hdrs = [unsafe { make_hdr(0, 0) }; 4];
        for l in 0..4 {
            let i = j + l;
            hdrs[l] = unsafe { make_hdr(word2, first + i as u32) };
            x[l] = arm::load_be(&vals[2 * i], 0);
            xb[l] = arm::load_be(&vals[2 * i + 1], 0);
        }
        // pair_block for N=16 has the exact 32-byte payload layout of short_block<32>.
        step4_shared_head::<32>(state, &head, &hdrs, &mut x, &mut xb);
        for l in 0..4 {
            unsafe { vst1q_u8(vals[j + l].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[l]))) };
        }
        j += 4;
    }
    let k_ptr = core::hint::black_box(super::K.as_ptr());
    while j + 2 <= count {
        let mut m1 = [z; 2];
        let mut m2 = [z; 2];
        let mut m3 = [z; 2];
        for l in 0..2 {
            let i = j + l;
            let hdr = unsafe { make_hdr(word2, first + i as u32) };
            let left = arm::load_be(&vals[2 * i], 0);
            let right = arm::load_be(&vals[2 * i + 1], 0);
            let (a, b, d) = unsafe { pack_short::<32>(hdr, left, right) };
            m1[l] = a;
            m2[l] = b;
            m3[l] = d;
        }
        let (m0, a1, e1) = unsafe { load_shared_head::<2>(&head) };
        let (x, _) = unsafe { finish_from_r4::<2, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) };
        for l in 0..2 {
            unsafe { vst1q_u8(vals[j + l].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[l]))) };
        }
        j += 2;
    }
    if j < count {
        let hdr = unsafe { make_hdr(word2, first + j as u32) };
        let left = arm::load_be(&vals[2 * j], 0);
        let right = arm::load_be(&vals[2 * j + 1], 0);
        let (a, b, d) = unsafe { pack_short::<32>(hdr, left, right) };
        let (m0, a1, e1) = unsafe { load_shared_head::<1>(&head) };
        let (x, _) = unsafe { finish_from_r4::<1, false>(state, a1, e1, m0, [a], [b], [d], k_ptr) };
        unsafe { vst1q_u8(vals[j].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[0]))) };
    }
}

/// Fused FORS PRF + leaf `F` in registers for `out.len()` consecutive leaves
/// starting at `first_idx`.
pub(crate) fn fors_leaves<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    first_idx: u32,
    out: &mut [[u8; N]],
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { fors_leaves_active::<N>(state, sk_seed, adrs, first_idx, out) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn fors_leaves_active<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    first_idx: u32,
    out: &mut [[u8; N]],
) {
    let prf_adrs = adrs.with_type(FORS_PRF).with_keypair(adrs.keypair);
    let tree_adrs = adrs.with_type(FORS_TREE).with_keypair(adrs.keypair);
    let p_head = unsafe { make_head(state, prf_adrs) };
    let t_head = unsafe { make_head(state, tree_adrs) };
    let (sk_x, sk_xb) = unsafe { load_n::<N>(sk_seed) };

    let n = out.len();
    let mut j = 0usize;
    while j + 4 <= n {
        let base_idx = first_idx + j as u32;
        let hdrs = [
            unsafe { make_hdr(0, base_idx) },
            unsafe { make_hdr(0, base_idx + 1) },
            unsafe { make_hdr(0, base_idx + 2) },
            unsafe { make_hdr(0, base_idx + 3) },
        ];
        let mut x = [sk_x; 4];
        let mut xb = [sk_xb; 4];
        step4_shared_head::<N>(state, &p_head, &hdrs, &mut x, &mut xb);
        step4_shared_head::<N>(state, &t_head, &hdrs, &mut x, &mut xb);
        for l in 0..4 {
            unsafe { store_n::<N>(&mut out[j + l], x[l], xb[l]) };
        }
        j += 4;
    }
    if j < n {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        while j + 2 <= n {
            let h0 = unsafe { make_hdr(0, first_idx + j as u32) };
            let h1 = unsafe { make_hdr(0, first_idx + (j + 1) as u32) };
            let (p0a, p0b, p0c) = unsafe { pack_short::<N>(h0, sk_x, sk_xb) };
            let (p1a, p1b, p1c) = unsafe { pack_short::<N>(h1, sk_x, sk_xb) };
            let (m0p, a1p, e1p) = unsafe { load_shared_head::<2>(&p_head) };
            let (x, xb) = if N == 16 {
                unsafe { finish_from_r4::<2, false>(state, a1p, e1p, m0p, [p0a, p1a], [p0b, p1b], [p0c, p1c], k_ptr) }
            } else {
                unsafe { finish_from_r4::<2, true>(state, a1p, e1p, m0p, [p0a, p1a], [p0b, p1b], [p0c, p1c], k_ptr) }
            };
            let (a0, b0, d0) = unsafe { pack_short::<N>(h0, x[0], xb[0]) };
            let (a1, b1, d1) = unsafe { pack_short::<N>(h1, x[1], xb[1]) };
            let (m0t, a1t, e1t) = unsafe { load_shared_head::<2>(&t_head) };
            let (lx, lxb) = if N == 16 {
                unsafe { finish_from_r4::<2, false>(state, a1t, e1t, m0t, [a0, a1], [b0, b1], [d0, d1], k_ptr) }
            } else {
                unsafe { finish_from_r4::<2, true>(state, a1t, e1t, m0t, [a0, a1], [b0, b1], [d0, d1], k_ptr) }
            };
            unsafe {
                store_n::<N>(&mut out[j], lx[0], lxb[0]);
                store_n::<N>(&mut out[j + 1], lx[1], lxb[1]);
            }
            j += 2;
        }
        if j < n {
            let h0 = unsafe { make_hdr(0, first_idx + j as u32) };
            let (p0a, p0b, p0c) = unsafe { pack_short::<N>(h0, sk_x, sk_xb) };
            let (m0p, a1p, e1p) = unsafe { load_shared_head::<1>(&p_head) };
            let (x, xb) = if N == 16 {
                unsafe { finish_from_r4::<1, false>(state, a1p, e1p, m0p, [p0a], [p0b], [p0c], k_ptr) }
            } else {
                unsafe { finish_from_r4::<1, true>(state, a1p, e1p, m0p, [p0a], [p0b], [p0c], k_ptr) }
            };
            let (a0, b0, d0) = unsafe { pack_short::<N>(h0, x[0], xb[0]) };
            let (m0t, a1t, e1t) = unsafe { load_shared_head::<1>(&t_head) };
            let (lx, lxb) = if N == 16 {
                unsafe { finish_from_r4::<1, false>(state, a1t, e1t, m0t, [a0], [b0], [d0], k_ptr) }
            } else {
                unsafe { finish_from_r4::<1, true>(state, a1t, e1t, m0t, [a0], [b0], [d0], k_ptr) }
            };
            unsafe { store_n::<N>(&mut out[j], lx[0], lxb[0]) };
        }
    }
}

/// Compute `k` FORS verification leaves `F(sk_i)` in 4-way lockstep directly
/// from `sig` into `vals[..k]`.
pub(crate) fn fors_verify_leaves<const N: usize>(
    state: &[u32; 8],
    adrs: Adrs,
    sig: &[u8],
    indices: &[u32],
    vals: &mut [[u8; N]],
    height: usize,
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { fors_verify_leaves_active::<N>(state, adrs, sig, indices, vals, height) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn fors_verify_leaves_active<const N: usize>(
    state: &[u32; 8],
    adrs: Adrs,
    sig: &[u8],
    indices: &[u32],
    vals: &mut [[u8; N]],
    height: usize,
) {
    let head = unsafe { make_head(state, adrs.with_word2(0)) };
    let stride = N * (height + 1);
    let z = vdupq_n_u32(0);
    let k = vals.len();
    let mut i = 0usize;
    while i + 4 <= k {
        let mut x = [z; 4];
        let mut xb = [z; 4];
        let mut hdrs = [unsafe { make_hdr(0, 0) }; 4];
        for l in 0..4 {
            let idx = i + l;
            let (sx, sxb) = unsafe { load_n::<N>(&sig[idx * stride..]) };
            x[l] = sx;
            xb[l] = sxb;
            hdrs[l] = unsafe { make_hdr(0, indices[idx]) };
        }
        step4_shared_head::<N>(state, &head, &hdrs, &mut x, &mut xb);
        for l in 0..4 {
            unsafe { store_n::<N>(&mut vals[i + l], x[l], xb[l]) };
        }
        i += 4;
    }
    let rem = k - i;
    if rem > 0 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        if rem == 3 {
            let mut m1 = [z; 3];
            let mut m2 = [z; 3];
            let mut m3 = [z; 3];
            for l in 0..3 {
                let idx = i + l;
                let (sx, sxb) = unsafe { load_n::<N>(&sig[idx * stride..]) };
                let hdr = unsafe { make_hdr(0, indices[idx]) };
                let (a, b, d) = unsafe { pack_short::<N>(hdr, sx, sxb) };
                m1[l] = a;
                m2[l] = b;
                m3[l] = d;
            }
            let (m0, a1, e1) = unsafe { load_shared_head::<3>(&head) };
            let (x, xb) = if N == 16 {
                unsafe { finish_from_r4::<3, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            } else {
                unsafe { finish_from_r4::<3, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            };
            for l in 0..3 {
                unsafe { store_n::<N>(&mut vals[i + l], x[l], xb[l]) };
            }
        } else if rem == 2 {
            let mut m1 = [z; 2];
            let mut m2 = [z; 2];
            let mut m3 = [z; 2];
            for l in 0..2 {
                let idx = i + l;
                let (sx, sxb) = unsafe { load_n::<N>(&sig[idx * stride..]) };
                let hdr = unsafe { make_hdr(0, indices[idx]) };
                let (a, b, d) = unsafe { pack_short::<N>(hdr, sx, sxb) };
                m1[l] = a;
                m2[l] = b;
                m3[l] = d;
            }
            let (m0, a1, e1) = unsafe { load_shared_head::<2>(&head) };
            let (x, xb) = if N == 16 {
                unsafe { finish_from_r4::<2, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            } else {
                unsafe { finish_from_r4::<2, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            };
            for l in 0..2 {
                unsafe { store_n::<N>(&mut vals[i + l], x[l], xb[l]) };
            }
        } else {
            let (sx, sxb) = unsafe { load_n::<N>(&sig[i * stride..]) };
            let hdr = unsafe { make_hdr(0, indices[i]) };
            let (a, b, d) = unsafe { pack_short::<N>(hdr, sx, sxb) };
            let (m0, a1, e1) = unsafe { load_shared_head::<1>(&head) };
            let (x, xb) = if N == 16 {
                unsafe { finish_from_r4::<1, false>(state, a1, e1, m0, [a], [b], [d], k_ptr) }
            } else {
                unsafe { finish_from_r4::<1, true>(state, a1, e1, m0, [a], [b], [d], k_ptr) }
            };
            unsafe { store_n::<N>(&mut vals[i], x[0], xb[0]) };
        }
    }
}

/// Climb one level of `k` FORS authentication paths for `N = 16` in 4-way lockstep.
pub(crate) fn fors_path_level_16(
    state: &[u32; 8],
    adrs: Adrs,
    sig: &[u8],
    indices: &mut [u32],
    vals: &mut [[u8; 16]],
    height: usize,
    level_offset: usize,
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { fors_path_level_16_active(state, adrs, sig, indices, vals, height, level_offset) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn fors_path_level_16_active(
    state: &[u32; 8],
    adrs: Adrs,
    sig: &[u8],
    indices: &mut [u32],
    vals: &mut [[u8; 16]],
    height: usize,
    level_offset: usize,
) {
    let word2 = (level_offset + 1) as u32;
    let head = unsafe { make_head(state, adrs.with_word2(word2)) };
    let stride = 16 * (height + 1);
    let sib_off = 16 * (1 + level_offset);
    let z = vdupq_n_u32(0);
    let k = vals.len();
    let mut i = 0usize;
    while i + 4 <= k {
        let mut x = [z; 4];
        let mut xb = [z; 4];
        let mut hdrs = [unsafe { make_hdr(0, 0) }; 4];
        for l in 0..4 {
            let idx = i + l;
            let pos = indices[idx];
            let parent = pos >> 1;
            indices[idx] = parent;
            let node = arm::load_be(&vals[idx], 0);
            let sib = arm::load_be(&sig[idx * stride + sib_off..], 0);
            let (left, right) = if pos & 1 == 0 { (node, sib) } else { (sib, node) };
            x[l] = left;
            xb[l] = right;
            hdrs[l] = unsafe { make_hdr(word2, parent) };
        }
        step4_shared_head::<32>(state, &head, &hdrs, &mut x, &mut xb);
        for l in 0..4 {
            unsafe { vst1q_u8(vals[i + l].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[l]))) };
        }
        i += 4;
    }
    let rem = k - i;
    if rem > 0 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        if rem == 3 {
            let mut m1 = [z; 3];
            let mut m2 = [z; 3];
            let mut m3 = [z; 3];
            for l in 0..3 {
                let idx = i + l;
                let pos = indices[idx];
                let parent = pos >> 1;
                indices[idx] = parent;
                let node = arm::load_be(&vals[idx], 0);
                let sib = arm::load_be(&sig[idx * stride + sib_off..], 0);
                let (left, right) = if pos & 1 == 0 { (node, sib) } else { (sib, node) };
                let hdr = unsafe { make_hdr(word2, parent) };
                let (a, b, d) = unsafe { pack_short::<32>(hdr, left, right) };
                m1[l] = a;
                m2[l] = b;
                m3[l] = d;
            }
            let (m0, a1, e1) = unsafe { load_shared_head::<3>(&head) };
            let (x, _) = unsafe { finish_from_r4::<3, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) };
            for l in 0..3 {
                unsafe { vst1q_u8(vals[i + l].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[l]))) };
            }
        } else if rem == 2 {
            let mut m1 = [z; 2];
            let mut m2 = [z; 2];
            let mut m3 = [z; 2];
            for l in 0..2 {
                let idx = i + l;
                let pos = indices[idx];
                let parent = pos >> 1;
                indices[idx] = parent;
                let node = arm::load_be(&vals[idx], 0);
                let sib = arm::load_be(&sig[idx * stride + sib_off..], 0);
                let (left, right) = if pos & 1 == 0 { (node, sib) } else { (sib, node) };
                let hdr = unsafe { make_hdr(word2, parent) };
                let (a, b, d) = unsafe { pack_short::<32>(hdr, left, right) };
                m1[l] = a;
                m2[l] = b;
                m3[l] = d;
            }
            let (m0, a1, e1) = unsafe { load_shared_head::<2>(&head) };
            let (x, _) = unsafe { finish_from_r4::<2, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) };
            for l in 0..2 {
                unsafe { vst1q_u8(vals[i + l].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[l]))) };
            }
        } else {
            let pos = indices[i];
            let parent = pos >> 1;
            indices[i] = parent;
            let node = arm::load_be(&vals[i], 0);
            let sib = arm::load_be(&sig[i * stride + sib_off..], 0);
            let (left, right) = if pos & 1 == 0 { (node, sib) } else { (sib, node) };
            let hdr = unsafe { make_hdr(word2, parent) };
            let (a, b, d) = unsafe { pack_short::<32>(hdr, left, right) };
            let (m0, a1, e1) = unsafe { load_shared_head::<1>(&head) };
            let (x, _) = unsafe { finish_from_r4::<1, false>(state, a1, e1, m0, [a], [b], [d], k_ptr) };
            unsafe { vst1q_u8(vals[i].as_mut_ptr(), vrev32q_u8(vreinterpretq_u8_u32(x[0]))) };
        }
    }
}

/// Bucket-sort chain indices `0..len` in descending order of `weights[i]` (range `0..=15`),
/// returning only chains with `weights[i] > 0` in `order[..count]`.
#[inline]
fn sort_descending(weights: &[u32], order: &mut [u8; LEN_MAX]) -> usize {
    let mut counts = [0u8; 16];
    for &w in weights {
        if w > 0 {
            counts[w as usize] += 1;
        }
    }
    let mut offsets = [0usize; 16];
    let mut total = 0usize;
    let mut b = 15usize;
    while b >= 1 {
        offsets[b] = total;
        total += counts[b] as usize;
        b -= 1;
    }
    for (i, &w) in weights.iter().enumerate() {
        if w > 0 {
            let pos = offsets[w as usize];
            order[pos] = i as u8;
            offsets[w as usize] = pos + 1;
        }
    }
    total
}

/// Sorted dynamic lane-refill 4-lane WOTS+ verification recovery.
/// Writes all `len` recovered endpoints directly into `buf[22 + c * N ..]`.
pub(crate) fn wots_recover<const N: usize>(
    state: &[u32; 8],
    adrs: Adrs,
    sig: &[u8],
    digits: &[u32],
    buf: &mut [u8],
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { wots_recover_active::<N>(state, adrs, sig, digits, buf) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn wots_recover_active<const N: usize>(
    state: &[u32; 8],
    adrs: Adrs,
    sig: &[u8],
    digits: &[u32],
    buf: &mut [u8],
) {
    let len = digits.len();
    let mut rem_weights = [0u32; LEN_MAX];
    for i in 0..len {
        let d = digits[i];
        if d == 15 {
            buf[22 + i * N..22 + (i + 1) * N].copy_from_slice(&sig[i * N..(i + 1) * N]);
        } else {
            rem_weights[i] = 15 - d;
        }
    }
    let mut order = [0u8; LEN_MAX];
    let total = sort_descending(&rem_weights[..len], &mut order);
    if total == 0 {
        return;
    }

    let head = unsafe { make_head(state, adrs) };
    let z = vdupq_n_u32(0);

    let mut x = [z; 4];
    let mut xb = [z; 4];
    let mut chain = [0usize; 4];
    let mut cur_t = [0u32; 4];
    let mut left = [0u32; 4];
    let mut active = 0usize;
    let mut next = 0usize;

    while active < 4 && next < total {
        let c = order[next] as usize;
        next += 1;
        let (vx, vxb) = unsafe { load_n::<N>(&sig[c * N..]) };
        x[active] = vx;
        xb[active] = vxb;
        chain[active] = c;
        cur_t[active] = digits[c];
        left[active] = 15 - digits[c];
        active += 1;
    }

    // Hot 4-lane loop: run `min_left` consecutive steps in registers before refilling!
    while active == 4 {
        let min_left = left[0].min(left[1]).min(left[2]).min(left[3]);
        run_shared4_steps::<N>(
            state,
            &head,
            [chain[0] as u32, chain[1] as u32, chain[2] as u32, chain[3] as u32],
            cur_t,
            min_left,
            &mut x,
            &mut xb,
        );
        for l in 0..4 {
            cur_t[l] += min_left;
            left[l] -= min_left;
            if left[l] == 0 {
                let c = chain[l];
                unsafe { store_n::<N>(&mut buf[22 + c * N..], x[l], xb[l]) };
                if next < total {
                    let nc = order[next] as usize;
                    next += 1;
                    let (vx, vxb) = unsafe { load_n::<N>(&sig[nc * N..]) };
                    x[l] = vx;
                    xb[l] = vxb;
                    chain[l] = nc;
                    cur_t[l] = digits[nc];
                    left[l] = 15 - digits[nc];
                }
            }
        }
        if left[0] == 0 || left[1] == 0 || left[2] == 0 || left[3] == 0 {
            let mut k = 0;
            for l in 0..4 {
                if left[l] > 0 {
                    x[k] = x[l];
                    xb[k] = xb[l];
                    chain[k] = chain[l];
                    cur_t[k] = cur_t[l];
                    left[k] = left[l];
                    k += 1;
                }
            }
            active = k;
        }
    }

    while active > 0 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        if active == 3 {
            let mut m1 = [z; 3];
            let mut m2 = [z; 3];
            let mut m3 = [z; 3];
            for l in 0..3 {
                let (a, b, d) = unsafe { pack_short::<N>(make_hdr(chain[l] as u32, cur_t[l]), x[l], xb[l]) };
                m1[l] = a;
                m2[l] = b;
                m3[l] = d;
            }
            let (m0, a1, e1) = unsafe { load_shared_head::<3>(&head) };
            let (nx, nxb) = if N == 16 {
                unsafe { finish_from_r4::<3, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            } else {
                unsafe { finish_from_r4::<3, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            };
            for l in 0..3 {
                x[l] = nx[l];
                xb[l] = nxb[l];
            }
        } else if active == 2 {
            let (a0, b0, d0) = unsafe { pack_short::<N>(make_hdr(chain[0] as u32, cur_t[0]), x[0], xb[0]) };
            let (a1p, b1p, d1p) = unsafe { pack_short::<N>(make_hdr(chain[1] as u32, cur_t[1]), x[1], xb[1]) };
            let (m0, a1, e1) = unsafe { load_shared_head::<2>(&head) };
            let (nx, nxb) = if N == 16 {
                unsafe { finish_from_r4::<2, false>(state, a1, e1, m0, [a0, a1p], [b0, b1p], [d0, d1p], k_ptr) }
            } else {
                unsafe { finish_from_r4::<2, true>(state, a1, e1, m0, [a0, a1p], [b0, b1p], [d0, d1p], k_ptr) }
            };
            x[0] = nx[0];
            xb[0] = nxb[0];
            x[1] = nx[1];
            xb[1] = nxb[1];
        } else {
            let (a0, b0, d0) = unsafe { pack_short::<N>(make_hdr(chain[0] as u32, cur_t[0]), x[0], xb[0]) };
            let (m0, a1, e1) = unsafe { load_shared_head::<1>(&head) };
            let (nx, nxb) = if N == 16 {
                unsafe { finish_from_r4::<1, false>(state, a1, e1, m0, [a0], [b0], [d0], k_ptr) }
            } else {
                unsafe { finish_from_r4::<1, true>(state, a1, e1, m0, [a0], [b0], [d0], k_ptr) }
            };
            x[0] = nx[0];
            xb[0] = nxb[0];
        }
        let mut k = 0;
        for l in 0..active {
            cur_t[l] += 1;
            left[l] -= 1;
            if left[l] == 0 {
                let c = chain[l];
                unsafe { store_n::<N>(&mut buf[22 + c * N..], x[l], xb[l]) };
            } else {
                x[k] = x[l];
                xb[k] = xb[l];
                chain[k] = chain[l];
                cur_t[k] = cur_t[l];
                left[k] = left[l];
                k += 1;
            }
        }
        active = k;
    }
}

/// Fused + sorted dynamic lane-refill 4-lane WOTS+ signing.
/// Runs PRF + `digits[c]` chain steps for all `len` chains directly into `sig`.
pub(crate) fn wots_sign_fused<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    digits: &[u32],
    sig: &mut [u8],
) {
    debug_assert!(available());
    // SAFETY: caller verified arm::available().
    unsafe { wots_sign_fused_active::<N>(state, sk_seed, adrs, digits, sig) };
}

#[target_feature(enable = "neon,sha2")]
#[allow(unused_unsafe)]
fn wots_sign_fused_active<const N: usize>(
    state: &[u32; 8],
    sk_seed: &[u8; N],
    adrs: Adrs,
    digits: &[u32],
    sig: &mut [u8],
) {
    let len = digits.len();
    let mut counts = [0u8; 16];
    for &d in digits {
        counts[d as usize] += 1;
    }
    let mut offsets = [0usize; 16];
    let mut total = 0usize;
    let mut b = 15isize;
    while b >= 0 {
        offsets[b as usize] = total;
        total += counts[b as usize] as usize;
        b -= 1;
    }
    let mut order = [0u8; LEN_MAX];
    for (i, &d) in digits.iter().enumerate() {
        let pos = offsets[d as usize];
        order[pos] = i as u8;
        offsets[d as usize] = pos + 1;
    }

    let (sk_x, sk_xb) = unsafe { load_n::<N>(sk_seed) };
    let prf_head = unsafe { make_head(state, adrs.with_type(WOTS_PRF).with_keypair(adrs.keypair)) };
    let hash_head = unsafe { make_head(state, adrs.with_type(WOTS_HASH).with_keypair(adrs.keypair)) };
    let z = vdupq_n_u32(0);

    let mut x = [z; 4];
    let mut xb = [z; 4];
    let mut heads = [prf_head; 4];
    let mut chain = [0usize; 4];
    let mut cur_t = [0u32; 4];
    let mut left = [0u32; 4];
    let mut is_prf = [false; 4];
    let mut active = 0usize;
    let mut next = 0usize;

    while active < 4 && next < len {
        let c = order[next] as usize;
        next += 1;
        x[active] = sk_x;
        xb[active] = sk_xb;
        heads[active] = prf_head;
        chain[active] = c;
        cur_t[active] = 0;
        left[active] = 1 + digits[c];
        is_prf[active] = true;
        active += 1;
    }

    while active == 4 {
        if !(is_prf[0] || is_prf[1] || is_prf[2] || is_prf[3]) {
            let min_left = left[0].min(left[1]).min(left[2]).min(left[3]);
            run_shared4_steps::<N>(
                state,
                &hash_head,
                [chain[0] as u32, chain[1] as u32, chain[2] as u32, chain[3] as u32],
                cur_t,
                min_left,
                &mut x,
                &mut xb,
            );
            for l in 0..4 {
                cur_t[l] += min_left;
                left[l] -= min_left;
                if left[l] == 0 {
                    let c = chain[l];
                    unsafe { store_n::<N>(&mut sig[c * N..], x[l], xb[l]) };
                    if next < len {
                        let nc = order[next] as usize;
                        next += 1;
                        x[l] = sk_x;
                        xb[l] = sk_xb;
                        heads[l] = prf_head;
                        chain[l] = nc;
                        cur_t[l] = 0;
                        left[l] = 1 + digits[nc];
                        is_prf[l] = true;
                    }
                }
            }
        } else {
            let hdrs = [
                unsafe { make_hdr(chain[0] as u32, cur_t[0]) },
                unsafe { make_hdr(chain[1] as u32, cur_t[1]) },
                unsafe { make_hdr(chain[2] as u32, cur_t[2]) },
                unsafe { make_hdr(chain[3] as u32, cur_t[3]) },
            ];
            step4_distinct_heads::<N>(state, &heads, &hdrs, &mut x, &mut xb);
            for l in 0..4 {
                left[l] -= 1;
                if left[l] == 0 {
                    let c = chain[l];
                    unsafe { store_n::<N>(&mut sig[c * N..], x[l], xb[l]) };
                    if next < len {
                        let nc = order[next] as usize;
                        next += 1;
                        x[l] = sk_x;
                        xb[l] = sk_xb;
                        heads[l] = prf_head;
                        chain[l] = nc;
                        cur_t[l] = 0;
                        left[l] = 1 + digits[nc];
                        is_prf[l] = true;
                    }
                } else if is_prf[l] {
                    is_prf[l] = false;
                    heads[l] = hash_head;
                } else {
                    cur_t[l] += 1;
                }
            }
        }
        if left[0] == 0 || left[1] == 0 || left[2] == 0 || left[3] == 0 {
            let mut k = 0;
            for l in 0..4 {
                if left[l] > 0 {
                    x[k] = x[l];
                    xb[k] = xb[l];
                    heads[k] = heads[l];
                    chain[k] = chain[l];
                    cur_t[k] = cur_t[l];
                    left[k] = left[l];
                    is_prf[k] = is_prf[l];
                    k += 1;
                }
            }
            active = k;
        }
    }

    while active > 0 {
        let k_ptr = core::hint::black_box(super::K.as_ptr());
        if active == 3 {
            let mut m1 = [z; 3];
            let mut m2 = [z; 3];
            let mut m3 = [z; 3];
            for l in 0..3 {
                let (a, b, d) = unsafe { pack_short::<N>(make_hdr(chain[l] as u32, cur_t[l]), x[l], xb[l]) };
                m1[l] = a;
                m2[l] = b;
                m3[l] = d;
            }
            let (m0, a1, e1) = unsafe { load_heads::<3>(&[heads[0], heads[1], heads[2]]) };
            let (nx, nxb) = if N == 16 {
                unsafe { finish_from_r4::<3, false>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            } else {
                unsafe { finish_from_r4::<3, true>(state, a1, e1, m0, m1, m2, m3, k_ptr) }
            };
            for l in 0..3 {
                x[l] = nx[l];
                xb[l] = nxb[l];
            }
        } else if active == 2 {
            let (a0, b0, d0) = unsafe { pack_short::<N>(make_hdr(chain[0] as u32, cur_t[0]), x[0], xb[0]) };
            let (a1p, b1p, d1p) = unsafe { pack_short::<N>(make_hdr(chain[1] as u32, cur_t[1]), x[1], xb[1]) };
            let (m0, a1, e1) = unsafe { load_heads::<2>(&[heads[0], heads[1]]) };
            let (nx, nxb) = if N == 16 {
                unsafe { finish_from_r4::<2, false>(state, a1, e1, m0, [a0, a1p], [b0, b1p], [d0, d1p], k_ptr) }
            } else {
                unsafe { finish_from_r4::<2, true>(state, a1, e1, m0, [a0, a1p], [b0, b1p], [d0, d1p], k_ptr) }
            };
            x[0] = nx[0];
            xb[0] = nxb[0];
            x[1] = nx[1];
            xb[1] = nxb[1];
        } else {
            let (a0, b0, d0) = unsafe { pack_short::<N>(make_hdr(chain[0] as u32, cur_t[0]), x[0], xb[0]) };
            let (m0, a1, e1) = unsafe { load_heads::<1>(&[heads[0]]) };
            let (nx, nxb) = if N == 16 {
                unsafe { finish_from_r4::<1, false>(state, a1, e1, m0, [a0], [b0], [d0], k_ptr) }
            } else {
                unsafe { finish_from_r4::<1, true>(state, a1, e1, m0, [a0], [b0], [d0], k_ptr) }
            };
            x[0] = nx[0];
            xb[0] = nxb[0];
        }
        let mut k = 0;
        for l in 0..active {
            left[l] -= 1;
            if left[l] == 0 {
                let c = chain[l];
                unsafe { store_n::<N>(&mut sig[c * N..], x[l], xb[l]) };
            } else {
                if is_prf[l] {
                    is_prf[l] = false;
                    heads[l] = hash_head;
                } else {
                    cur_t[l] += 1;
                }
                x[k] = x[l];
                xb[k] = xb[l];
                heads[k] = heads[l];
                chain[k] = chain[l];
                cur_t[k] = cur_t[l];
                left[k] = left[l];
                is_prf[k] = is_prf[l];
                k += 1;
            }
        }
        active = k;
    }
}
