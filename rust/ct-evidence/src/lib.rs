//! Harness shared by the two evidence binaries (`cttrace`, `dudect`).
//!
//! Every function under test is wrapped in an `extern "C" fn(input, output)`
//! entry point with a flat byte layout, so that the emulator can call it with
//! two pointers and the timing harness can call it natively. The wrappers are
//! thin: they decode public parameters, call the `slhdsa` function, and copy
//! the result out.
//!
//! Common input layout (not every wrapper uses every field):
//!
//! ```text
//!   0..4    a      u32 LE   (i / idx / length, public)
//!   4       z      u8       (tree height z, or chain step count s, public)
//!   5       ci     u8       (chain start index i, public)
//!   6..8    b      u16 LE   (second length, public)
//!   8..16   t      u64 LE   (idx_tree, public)
//!   16..32  pk_seed          (public)
//!   32..64  ADRS fields      (public)
//!   64..80  sk_seed / chain start value x / SK.prf   (SECRET)
//!   80..96  16-byte message m (public) or addrnd / opt_rand (SECRET)
//!   96..    variable-length data
//! ```

use slhdsa::address::Adrs;

pub type Entry = extern "C" fn(*const u8, *mut u8);

pub const IN_MAX: usize = 4096;
pub const OUT_MAX: usize = 16384;

pub const OFF_A: usize = 0;
pub const OFF_Z: usize = 4;
pub const OFF_CI: usize = 5;
pub const OFF_B: usize = 6;
pub const OFF_T: usize = 8;
pub const OFF_PKSEED: usize = 16;
pub const OFF_ADRS: usize = 32;
pub const OFF_SEC: usize = 64;
pub const OFF_M16: usize = 80;
pub const OFF_DATA: usize = 96;

#[inline(always)]
unsafe fn inp<'a>(p: *const u8) -> &'a [u8] {
    core::slice::from_raw_parts(p, IN_MAX)
}
#[inline(always)]
unsafe fn outp<'a>(p: *mut u8) -> &'a mut [u8] {
    core::slice::from_raw_parts_mut(p, OUT_MAX)
}
fn u32at(b: &[u8], o: usize) -> u32 {
    u32::from_le_bytes([b[o], b[o + 1], b[o + 2], b[o + 3]])
}
fn u64at(b: &[u8], o: usize) -> u64 {
    let mut x = [0u8; 8];
    x.copy_from_slice(&b[o..o + 8]);
    u64::from_le_bytes(x)
}
fn a16(b: &[u8], o: usize) -> [u8; 16] {
    let mut x = [0u8; 16];
    x.copy_from_slice(&b[o..o + 16]);
    x
}
fn adrs(b: &[u8]) -> Adrs {
    Adrs {
        layer: u32at(b, OFF_ADRS),
        tree: u64at(b, OFF_ADRS + 4),
        typ: u32at(b, OFF_ADRS + 12),
        keypair: u32at(b, OFF_ADRS + 16),
        word2: u32at(b, OFF_ADRS + 20),
        word3: u32at(b, OFF_ADRS + 24),
    }
}

// ---------------------------------------------------------------- wrappers

#[inline(never)]
pub extern "C" fn w_sha256(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::sha256::sha256(&b[OFF_DATA..OFF_DATA + len]);
    out[..32].copy_from_slice(&d);
}

/// key = in[64..64+klen] (klen = z field), msg = in[96..96+a]
#[inline(never)]
pub extern "C" fn w_hmac(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let mlen = u32at(b, OFF_A) as usize;
    let klen = b[OFF_Z] as usize;
    let d = slhdsa::sha256::hmac_sha256(&b[OFF_SEC..OFF_SEC + klen], &b[OFF_DATA..OFF_DATA + mlen]);
    out[..32].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_thash(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::hash::thash(&a16(b, OFF_PKSEED), &adrs(b), &b[OFF_DATA..OFF_DATA + len]);
    out[..16].copy_from_slice(&d);
}

/// sk_prf = in[64..80] (secret), opt_rand = in[80..96] (secret: addrnd), m = in[96..96+a] (public)
#[inline(never)]
pub extern "C" fn w_prf_msg(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::hash::prf_msg(&a16(b, OFF_SEC), &a16(b, OFF_M16), &b[OFF_DATA..OFF_DATA + len]);
    out[..16].copy_from_slice(&d);
}

/// x = in[64..80] (secret), i = ci, s = z
#[inline(never)]
pub extern "C" fn w_chain(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::wots::chain(a16(b, OFF_SEC), b[OFF_CI] as u32, b[OFF_Z] as u32, &a16(b, OFF_PKSEED), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_wots_pk_gen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::wots::wots_pk_gen(&a16(b, OFF_SEC), &a16(b, OFF_PKSEED), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_wots_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let s = slhdsa::wots::wots_sign(&a16(b, OFF_M16), &a16(b, OFF_SEC), &a16(b, OFF_PKSEED), adrs(b));
    out[..s.len()].copy_from_slice(&s);
}

#[inline(never)]
pub extern "C" fn w_xmss_node(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::xmss::xmss_node(&a16(b, OFF_SEC), u32at(b, OFF_A), b[OFF_Z] as u32, &a16(b, OFF_PKSEED), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_xmss_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let s = slhdsa::xmss::xmss_sign(&a16(b, OFF_M16), &a16(b, OFF_SEC), u32at(b, OFF_A), &a16(b, OFF_PKSEED), adrs(b));
    out[..s.len()].copy_from_slice(&s);
}

#[inline(never)]
pub extern "C" fn w_fors_sk_gen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::fors::fors_sk_gen(&a16(b, OFF_SEC), &a16(b, OFF_PKSEED), adrs(b), u32at(b, OFF_A));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_fors_node(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::fors::fors_node(&a16(b, OFF_SEC), u32at(b, OFF_A), b[OFF_Z] as u32, &a16(b, OFF_PKSEED), adrs(b));
    out[..16].copy_from_slice(&d);
}

/// md = in[96..117] (public)
#[inline(never)]
pub extern "C" fn w_fors_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let s = slhdsa::fors::fors_sign(&b[OFF_DATA..OFF_DATA + 21], &a16(b, OFF_SEC), &a16(b, OFF_PKSEED), adrs(b));
    out[..s.len()].copy_from_slice(&s);
}

/// sk_seed = in[64..80], sk_prf = in[80..96], pk_seed = in[16..32]
#[inline(never)]
pub extern "C" fn w_keygen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (sk, pk) = slhdsa::slh_keygen_internal(&a16(b, OFF_SEC), &a16(b, OFF_M16), &a16(b, OFF_PKSEED));
    out[..64].copy_from_slice(&sk);
    out[64..96].copy_from_slice(&pk);
}

pub const OFF_SK: usize = 128; // 64-byte sk: seed | prf | pk_seed | pk_root
pub const OFF_ADDRND: usize = 192;
pub const OFF_MSG: usize = 256;

/// m = in[256..256+a] (public), sk = in[128..192], addrnd = in[192..208]
#[inline(never)]
pub extern "C" fn w_sign_internal(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let mut sk = [0u8; 64];
    sk.copy_from_slice(&b[OFF_SK..OFF_SK + 64]);
    let s = slhdsa::slh_sign_internal(&b[OFF_MSG..OFF_MSG + len], &sk, &a16(b, OFF_ADDRND));
    out[..s.len()].copy_from_slice(&s);
}

/// As `w_sign_internal` plus ctx = in[1024..1024+b] (public).
#[inline(never)]
pub extern "C" fn w_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let clen = u16::from_le_bytes([b[OFF_B], b[OFF_B + 1]]) as usize;
    let mut sk = [0u8; 64];
    sk.copy_from_slice(&b[OFF_SK..OFF_SK + 64]);
    let s = slhdsa::slh_sign(&b[OFF_MSG..OFF_MSG + len], &b[1024..1024 + clen], &sk, &a16(b, OFF_ADDRND)).unwrap();
    out[..s.len()].copy_from_slice(&s);
}

// ------------------------------------------------------ positive controls
// Deliberately leaky code. These live only in this harness crate.

/// Early-exit comparison of a secret (in[64..80]) against a public guess
/// (in[80..96]): leaks the length of the matching prefix via control flow.
/// Only the low bit of each byte is compared, so that random secrets match
/// prefixes of geometrically distributed length (otherwise almost every
/// random secret would exit at byte 0 and the control would be vacuous).
#[inline(never)]
pub extern "C" fn w_leaky_cmp(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let mut k = 0;
    let mut eq = 1u8;
    while k < 16 {
        if (core::hint::black_box(b[OFF_SEC + k]) ^ b[OFF_M16 + k]) & 1 != 0 {
            eq = 0;
            break;
        }
        // some work per matching byte so the timing harness can see it too
        let mut j = 0u32;
        let mut acc = 0u32;
        while j < 200 {
            acc = core::hint::black_box(acc.wrapping_mul(31).wrapping_add(j));
            j += 1;
        }
        out[1] = acc as u8;
        k += 1;
    }
    out[0] = eq;
}

static TABLE: [u8; 256] = {
    let mut t = [0u8; 256];
    let mut i = 0;
    while i < 256 {
        t[i] = (i as u8).wrapping_mul(167).wrapping_add(13);
        i += 1;
    }
    t
};

/// Secret-indexed table lookup: leaks in[64] via the address read.
/// Control flow is constant, so only the memory-address trace can catch it.
#[inline(never)]
pub extern "C" fn w_leaky_table(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let idx = core::hint::black_box(b[OFF_SEC]) as usize;
    out[0] = core::hint::black_box(&TABLE)[idx];
}

/// Secret-dependent loop count (popcount-many dummy SHA-256 calls): a leak
/// that is easy to see in timing.
#[inline(never)]
pub extern "C" fn w_leaky_loop(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let n = core::hint::black_box(b[OFF_SEC]).count_ones();
    let mut d = [0u8; 32];
    let mut k = 0;
    while k < n {
        d = slhdsa::sha256::sha256(&d);
        k += 1;
    }
    out[..32].copy_from_slice(&d);
}

// ------------------------------------------------------------ target table

pub struct Target {
    pub name: String,
    pub f: Entry,
    /// Byte ranges (start, len) of the input that are varied between runs.
    pub vary: Vec<(usize, usize)>,
    /// Sets the public parameters after the buffer was filled with public
    /// pseudo-random bytes.
    pub fix: Box<dyn Fn(&mut [u8]) + Send + Sync>,
    /// true: the audit claims the trace is independent of `vary` (must be EQUAL).
    /// false: control, the trace is expected to DIFFER.
    pub expect_equal: bool,
    /// What `vary` is, for the report.
    pub what: &'static str,
    /// Trace experiment size: (public configurations, secrets per configuration).
    pub trials: (usize, usize),
    /// Rough native cost class for the timing harness (samples per class).
    pub dudect_n: usize,
}

fn set_u32(b: &mut [u8], o: usize, v: u32) {
    b[o..o + 4].copy_from_slice(&v.to_le_bytes());
}
fn clamp_adrs(b: &mut [u8]) {
    // keep ADRS fields in their real ranges (layer < 7, 54-bit tree, 9-bit keypair)
    let l = u32at(b, OFF_ADRS) % 7;
    set_u32(b, OFF_ADRS, l);
    let t = u64at(b, OFF_ADRS + 4) & ((1u64 << 54) - 1);
    b[OFF_ADRS + 4..OFF_ADRS + 12].copy_from_slice(&t.to_le_bytes());
    let ty = u32at(b, OFF_ADRS + 12) % 7;
    set_u32(b, OFF_ADRS + 12, ty);
    let kp = u32at(b, OFF_ADRS + 16) & 511;
    set_u32(b, OFF_ADRS + 16, kp);
}

pub fn targets() -> Vec<Target> {
    let mut v: Vec<Target> = Vec::new();
    let sec16 = vec![(OFF_SEC, 16)];

    for &len in &[1usize, 16, 55, 56, 64, 119, 120, 256, 560] {
        v.push(Target {
            name: format!("sha256/len={len}"),
            f: w_sha256,
            vary: vec![(OFF_DATA, len)],
            fix: Box::new(move |b| set_u32(b, OFF_A, len as u32)),
            expect_equal: true,
            what: "all message bytes",
            trials: (1, 64),
            dudect_n: 200_000,
        });
    }
    for &(klen, mlen) in &[(16usize, 32usize), (16, 150), (64, 64), (32, 1)] {
        v.push(Target {
            name: format!("hmac_sha256/klen={klen},mlen={mlen}"),
            f: w_hmac,
            vary: vec![(OFF_SEC, klen), (OFF_DATA, mlen)],
            fix: Box::new(move |b| {
                set_u32(b, OFF_A, mlen as u32);
                b[OFF_Z] = klen as u8;
            }),
            expect_equal: true,
            what: "key and message bytes",
            trials: (1, 64),
            dudect_n: 100_000,
        });
    }
    for &len in &[16usize, 32, 560, 224] {
        v.push(Target {
            name: format!("thash/len={len}"),
            f: w_thash,
            vary: vec![(OFF_DATA, len)],
            fix: Box::new(move |b| {
                set_u32(b, OFF_A, len as u32);
                clamp_adrs(b)
            }),
            expect_equal: true,
            what: "m (e.g. SK.seed / chain value / node values)",
            trials: (4, 16),
            dudect_n: 200_000,
        });
    }
    for &len in &[0usize, 32, 100, 1000] {
        v.push(Target {
            name: format!("prf_msg/mlen={len}"),
            f: w_prf_msg,
            vary: vec![(OFF_SEC, 16), (OFF_M16, 16)],
            fix: Box::new(move |b| set_u32(b, OFF_A, len as u32)),
            expect_equal: true,
            what: "SK.prf and opt_rand(addrnd)",
            trials: (4, 16),
            dudect_n: 100_000,
        });
    }
    for &(ci, s) in &[(0u8, 15u8), (0, 1), (3, 7), (15, 0), (0, 0)] {
        v.push(Target {
            name: format!("chain/i={ci},s={s}"),
            f: w_chain,
            vary: sec16.clone(),
            fix: Box::new(move |b| {
                b[OFF_CI] = ci;
                b[OFF_Z] = s;
                clamp_adrs(b)
            }),
            expect_equal: true,
            what: "start value x",
            trials: (4, 16),
            dudect_n: 100_000,
        });
    }
    v.push(Target {
        name: "wots_pk_gen".into(),
        f: w_wots_pk_gen,
        vary: sec16.clone(),
        fix: Box::new(clamp_adrs),
        expect_equal: true,
        what: "SK.seed",
        trials: (4, 16),
        dudect_n: 50_000,
    });
    v.push(Target {
        name: "wots_sign".into(),
        f: w_wots_sign,
        vary: sec16.clone(),
        fix: Box::new(clamp_adrs),
        expect_equal: true,
        what: "SK.seed (message m public, fixed)",
        trials: (8, 8),
        dudect_n: 50_000,
    });
    for &z in &[0u8, 1, 2, 3, 4] {
        v.push(Target {
            name: format!("xmss_node/z={z}"),
            f: w_xmss_node,
            vary: sec16.clone(),
            fix: Box::new(move |b| {
                b[OFF_Z] = z;
                let i = u32at(b, OFF_A) & ((1u32 << (9 - z)) - 1);
                set_u32(b, OFF_A, i);
                clamp_adrs(b)
            }),
            expect_equal: true,
            what: "SK.seed",
            trials: if z <= 2 { (4, 16) } else { (2, 16) },
            dudect_n: if z <= 1 { 10_000 } else { 3_000 },
        });
    }
    v.push(Target {
        name: "xmss_sign".into(),
        f: w_xmss_sign,
        vary: sec16.clone(),
        fix: Box::new(|b| {
            let i = u32at(b, OFF_A) & 511;
            set_u32(b, OFF_A, i);
            clamp_adrs(b)
        }),
        expect_equal: true,
        what: "SK.seed (m, idx public, fixed)",
        trials: (2, 8),
        dudect_n: 500,
    });
    v.push(Target {
        name: "fors_sk_gen".into(),
        f: w_fors_sk_gen,
        vary: sec16.clone(),
        fix: Box::new(clamp_adrs),
        expect_equal: true,
        what: "SK.seed",
        trials: (4, 16),
        dudect_n: 200_000,
    });
    for &z in &[0u8, 1, 3, 6, 12] {
        v.push(Target {
            name: format!("fors_node/z={z}"),
            f: w_fors_node,
            vary: sec16.clone(),
            fix: Box::new(move |b| {
                b[OFF_Z] = z;
                let i = u32at(b, OFF_A) % (14u32 << (12 - z));
                set_u32(b, OFF_A, i);
                clamp_adrs(b)
            }),
            expect_equal: true,
            what: "SK.seed",
            trials: if z <= 6 { (4, 16) } else { (2, 8) },
            dudect_n: match z {
                0 | 1 => 100_000,
                3 => 30_000,
                6 => 5_000,
                _ => 2_000,
            },
        });
    }
    v.push(Target {
        name: "fors_sign".into(),
        f: w_fors_sign,
        vary: sec16.clone(),
        fix: Box::new(clamp_adrs),
        expect_equal: true,
        what: "SK.seed (md public, fixed)",
        trials: (2, 8),
        dudect_n: 300,
    });
    v.push(Target {
        name: "slh_keygen_internal".into(),
        f: w_keygen,
        vary: vec![(OFF_SEC, 32)],
        fix: Box::new(|_| {}),
        expect_equal: true,
        what: "SK.seed and SK.prf (PK.seed fixed)",
        trials: (2, 12),
        dudect_n: 1000,
    });
    v.push(Target {
        name: "slh_keygen_internal/all-inputs".into(),
        f: w_keygen,
        vary: vec![(OFF_SEC, 32), (OFF_PKSEED, 16)],
        fix: Box::new(|_| {}),
        expect_equal: true,
        what: "SK.seed, SK.prf and PK.seed",
        trials: (1, 12),
        dudect_n: 0,
    });

    // Informational: FORS signing never branches on the digest (the indices only
    // flow into ADRS contents), so its trace is identical even when the PUBLIC
    // digest changes -- stronger than what the audit needs.
    v.push(Target {
        name: "fors_sign, PUBLIC md varied (informational)".into(),
        f: w_fors_sign,
        vary: vec![(OFF_DATA, 21)],
        fix: Box::new(clamp_adrs),
        expect_equal: true,
        what: "public digest md (SK.seed fixed)",
        trials: (1, 4),
        dudect_n: 0,
    });
    // ---- positive controls: must DIFFER
    v.push(Target {
        name: "CONTROL leaky_cmp (early-exit compare of secret)".into(),
        f: w_leaky_cmp,
        vary: sec16.clone(),
        fix: Box::new(|b| {
            for k in 0..16 {
                b[OFF_M16 + k] = 0;
            }
        }),
        expect_equal: false,
        what: "secret (leaky by construction)",
        trials: (1, 64),
        dudect_n: 100_000,
    });
    v.push(Target {
        name: "CONTROL leaky_table (secret-indexed lookup)".into(),
        f: w_leaky_table,
        vary: vec![(OFF_SEC, 1)],
        fix: Box::new(|_| {}),
        expect_equal: false,
        what: "secret index (leaky by construction)",
        trials: (1, 64),
        dudect_n: 0,
    });
    v.push(Target {
        name: "CONTROL leaky_loop (secret-dependent iteration count)".into(),
        f: w_leaky_loop,
        vary: vec![(OFF_SEC, 1)],
        fix: Box::new(|_| {}),
        expect_equal: false,
        what: "secret byte (leaky by construction)",
        trials: (1, 64),
        dudect_n: 100_000,
    });
    // ---- public-variation controls: varying a PUBLIC input must change the trace
    v.push(Target {
        name: "CONTROL wots_sign, PUBLIC m varied".into(),
        f: w_wots_sign,
        vary: vec![(OFF_M16, 16)],
        fix: Box::new(clamp_adrs),
        expect_equal: false,
        what: "public message m (chain lengths are public)",
        trials: (2, 16),
        dudect_n: 0,
    });
    v.push(Target {
        name: "CONTROL chain, PUBLIC s varied".into(),
        f: w_chain,
        vary: vec![(OFF_Z, 1)],
        fix: Box::new(|b| {
            b[OFF_CI] = 0;
            clamp_adrs(b)
        }),
        expect_equal: false,
        what: "public step count s",
        trials: (1, 32),
        dudect_n: 0,
    });
    v.push(Target {
        name: "CONTROL sha256, PUBLIC length varied".into(),
        f: w_sha256,
        vary: vec![(OFF_A, 1)],
        fix: Box::new(|b| set_u32(b, OFF_A, 0)),
        expect_equal: false,
        what: "public message length (0..255)",
        trials: (1, 32),
        dudect_n: 0,
    });
    v
}

// ------------------------------------------------------------------- PRNG

/// xoshiro256** seeded through splitmix64. Deterministic, so every experiment
/// is reproducible from its seed.
pub struct Rng([u64; 4]);
impl Rng {
    pub fn new(seed: u64) -> Rng {
        let mut s = seed;
        let mut st = [0u64; 4];
        for x in st.iter_mut() {
            s = s.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            *x = z ^ (z >> 31);
        }
        Rng(st)
    }
    pub fn next(&mut self) -> u64 {
        let s = &mut self.0;
        let r = s[1].wrapping_mul(5).rotate_left(7).wrapping_mul(9);
        let t = s[1] << 17;
        s[2] ^= s[0];
        s[3] ^= s[1];
        s[1] ^= s[2];
        s[0] ^= s[3];
        s[2] ^= t;
        s[3] = s[3].rotate_left(45);
        r
    }
    pub fn fill(&mut self, b: &mut [u8]) {
        for c in b.chunks_mut(8) {
            let r = self.next().to_le_bytes();
            c.copy_from_slice(&r[..c.len()]);
        }
    }
}

/// Input buffer for a target: public pseudo-random fill + `fix`.
pub fn public_input(t: &Target, seed: u64) -> Vec<u8> {
    let mut b = vec![0u8; IN_MAX];
    Rng::new(seed).fill(&mut b);
    (t.fix)(&mut b);
    b
}
/// Overwrite the varied ranges with fresh pseudo-random bytes.
pub fn vary_input(t: &Target, b: &mut [u8], rng: &mut Rng) {
    for &(o, l) in &t.vary {
        rng.fill(&mut b[o..o + l]);
    }
}
