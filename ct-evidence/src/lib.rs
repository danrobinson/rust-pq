//! Harness shared by the two evidence binaries (`cttrace`, `dudect`).
//!
//! Every function under test is wrapped in an `extern "C" fn(input, output)`
//! entry point with a flat byte layout, so that the emulator can call it with
//! two pointers and the timing harness can call it natively. The wrappers are
//! thin: they decode public parameters, call the `slhdsa` function, and copy
//! the result out.
//!
//! Input layout (not every wrapper uses every field):
//!
//! ```text
//!       0..4      a      u32 LE   (i / idx / length / number of blocks, public)
//!       4         z      u8       (tree height z, or HMAC key length, public)
//!       6..8      b      u16 LE   (context length, public)
//!       8..16     t      u64 LE   (idx_tree, public)
//!      16..32     PK.seed          (public)
//!      32..64     ADRS fields      (public)
//!      64..80     SK.seed / SK.prf / HMAC key   (SECRET)
//!      80..96     16-byte message m (public) or addrnd / opt_rand / SK.prf (SECRET)
//!      96..128    SHA-256 state after the block PK.seed ‖ 0^48, 8 x u32 LE
//!                 (public; always `seed_ctx(PK.seed).state`, see `finish_public`)
//!     128..192    private key SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root (whole signing)
//!     192..208    addrnd (whole signing, SECRET)
//!     256..1024   message M (whole signing) / digest md (FORS), public
//!    1024..1280   context string, public
//!    2048..10240  variable-length data: hash input, 64-byte blocks, signature bytes
//!   10240..11264  step ranges of `chain_blocks`: (start u32 LE, end u32 LE) per block, public
//! ```
//!
//! The tweakable-hash functions of the crate take a `&hash::Seed`, which the
//! crate always obtains from `hash::seed_ctx(&pk_seed)`. The wrappers rebuild
//! the same `Seed` from the PK.seed and the state stored in the input buffer
//! (both public), so that the one compression that computes it is not part of
//! every traced and timed call.

use slhdsa::address::Adrs;
use slhdsa::params::SHA2_128S as P;
/// The parameter set under test: SLH-DSA-SHA2-128s of the six-set crate (`slhdsa::sha2_128s`).
use slhdsa::sha2_128s as set;
type Seed = slhdsa::hash::Seed<16>;

pub type Entry = extern "C" fn(*const u8, *mut u8);

pub const IN_MAX: usize = 12288;
pub const OUT_MAX: usize = 16384;

pub const OFF_A: usize = 0;
pub const OFF_Z: usize = 4;
pub const OFF_B: usize = 6;
pub const OFF_T: usize = 8;
pub const OFF_PKSEED: usize = 16;
pub const OFF_ADRS: usize = 32;
pub const OFF_SEC: usize = 64;
pub const OFF_M16: usize = 80;
pub const OFF_STATE: usize = 96;
pub const OFF_SK: usize = 128; // 64-byte sk: seed | prf | pk_seed | pk_root
pub const OFF_ADDRND: usize = 192;
pub const OFF_MSG: usize = 256;
pub const OFF_CTX: usize = 1024;
pub const OFF_DATA: usize = 2048;
pub const OFF_RANGES: usize = 10240;

/// Most blocks a `chain_blocks` wrapper call takes (the crate's largest batch).
pub const MAX_BLOCKS: usize = 128;

/// Output: signature bytes at 0.., and at this offset 1 if the signer
/// returned a signature and 2 if it returned `None`.
pub const OFF_OUT_FLAG: usize = 8000;

/// Whether the crate under test was built with its `hw-sha2` feature.
pub const HW_SHA2: bool = cfg!(feature = "hw-sha2");
pub fn variant() -> &'static str {
    if HW_SHA2 {
        "hw-sha2"
    } else {
        "default"
    }
}
/// With the `hw-sha2` build: whether the crate reports that it runs on the
/// SHA-256 instructions (it does on every `aarch64-apple-darwin` CPU).
pub fn hw_active() -> bool {
    #[cfg(feature = "hw-sha2")]
    {
        slhdsa::sha256::hw_active()
    }
    #[cfg(not(feature = "hw-sha2"))]
    {
        false
    }
}

#[inline(always)]
unsafe fn inp<'a>(p: *const u8) -> &'a [u8] {
    core::slice::from_raw_parts(p, IN_MAX)
}
#[inline(always)]
unsafe fn outp<'a>(p: *mut u8) -> &'a mut [u8] {
    core::slice::from_raw_parts_mut(p, OUT_MAX)
}
pub fn u32at(b: &[u8], o: usize) -> u32 {
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
fn words8(b: &[u8], o: usize) -> [u32; 8] {
    let mut s = [0u32; 8];
    let mut k = 0;
    while k < 8 {
        s[k] = u32at(b, o + 4 * k);
        k += 1;
    }
    s
}
/// The `Seed` of the PK.seed in the buffer, from the stored state.
fn seed(b: &[u8]) -> Seed {
    Seed { pk_seed: a16(b, OFF_PKSEED), state: words8(b, OFF_STATE), state512: [0u64; 8] }
}

// ---------------------------------------------------------------- wrappers

#[inline(never)]
pub extern "C" fn w_sha256(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::sha256::sha256(&b[OFF_DATA..OFF_DATA + len]);
    out[..32].copy_from_slice(&d);
}

/// key = in[64..64+klen] (klen = z field), msg = data[0..a]
#[inline(never)]
pub extern "C" fn w_hmac(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let mlen = u32at(b, OFF_A) as usize;
    let klen = b[OFF_Z] as usize;
    let d = slhdsa::sha256::hmac_sha256(&b[OFF_SEC..OFF_SEC + klen], &b[OFF_DATA..OFF_DATA + mlen]);
    out[..32].copy_from_slice(&d);
}

/// The compression function: state = data[0..32] (8 x u32 LE), block = data[32..96].
/// `compress` is `#[inline]` in the crate, so the code traced here is the copy
/// rustc inlines into this wrapper; the copies inlined into the crate's own
/// functions are what every other row exercises.
#[inline(never)]
pub extern "C" fn w_compress(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let st = words8(b, OFF_DATA);
    let r = slhdsa::sha256::compress(&st, &b[OFF_DATA + 32..OFF_DATA + 96], 0);
    let mut k = 0;
    while k < 8 {
        out[4 * k..4 * k + 4].copy_from_slice(&r[k].to_le_bytes());
        k += 1;
    }
}

/// `thash(seed, adrs, data[0..a])`
#[inline(never)]
pub extern "C" fn w_thash(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::hash::thash::<16>(&seed(b), &adrs(b), &b[OFF_DATA..OFF_DATA + len]);
    out[..16].copy_from_slice(&d);
}

/// `thash_short(seed, adrs, data[0..a])`, a <= 33: F and PRF (a = 16), H (a = 32)
#[inline(never)]
pub extern "C" fn w_thash_short(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::hash::thash_short::<16>(&seed(b), &adrs(b), &b[OFF_DATA..OFF_DATA + len]);
    out[..16].copy_from_slice(&d);
}

/// `thash_values(seed, adrs, blocks)`: T_len over the values held in the 35
/// blocks data[0..35*64].
#[inline(never)]
pub extern "C" fn w_thash_values(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    // [[u8; 64]; 35] has alignment 1 and the buffer is long enough.
    let blocks: &[[u8; 64]; 35] = unsafe { &*(b[OFF_DATA..OFF_DATA + 35 * 64].as_ptr() as *const [[u8; 64]; 35]) };
    let d = slhdsa::hash::thash_values::<16>(&seed(b), &adrs(b), blocks);
    out[..16].copy_from_slice(&d);
}

/// sk_prf = in[64..80] (secret), opt_rand = in[80..96] (secret: addrnd), m = data[0..a] (public)
#[inline(never)]
pub extern "C" fn w_prf_msg(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let len = u32at(b, OFF_A) as usize;
    let d = slhdsa::hash::prf_msg::<16>(&a16(b, OFF_SEC), &a16(b, OFF_M16), &b[OFF_DATA..OFF_DATA + len]);
    out[..16].copy_from_slice(&d);
}

/// The n = a blocks data[64k..64k+64] are copied to the output buffer and
/// iterated there in place.
#[inline(always)]
fn chain_blocks_with<F: Fn(&[u32; 8], &mut [[u8; 64]], &[u32], &[u32])>(i: *const u8, o: *mut u8, f: F) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let n = (u32at(b, OFF_A) as usize).min(MAX_BLOCKS);
    let mut start = [0u32; MAX_BLOCKS];
    let mut end = [0u32; MAX_BLOCKS];
    let mut k = 0;
    while k < n {
        start[k] = u32at(b, OFF_RANGES + 8 * k);
        end[k] = u32at(b, OFF_RANGES + 8 * k + 4);
        k += 1;
    }
    out[..64 * n].copy_from_slice(&b[OFF_DATA..OFF_DATA + 64 * n]);
    // [u8; 64] has alignment 1; `out` holds OUT_MAX >= 64 * MAX_BLOCKS bytes.
    let blocks: &mut [[u8; 64]] = unsafe { core::slice::from_raw_parts_mut(o as *mut [u8; 64], n) };
    f(&words8(b, OFF_STATE), blocks, &start, &end);
}

/// `chain_blocks(state, blocks, start, end)` with the seed state.
#[inline(never)]
pub extern "C" fn w_chain_blocks(i: *const u8, o: *mut u8) {
    chain_blocks_with(i, o, slhdsa::hash::chain_blocks::<16>)
}

/// `chain_blocks_portable`: in the default build the same code as
/// `chain_blocks`; in the `hw-sha2` build the fallback loop (not reached on
/// this CPU from the crate), whose compression is the single-block hardware one.
#[inline(never)]
pub extern "C" fn w_chain_blocks_portable(i: *const u8, o: *mut u8) {
    chain_blocks_with(i, o, slhdsa::hash::chain_blocks_portable::<16>)
}

#[inline(never)]
pub extern "C" fn w_wots_pk_gen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::wots::wots_pk_gen::<16>(&a16(b, OFF_SEC), &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_wots_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let s = slhdsa::wots::wots_sign::<16>(&a16(b, OFF_M16), &a16(b, OFF_SEC), &seed(b), adrs(b));
    out[..s.len()].copy_from_slice(&s);
}

/// sig = data[0..560], m = in[80..96]
#[inline(never)]
pub extern "C" fn w_wots_pk_from_sig(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::wots::wots_pk_from_sig::<16>(&b[OFF_DATA..OFF_DATA + 560], &a16(b, OFF_M16), &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_xmss_node(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::xmss::xmss_node::<16>(&a16(b, OFF_SEC), u32at(b, OFF_A), b[OFF_Z] as u32, &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_xmss_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let s = slhdsa::xmss::xmss_sign::<16>(&P, &a16(b, OFF_M16), &a16(b, OFF_SEC), u32at(b, OFF_A), &seed(b), adrs(b));
    out[..s.len()].copy_from_slice(&s);
}

/// idx = a, sig = data[0..704], m = in[80..96]
#[inline(never)]
pub extern "C" fn w_xmss_pk_from_sig(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::xmss::xmss_pk_from_sig::<16>(&P, u32at(b, OFF_A), &b[OFF_DATA..OFF_DATA + 704], &a16(b, OFF_M16), &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_fors_sk_gen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::fors::fors_sk_gen::<16>(&a16(b, OFF_SEC), &seed(b), adrs(b), u32at(b, OFF_A));
    out[..16].copy_from_slice(&d);
}

#[inline(never)]
pub extern "C" fn w_fors_node(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::fors::fors_node::<16>(&a16(b, OFF_SEC), u32at(b, OFF_A), b[OFF_Z] as u32, &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

/// md = in[256..277] (public)
#[inline(never)]
pub extern "C" fn w_fors_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let s = slhdsa::fors::fors_sign::<16>(&P, &b[OFF_MSG..OFF_MSG + 21], &a16(b, OFF_SEC), &seed(b), adrs(b));
    out[..s.len()].copy_from_slice(&s);
}

#[inline(never)]
pub extern "C" fn w_fors_pk_gen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::fors::fors_pk_gen::<16>(&P, &a16(b, OFF_SEC), &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

/// sig = data[0..2912], md = in[256..277]
#[inline(never)]
pub extern "C" fn w_fors_pk_from_sig(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let d = slhdsa::fors::fors_pk_from_sig::<16>(&P, &b[OFF_DATA..OFF_DATA + 2912], &b[OFF_MSG..OFF_MSG + 21], &seed(b), adrs(b));
    out[..16].copy_from_slice(&d);
}

/// sk_seed = in[64..80], sk_prf = in[80..96], pk_seed = in[16..32]
#[inline(never)]
pub extern "C" fn w_keygen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (sk, pk) = set::slh_keygen_internal(&a16(b, OFF_SEC), &a16(b, OFF_M16), &a16(b, OFF_PKSEED));
    out[..64].copy_from_slice(&sk);
    out[64..96].copy_from_slice(&pk);
}

/// `api::keygen` with seeds = in[64..80] ‖ in[80..96] ‖ in[16..32]
#[inline(never)]
pub extern "C" fn w_api_keygen(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let mut seeds = [0u8; 48];
    seeds[0..32].copy_from_slice(&b[OFF_SEC..OFF_SEC + 32]);
    seeds[32..48].copy_from_slice(&b[OFF_PKSEED..OFF_PKSEED + 16]);
    let mut sk = [0u8; 64];
    let mut pk = [0u8; 32];
    set::keygen(&seeds, &mut sk, &mut pk);
    out[..64].copy_from_slice(&sk);
    out[64..96].copy_from_slice(&pk);
}

// Whole signing: m = in[256..256+a] (public), ctx = in[1024..1024+b] (public),
// sk = in[128..192], addrnd = in[192..208].

#[inline(always)]
fn sign_args<'a>(b: &'a [u8]) -> (&'a [u8], &'a [u8], [u8; 64], [u8; 16]) {
    let len = u32at(b, OFF_A) as usize;
    let clen = u16::from_le_bytes([b[OFF_B], b[OFF_B + 1]]) as usize;
    let mut sk = [0u8; 64];
    sk.copy_from_slice(&b[OFF_SK..OFF_SK + 64]);
    (&b[OFF_MSG..OFF_MSG + len], &b[OFF_CTX..OFF_CTX + clen], sk, a16(b, OFF_ADDRND))
}
#[inline(always)]
fn put_sig(out: &mut [u8], s: Option<Vec<u8>>) {
    match s {
        Some(s) => {
            out[..s.len()].copy_from_slice(&s);
            out[OFF_OUT_FLAG] = 1;
        }
        None => out[OFF_OUT_FLAG] = 2,
    }
}

#[inline(never)]
pub extern "C" fn w_sign_internal(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, _, sk, addrnd) = sign_args(b);
    put_sig(out, Some(set::slh_sign_internal(m, &sk, &addrnd)));
}
#[inline(never)]
pub extern "C" fn w_sign_internal_checked(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, _, sk, addrnd) = sign_args(b);
    put_sig(out, set::slh_sign_internal_checked(m, &sk, &addrnd));
}
#[inline(never)]
pub extern "C" fn w_slh_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, ctx, sk, addrnd) = sign_args(b);
    put_sig(out, set::slh_sign(m, ctx, &sk, &addrnd));
}
#[inline(never)]
pub extern "C" fn w_slh_sign_checked(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, ctx, sk, addrnd) = sign_args(b);
    put_sig(out, set::slh_sign_checked(m, ctx, &sk, &addrnd));
}
#[inline(never)]
pub extern "C" fn w_api_sign(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, ctx, sk, addrnd) = sign_args(b);
    put_sig(out, set::sign(m, ctx, &sk, &addrnd));
}
#[inline(never)]
pub extern "C" fn w_api_sign_checked(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, ctx, sk, addrnd) = sign_args(b);
    put_sig(out, set::sign_checked(m, ctx, &sk, &addrnd));
}
#[inline(never)]
pub extern "C" fn w_api_sign_deterministic(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, ctx, sk, _) = sign_args(b);
    put_sig(out, set::sign_deterministic(m, ctx, &sk));
}
#[inline(never)]
pub extern "C" fn w_api_sign_deterministic_checked(i: *const u8, o: *mut u8) {
    let (b, out) = unsafe { (inp(i), outp(o)) };
    let (m, ctx, sk, _) = sign_args(b);
    put_sig(out, set::sign_deterministic_checked(m, ctx, &sk));
}

/// A whole-signing entry point of the crate.
pub struct SignEntry {
    /// name on the command line
    pub key: &'static str,
    /// the crate function
    pub name: &'static str,
    pub f: Entry,
    /// the checked signer: every signed value computed twice
    pub checked: bool,
    /// takes a context string (M' = 0 ‖ |ctx| ‖ ctx ‖ M)
    pub ctx: bool,
    /// addrnd = PK.seed
    pub deterministic: bool,
}
pub fn sign_entries() -> Vec<SignEntry> {
    let e = |key, name, f, checked, ctx, deterministic| SignEntry { key, name, f, checked, ctx, deterministic };
    vec![
        e("internal", "slh::slh_sign_internal", w_sign_internal as Entry, false, false, false),
        e("internal-checked", "slh::slh_sign_internal_checked", w_sign_internal_checked as Entry, true, false, false),
        e("slh", "slh::slh_sign", w_slh_sign as Entry, false, true, false),
        e("slh-checked", "slh::slh_sign_checked", w_slh_sign_checked as Entry, true, true, false),
        e("api", "api::sign", w_api_sign as Entry, false, true, false),
        e("api-checked", "api::sign_checked", w_api_sign_checked as Entry, true, true, false),
        e("api-det", "api::sign_deterministic", w_api_sign_deterministic as Entry, false, true, true),
        e("api-det-checked", "api::sign_deterministic_checked", w_api_sign_deterministic_checked as Entry, true, true, true),
    ]
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

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expect {
    /// The varied bytes are secret (or are values the signer is about to
    /// publish): the trace must not depend on them.
    Equal,
    /// Control: the trace must change.
    Differ,
    /// A public input is varied and either outcome is consistent with the
    /// claim under test; the outcome is reported, not judged.
    Info,
}

pub struct Target {
    pub name: String,
    pub f: Entry,
    /// Byte ranges (start, len) of the input that are varied between runs.
    pub vary: Vec<(usize, usize)>,
    /// Sets the public parameters after the buffer was filled with public
    /// pseudo-random bytes.
    pub fix: Box<dyn Fn(&mut [u8]) + Send + Sync>,
    pub expect: Expect,
    /// What `vary` is, for the report.
    pub what: &'static str,
    /// Trace experiment size: (public configurations, secrets per configuration).
    pub trials: (usize, usize),
    /// Samples per class for the timing harness (0: not timed).
    pub dudect_n: usize,
    /// Applied after the varied bytes were redrawn (or zeroed): reduces them
    /// to the values the row is about.
    pub post: Option<fn(&mut [u8])>,
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

/// Public step ranges of a `chain_blocks` row.
#[derive(Clone, Copy)]
pub enum Ranges {
    /// every block start..end
    Fixed(u32, u32),
    /// block i: 0..d_i with a pseudo-random digit d_i < 16 (as `wots_sign`)
    UpTo,
    /// block i: d_i..15 (as `wots_pk_from_sig`)
    From,
    /// block i: t_i..t_i+1 with a pseudo-random 20-bit t_i (as the FORS levels)
    Unit,
    /// block i: s_i..e_i with pseudo-random 0 <= s_i <= e_i <= 15, about
    /// four in ten of them empty
    Random,
}
/// The first 16 bytes of the blocks of a `chain_blocks` row (in the crate an
/// address prefix: layer, tree, type, key pair, upper half of word 2).
#[derive(Clone, Copy)]
pub enum Heads {
    /// all blocks the same prefix (as in every call the crate makes)
    Same,
    /// pseudo-random, all different
    Distinct,
    /// each block one of two prefixes, pseudo-randomly
    Mixed,
}
fn chain_fix(n: usize, r: Ranges, h: Heads) -> impl Fn(&mut [u8]) + Send + Sync {
    move |b: &mut [u8]| {
        set_u32(b, OFF_A, n as u32);
        let two = [a16(b, OFF_DATA), a16(b, OFF_DATA + 64)];
        for k in 0..n {
            let r0 = u32at(b, OFF_RANGES + 8 * k);
            let r1 = u32at(b, OFF_RANGES + 8 * k + 4);
            let (s, e) = match r {
                Ranges::Fixed(s, e) => (s, e),
                Ranges::UpTo => (0, r0 % 16),
                Ranges::From => (r0 % 16, 15),
                Ranges::Unit => (r0 & 0xfffff, (r0 & 0xfffff) + 1),
                Ranges::Random => {
                    let s = r0 % 16;
                    (s, if r1 % 4 == 0 { s } else { s + (r1 >> 8) % (16 - s) })
                }
            };
            set_u32(b, OFF_RANGES + 8 * k, s);
            set_u32(b, OFF_RANGES + 8 * k + 4, e);
            let head = match h {
                Heads::Same => Some(two[0]),
                Heads::Distinct => None,
                Heads::Mixed => Some(two[if k < 2 { k } else { (r1 >> 31) as usize }]),
            };
            if let Some(head) = head {
                b[OFF_DATA + 64 * k..OFF_DATA + 64 * k + 16].copy_from_slice(&head);
            }
        }
    }
}
/// Bytes 16..64 of each of the first n blocks: everything but the prefix.
fn chain_vary(n: usize) -> Vec<(usize, usize)> {
    (0..n).map(|k| (OFF_DATA + 64 * k + 16, 48)).collect()
}

fn tgt(name: impl Into<String>, f: Entry, vary: Vec<(usize, usize)>, what: &'static str, trials: (usize, usize), dudect_n: usize, fix: impl Fn(&mut [u8]) + Send + Sync + 'static) -> Target {
    Target { name: name.into(), f, vary, fix: Box::new(fix), expect: Expect::Equal, what, trials, dudect_n, post: None }
}
fn with(mut t: Target, e: Expect) -> Target {
    t.expect = e;
    t
}

pub fn targets() -> Vec<Target> {
    let mut v: Vec<Target> = Vec::new();
    let sec16 = vec![(OFF_SEC, 16)];

    // ---- SHA-256 layer
    for &len in &[1usize, 16, 55, 56, 64, 119, 120, 256, 560] {
        v.push(tgt(format!("sha256/len={len}"), w_sha256, vec![(OFF_DATA, len)], "all message bytes", (1, 64), 200_000, move |b| set_u32(b, OFF_A, len as u32)));
    }
    for &(klen, mlen) in &[(16usize, 32usize), (16, 150), (64, 64), (32, 1)] {
        v.push(tgt(format!("hmac_sha256/klen={klen},mlen={mlen}"), w_hmac, vec![(OFF_SEC, klen), (OFF_DATA, mlen)], "key and message bytes", (1, 64), 100_000, move |b| {
            set_u32(b, OFF_A, mlen as u32);
            b[OFF_Z] = klen as u8;
        }));
    }
    v.push(tgt("compress (copy inlined into the wrapper)", w_compress, vec![(OFF_DATA, 96)], "state and block", (1, 64), 200_000, |_| {}));

    // ---- tweakable hashes
    for &len in &[16usize, 32] {
        v.push(tgt(format!("thash_short/len={len}"), w_thash_short, vec![(OFF_DATA, len)], "m (SK.seed / chain value / node values)", (4, 16), 200_000, move |b| {
            set_u32(b, OFF_A, len as u32);
            clamp_adrs(b)
        }));
    }
    for &len in &[16usize, 32, 224, 560] {
        v.push(tgt(format!("thash/len={len}"), w_thash, vec![(OFF_DATA, len)], "m (len=224: the 14 FORS roots)", (4, 16), 200_000, move |b| {
            set_u32(b, OFF_A, len as u32);
            clamp_adrs(b)
        }));
    }
    v.push(tgt("thash_values", w_thash_values, vec![(OFF_DATA, 35 * 64)], "all 35 blocks (the values are the WOTS+ chain ends)", (4, 16), 100_000, clamp_adrs));
    for &len in &[0usize, 32, 100, 1000] {
        v.push(tgt(format!("prf_msg/mlen={len}"), w_prf_msg, vec![(OFF_SEC, 16), (OFF_M16, 16)], "SK.prf and opt_rand(addrnd)", (4, 16), 100_000, move |b| set_u32(b, OFF_A, len as u32)));
    }

    // ---- chain_blocks: block contents secret, step ranges and prefixes public
    let what_cb = "bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed)";
    let shapes: [(&str, usize, Ranges, Heads, (usize, usize), usize); 13] = [
        ("n=1,steps=0..15", 1, Ranges::Fixed(0, 15), Heads::Same, (2, 16), 100_000),
        ("n=1,steps=3..10", 1, Ranges::Fixed(3, 10), Heads::Same, (2, 16), 0),
        ("n=1,steps=5..5 (none)", 1, Ranges::Fixed(5, 5), Heads::Same, (2, 16), 0),
        ("n=3,steps=0..15", 3, Ranges::Fixed(0, 15), Heads::Same, (2, 16), 0),
        ("n=4,steps=0..15", 4, Ranges::Fixed(0, 15), Heads::Same, (2, 16), 50_000),
        ("n=35,steps=0..15 (wots_pk_gen)", 35, Ranges::Fixed(0, 15), Heads::Same, (2, 16), 20_000),
        ("n=35,steps=0..d_i (wots_sign)", 35, Ranges::UpTo, Heads::Same, (8, 8), 20_000),
        ("n=35,steps=d_i..15 (wots_pk_from_sig)", 35, Ranges::From, Heads::Same, (8, 8), 0),
        ("n=14,steps=t_i..t_i+1 (FORS paths)", 14, Ranges::Unit, Heads::Same, (4, 16), 50_000),
        ("n=128,steps=t_i..t_i+1 (FORS batch)", 128, Ranges::Unit, Heads::Same, (2, 16), 10_000),
        ("n=7,random ranges,two prefixes", 7, Ranges::Random, Heads::Mixed, (16, 8), 0),
        ("n=64,random ranges,two prefixes", 64, Ranges::Random, Heads::Mixed, (8, 8), 0),
        ("n=35,random ranges,distinct prefixes", 35, Ranges::Random, Heads::Distinct, (8, 8), 0),
    ];
    for (name, n, r, h, trials, dn) in shapes {
        v.push(tgt(format!("chain_blocks/{name}"), w_chain_blocks, chain_vary(n), what_cb, trials, dn, chain_fix(n, r, h)));
    }
    for (name, n, r, h, trials) in [("n=4,steps=0..15", 4, Ranges::Fixed(0, 15), Heads::Same, (2, 16)), ("n=35,random ranges,two prefixes", 35, Ranges::Random, Heads::Mixed, (4, 8))] {
        v.push(tgt(format!("chain_blocks_portable/{name}"), w_chain_blocks_portable, chain_vary(n), what_cb, trials, 0, chain_fix(n, r, h)));
    }

    // ---- WOTS+, XMSS, FORS, key generation
    v.push(tgt("wots_pk_gen", w_wots_pk_gen, sec16.clone(), "SK.seed", (4, 16), 50_000, clamp_adrs));
    v.push(tgt("wots_sign", w_wots_sign, sec16.clone(), "SK.seed (message m public, fixed)", (8, 8), 50_000, clamp_adrs));
    for &z in &[0u8, 1, 2, 3, 4] {
        v.push(tgt(format!("xmss_node/z={z}"), w_xmss_node, sec16.clone(), "SK.seed", if z <= 2 { (4, 16) } else { (2, 16) }, if z <= 1 { 10_000 } else { 3_000 }, move |b| {
            b[OFF_Z] = z;
            let i = u32at(b, OFF_A) & ((1u32 << (9 - z)) - 1);
            set_u32(b, OFF_A, i);
            clamp_adrs(b)
        }));
    }
    v.push(tgt("xmss_sign", w_xmss_sign, sec16.clone(), "SK.seed (m, idx public, fixed)", (2, 8), 500, |b| {
        let i = u32at(b, OFF_A) & 511;
        set_u32(b, OFF_A, i);
        clamp_adrs(b)
    }));
    v.push(tgt("fors_sk_gen", w_fors_sk_gen, sec16.clone(), "SK.seed", (4, 16), 200_000, clamp_adrs));
    for &z in &[0u8, 1, 3, 6, 7, 8, 12] {
        v.push(tgt(
            format!("fors_node/z={z}"),
            w_fors_node,
            sec16.clone(),
            "SK.seed",
            if z <= 7 { (4, 16) } else { (2, 8) },
            match z {
                0 | 1 => 100_000,
                3 => 30_000,
                6 | 7 | 8 => 5_000,
                _ => 2_000,
            },
            move |b| {
                b[OFF_Z] = z;
                let i = u32at(b, OFF_A) % (14u32 << (12 - z));
                set_u32(b, OFF_A, i);
                clamp_adrs(b)
            },
        ));
    }
    v.push(tgt("fors_sign", w_fors_sign, sec16.clone(), "SK.seed (md public, fixed)", (2, 8), 300, clamp_adrs));
    v.push(tgt("fors_pk_gen", w_fors_pk_gen, sec16.clone(), "SK.seed", (2, 8), 300, clamp_adrs));
    v.push(tgt("slh_keygen_internal", w_keygen, vec![(OFF_SEC, 32)], "SK.seed and SK.prf (PK.seed fixed)", (2, 12), 1000, |_| {}));
    v.push(tgt("slh_keygen_internal/all-inputs", w_keygen, vec![(OFF_SEC, 32), (OFF_PKSEED, 16)], "SK.seed, SK.prf and PK.seed", (1, 12), 0, |_| {}));
    v.push(tgt("api::keygen", w_api_keygen, vec![(OFF_SEC, 32)], "SK.seed and SK.prf (PK.seed fixed)", (2, 8), 0, |_| {}));

    // ---- the recomputation a verifier does, which the signer runs on its own
    // signature before publishing it: the trace must not depend on the
    // signature bytes (the pinned whole-signature experiment relies on this)
    v.push(tgt("wots_pk_from_sig", w_wots_pk_from_sig, vec![(OFF_DATA, 560)], "WOTS+ signature bytes (m public, fixed)", (4, 8), 0, clamp_adrs));
    v.push(tgt("xmss_pk_from_sig", w_xmss_pk_from_sig, vec![(OFF_DATA, 704)], "XMSS signature bytes (m, idx public, fixed)", (4, 8), 0, |b| {
        let i = u32at(b, OFF_A) & 511;
        set_u32(b, OFF_A, i);
        clamp_adrs(b)
    }));
    v.push(tgt("fors_pk_from_sig", w_fors_pk_from_sig, vec![(OFF_DATA, 2912)], "FORS signature bytes (md public, fixed)", (4, 8), 0, clamp_adrs));

    // ---- a public input varied; reported, not judged
    v.push(with(tgt("INFO fors_sign, PUBLIC md varied", w_fors_sign, vec![(OFF_MSG, 21)], "public digest md (SK.seed fixed)", (1, 8), 0, clamp_adrs), Expect::Info));

    // ---- positive controls: must DIFFER
    v.push(with(
        tgt("CONTROL leaky_cmp (early-exit compare of secret)", w_leaky_cmp, sec16.clone(), "secret (leaky by construction)", (1, 64), 100_000, |b| {
            for k in 0..16 {
                b[OFF_M16 + k] = 0;
            }
        }),
        Expect::Differ,
    ));
    v.push(with(tgt("CONTROL leaky_table (secret-indexed lookup)", w_leaky_table, vec![(OFF_SEC, 1)], "secret index (leaky by construction)", (1, 64), 0, |_| {}), Expect::Differ));
    v.push(with(tgt("CONTROL leaky_loop (secret-dependent iteration count)", w_leaky_loop, vec![(OFF_SEC, 1)], "secret byte (leaky by construction)", (1, 64), 100_000, |_| {}), Expect::Differ));
    // ---- public-variation controls: varying a PUBLIC input must change the trace
    v.push(with(tgt("CONTROL wots_sign, PUBLIC m varied", w_wots_sign, vec![(OFF_M16, 16)], "public message m (chain lengths are public)", (2, 16), 0, clamp_adrs), Expect::Differ));
    v.push(with(
        tgt("CONTROL chain_blocks n=4, PUBLIC end of block 0 varied", w_chain_blocks, vec![(OFF_RANGES + 4, 1)], "public step count of one block (0..255)", (1, 32), 0, chain_fix(4, Ranges::Fixed(0, 8), Heads::Same)),
        Expect::Differ,
    ));
    v.push(with(tgt("CONTROL sha256, PUBLIC length varied", w_sha256, vec![(OFF_A, 1)], "public message length (0..255)", (1, 32), 0, |b| set_u32(b, OFF_A, 0)), Expect::Differ));
    // ---- the hw-sha2 backend of `chain_blocks` keeps the first four rounds of
    // the last block it entered and reuses them when the next block starts
    // with the same 16 bytes (an address prefix, public). Here the first byte
    // of block 2 is the common prefix's, or that with one bit flipped. With the
    // hw-sha2 build the trace must show it (a control: the tracer sees the
    // reuse); the default build has no such code and the row is informational.
    let mut t = tgt(
        "PREFIX chain_blocks n=8, PUBLIC: whether block 2 shares the others' 16-byte prefix",
        w_chain_blocks,
        vec![(OFF_DATA + 2 * 64, 1)],
        "one public bit: block 2 starts like the other blocks, or not",
        (1, 16),
        0,
        chain_fix(8, Ranges::Fixed(0, 4), Heads::Same),
    );
    t.post = Some(|b| b[OFF_DATA + 2 * 64] = b[OFF_DATA] ^ (b[OFF_DATA + 2 * 64] & 1));
    v.push(with(t, if HW_SHA2 { Expect::Differ } else { Expect::Info }));
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

/// Store `seed_ctx(PK.seed).state` for the PK.seed currently in the buffer.
pub fn finish_public(b: &mut [u8]) {
    let s = slhdsa::hash::seed_ctx::<16>(&a16(b, OFF_PKSEED));
    for k in 0..8 {
        set_u32(b, OFF_STATE + 4 * k, s.state[k]);
    }
}
/// Input buffer for a target: public pseudo-random fill + `fix`.
pub fn public_input(t: &Target, seed: u64) -> Vec<u8> {
    let mut b = vec![0u8; IN_MAX];
    Rng::new(seed).fill(&mut b);
    (t.fix)(&mut b);
    finish_public(&mut b);
    b
}
/// Overwrite the varied ranges with fresh pseudo-random bytes.
pub fn vary_input(t: &Target, b: &mut [u8], rng: &mut Rng) {
    for &(o, l) in &t.vary {
        rng.fill(&mut b[o..o + l]);
    }
    if let Some(post) = t.post {
        post(b);
    }
    finish_public(b);
}
/// Overwrite the varied ranges with zeros.
pub fn zero_input(t: &Target, b: &mut [u8]) {
    for &(o, l) in &t.vary {
        for x in &mut b[o..o + l] {
            *x = 0;
        }
    }
    if let Some(post) = t.post {
        post(b);
    }
    finish_public(b);
}
