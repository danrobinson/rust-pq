//! Armv8 SHA-256 WOTS+ keygen, signing, and sorted dynamic lane-refill recovery.
use super::*;
use crate::sha256::arm_wide;

/// Compute the `len = 2*N + 3` base-16 WOTS+ digits + checksum on the stack
/// without heap allocation.
#[inline]
pub(super) fn wots_digits_stack<const N: usize>(m: &[u8; N]) -> [u32; LEN_MAX] {
    let mut digits = [0u32; LEN_MAX];
    let mut csum: u32 = 0;
    let mut i = 0;
    while i < N {
        let byte = m[i];
        let hi = (byte >> 4) as u32;
        let lo = (byte & 0x0f) as u32;
        digits[2 * i] = hi;
        digits[2 * i + 1] = lo;
        csum += 30 - hi - lo;
        i += 1;
    }
    let len1 = 2 * N;
    digits[len1] = (csum >> 8) & 0x0f;
    digits[len1 + 1] = (csum >> 4) & 0x0f;
    digits[len1 + 2] = csum & 0x0f;
    digits
}

#[inline]
fn compress_tlen_1<const N: usize>(seed: &Seed<N>, adrs: Adrs, buf: &mut [u8], len: usize) -> [u8; N] {
    let pk_adrs = adrs.with_type(WOTS_PK).with_keypair(adrs.keypair);
    let size = 22 + len * N;
    buf[..22].copy_from_slice(&pk_adrs.compress());
    buf[size] = 0x80;
    if N == 16 {
        let total = 640;
        buf[total - 2..total].copy_from_slice(&(((64 + size) * 8) as u16).to_be_bytes());
        let d = arm_wide::compress_multi_1(&seed.state, &buf[..total]);
        let mut out = [0u8; N];
        out.copy_from_slice(&d);
        out
    } else {
        let total = if N == 24 { 1280 } else { 2304 };
        buf[total - 2..total].copy_from_slice(&(((128 + size) * 8) as u16).to_be_bytes());
        if let Some(out) = crate::sha512::paired::compress_multi_1::<N>(&seed.state512, &buf[..total]) {
            return out;
        }
        let mut st = seed.state512;
        let mut off = 0;
        while off < total {
            st = crate::sha512::compress(&st, buf, off);
            off += 128;
        }
        crate::hash::trunc512::<N>(&st)
    }
}

/// Fused Armv8 `wots_pkGen` for a single key (height 0).
pub(super) fn pk_gen<const N: usize>(sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let len = 2 * N + LEN2;
    if N == 16 {
        let mut buf = [0u8; 640];
        arm_wide::wots_endpoints_1::<N>(&seed.state, sk_seed, adrs, &mut buf);
        compress_tlen_1::<N>(seed, adrs, &mut buf, len)
    } else if N == 24 {
        let mut buf = [0u8; 1280];
        arm_wide::wots_endpoints_1::<N>(&seed.state, sk_seed, adrs, &mut buf);
        compress_tlen_1::<N>(seed, adrs, &mut buf, len)
    } else {
        let mut buf = [0u8; 2304];
        arm_wide::wots_endpoints_1::<N>(&seed.state, sk_seed, adrs, &mut buf);
        compress_tlen_1::<N>(seed, adrs, &mut buf, len)
    }
}

/// Fused + sorted dynamic lane-refill Armv8 `wots_sign`.
pub(super) fn sign<const N: usize>(m: &[u8; N], sk_seed: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> Vec<u8> {
    let len = 2 * N + LEN2;
    let digits = wots_digits_stack::<N>(m);
    let mut sig = alloc::vec![0u8; len * N];
    arm_wide::wots_sign_fused::<N>(&seed.state, sk_seed, adrs, &digits[..len], &mut sig);
    sig
}

/// Sorted dynamic lane-refill Armv8 `wots_pkFromSig`.
pub(super) fn recover<const N: usize>(sig: &[u8], m: &[u8; N], seed: &Seed<N>, adrs: Adrs) -> [u8; N] {
    let len = 2 * N + LEN2;
    let digits = wots_digits_stack::<N>(m);
    if N == 16 {
        let mut buf = [0u8; 640];
        arm_wide::wots_recover::<N>(&seed.state, adrs, sig, &digits[..len], &mut buf);
        compress_tlen_1::<N>(seed, adrs, &mut buf, len)
    } else if N == 24 {
        let mut buf = [0u8; 1280];
        arm_wide::wots_recover::<N>(&seed.state, adrs, sig, &digits[..len], &mut buf);
        compress_tlen_1::<N>(seed, adrs, &mut buf, len)
    } else {
        let mut buf = [0u8; 2304];
        arm_wide::wots_recover::<N>(&seed.state, adrs, sig, &digits[..len], &mut buf);
        compress_tlen_1::<N>(seed, adrs, &mut buf, len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hash::{chain_blocks_portable, seed_ctx};

    fn check_digits<const N: usize>() {
        for v in 0..32u8 {
            let m: [u8; N] = core::array::from_fn(|i| v.wrapping_mul(37).wrapping_add((i * 13) as u8));
            let expected = wots_digits::<N>(&m);
            let actual = wots_digits_stack::<N>(&m);
            assert_eq!(&actual[..expected.len()], expected.as_slice());
        }
    }

    fn check_recover<const N: usize>() {
        if !arm_wide::available() {
            return;
        }
        let seed = seed_ctx(&[0x6a; N]);
        let adrs = Adrs::new()
            .with_tree(0x0102030405060708)
            .with_keypair(0x11224455);
        let signature: [u8; 32 * LEN_MAX] = core::array::from_fn(|i| (i * 13 + i / 11) as u8);
        let len = 2 * N + LEN2;
        for variant in 0..20 {
            let digits: [u32; LEN_MAX] = core::array::from_fn(|i| match variant {
                0 => 0,
                1 => 15,
                2 if i < 16 => 15,
                2 => 0,
                n => ((i * 23 + i / 5 + n * 7) % 16) as u32,
            });
            let mut expected = [[0u8; 64]; LEN_MAX];
            for i in 0..len {
                expected[i] =
                    short_block(&adrs.with_word2(i as u32), &signature[i * N..(i + 1) * N]);
            }
            chain_blocks_portable::<N>(&seed.state, &mut expected[..len], &digits, &[15; LEN_MAX]);
            let mut buf = [0u8; 2304];
            arm_wide::wots_recover::<N>(&seed.state, adrs, &signature, &digits[..len], &mut buf);
            for i in 0..len {
                assert_eq!(&buf[22 + i * N..22 + (i + 1) * N], &expected[i][22..22 + N]);
            }
        }
    }

    #[test]
    fn arm_wots_digits_and_recover_match_portable() {
        check_digits::<16>();
        check_digits::<24>();
        check_digits::<32>();
        check_recover::<16>();
        check_recover::<24>();
        check_recover::<32>();
    }
}
