//! SHAKE256 hash functions of FIPS 205 §11.1.
use crate::address::Adrs;
use crate::params::Params;
use crate::shake256::Sponge;
use alloc::vec::Vec;

pub type Seed<const N: usize> = [u8; N];

pub fn seed_ctx<const N: usize>(pk_seed: &[u8; N]) -> Seed<N> {
    *pk_seed
}

pub(super) fn start<const N: usize>(seed: &Seed<N>, adrs: &Adrs) -> Sponge {
    let mut sponge = Sponge::new();
    sponge.absorb(seed);
    sponge.absorb(&adrs.full());
    sponge
}

pub(super) fn digest<const N: usize>(sponge: Sponge) -> [u8; N] {
    let mut out = [0; N];
    sponge.finish(&mut out);
    out
}

pub(super) fn thash<const N: usize>(seed: &Seed<N>, adrs: &Adrs, value: &[u8; N]) -> [u8; N] {
    let mut sponge = start(seed, adrs);
    sponge.absorb(value);
    digest(sponge)
}

pub(super) fn thash_pair<const N: usize>(
    seed: &Seed<N>,
    adrs: &Adrs,
    a: &[u8; N],
    b: &[u8; N],
) -> [u8; N] {
    let mut sponge = start(seed, adrs);
    sponge.absorb(a);
    sponge.absorb(b);
    digest(sponge)
}

pub(super) fn prf_msg<const N: usize>(sk_prf: &[u8; N], opt_rand: &[u8; N], msg: &[u8]) -> [u8; N] {
    let mut sponge = Sponge::new();
    sponge.absorb(sk_prf);
    sponge.absorb(opt_rand);
    sponge.absorb(msg);
    digest(sponge)
}

pub(super) fn h_msg<const N: usize>(
    p: &Params,
    r: &[u8; N],
    pk_seed: &[u8; N],
    pk_root: &[u8; N],
    msg: &[u8],
) -> Vec<u8> {
    let mut sponge = Sponge::new();
    sponge.absorb(r);
    sponge.absorb(pk_seed);
    sponge.absorb(pk_root);
    sponge.absorb(msg);
    let mut out = alloc::vec![0; p.m];
    sponge.finish(&mut out);
    out
}

/// Zero-copy segmented `PRF_msg` with domain separator `0x00 || |ctx| || ctx || msg`.
#[cfg(feature = "platform-sha2")]
pub(super) fn prf_msg_ctx<const N: usize>(
    sk_prf: &[u8; N],
    opt_rand: &[u8; N],
    ctx: &[u8],
    msg: &[u8],
) -> [u8; N] {
    let mut sponge = Sponge::new();
    sponge.absorb(sk_prf);
    sponge.absorb(opt_rand);
    sponge.absorb(&[0, ctx.len() as u8]);
    sponge.absorb(ctx);
    sponge.absorb(msg);
    digest(sponge)
}

/// Zero-copy segmented `H_msg` with domain separator `0x00 || |ctx| || ctx || msg`.
#[cfg(feature = "platform-sha2")]
pub(super) fn h_msg_ctx<const N: usize>(
    p: &Params,
    r: &[u8; N],
    pk_seed: &[u8; N],
    pk_root: &[u8; N],
    ctx: &[u8],
    msg: &[u8],
) -> Vec<u8> {
    let mut sponge = Sponge::new();
    sponge.absorb(r);
    sponge.absorb(pk_seed);
    sponge.absorb(pk_root);
    sponge.absorb(&[0, ctx.len() as u8]);
    sponge.absorb(ctx);
    sponge.absorb(msg);
    let mut out = alloc::vec![0; p.m];
    sponge.finish(&mut out);
    out
}

#[cfg(all(test, feature = "platform-sha2"))]
mod tests {
    use super::*;
    use crate::slh::with_context;

    fn check<const N: usize>(p: &Params) {
        let r = [0xab; N];
        let seed = [0x23; N];
        let root = [0x17; N];
        let bytes: [u8; 2305] = core::array::from_fn(|i| (i * 19 + i / 13) as u8);
        for context_len in [0, 1, 15, 63, 64, 127, 135, 136, 254, 255] {
            let ctx = &bytes[..context_len];
            for n in [
                0, 1, 32, 135, 136, 137, 271, 272, 1023, 1024, 1025, 2305,
            ] {
                let msg = &bytes[..n];
                let joined = with_context(msg, ctx);
                assert_eq!(prf_msg_ctx(&seed, &r, ctx, msg), prf_msg(&seed, &r, &joined));
                assert_eq!(
                    h_msg_ctx(p, &r, &seed, &root, ctx, msg),
                    h_msg(p, &r, &seed, &root, &joined)
                );
            }
        }
    }

    #[test]
    fn segmented_shake_domain_and_context_match_contiguous_input() {
        check::<16>(&crate::shake_128s::params::PARAMS);
        check::<24>(&crate::shake_192s::params::PARAMS);
        check::<32>(&crate::shake_256s::params::PARAMS);
    }
}
