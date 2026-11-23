//! Hash the SLH domain separator and context as a prefix of the caller's message.
use super::*;
use crate::{sha256, sha512};

trait MessageHash<const B: usize> {
    type State: Copy;
    type Digest;
    fn compress(state: &Self::State, bytes: &[u8], offset: usize) -> Self::State;
    fn finish(state: &Self::State, pre: usize, msg: &[u8]) -> Self::Digest;
}

struct Sha256;
struct Sha512;

impl MessageHash<64> for Sha256 {
    type State = [u32; 8];
    type Digest = [u8; 32];
    fn compress(state: &Self::State, bytes: &[u8], offset: usize) -> Self::State {
        sha256::compress(state, bytes, offset)
    }
    fn finish(state: &Self::State, pre: usize, msg: &[u8]) -> Self::Digest {
        sha256::sha256_from(state, pre, msg)
    }
}

impl MessageHash<128> for Sha512 {
    type State = [u64; 8];
    type Digest = [u8; 64];
    fn compress(state: &Self::State, bytes: &[u8], offset: usize) -> Self::State {
        sha512::compress(state, bytes, offset)
    }
    fn finish(state: &Self::State, pre: usize, msg: &[u8]) -> Self::Digest {
        sha512::sha512_from(state, pre, msg)
    }
}

fn continued<const B: usize, H: MessageHash<B>>(
    mut state: H::State, pre: usize, prefix: &[u8], msg: &[u8],
) -> H::Digest {
    let mut position = 0;
    while prefix.len() - position >= B {
        state = H::compress(&state, prefix, position);
        position += B;
    }
    let consumed = pre + position;
    let tail = &prefix[position..];
    let offset = tail.len();
    if offset == 0 {
        return H::finish(&state, consumed, msg);
    }
    let mut head = [0u8; B];
    head[..offset].copy_from_slice(tail);
    let n = (B - offset).min(msg.len());
    head[offset..offset + n].copy_from_slice(&msg[..n]);
    if offset + n < B {
        return H::finish(&state, consumed, &head[..offset + n]);
    }
    state = H::compress(&state, &head, 0);
    H::finish(&state, consumed + B, &msg[n..])
}

fn digest<const N: usize>(
    p: &Params,
    r: &[u8; N],
    pk: &[u8; N],
    root: &[u8; N],
    ctx: &[u8],
    msg: &[u8],
) -> Vec<u8> {
    let domain = [0, ctx.len() as u8];
    let mut prefix = [0; 3 * 32 + 2 + 255];
    prefix[..N].copy_from_slice(r);
    prefix[N..2 * N].copy_from_slice(pk);
    prefix[2 * N..3 * N].copy_from_slice(root);
    prefix[3 * N..3 * N + 2].copy_from_slice(&domain);
    let used = 3 * N + 2 + ctx.len();
    prefix[3 * N + 2..used].copy_from_slice(ctx);
    let mut seed = Vec::with_capacity(2 * N + 64);
    seed.extend_from_slice(r);
    seed.extend_from_slice(pk);
    if N == 16 {
        let d = continued::<64, Sha256>(sha256::H0, 0, &prefix[..used], msg);
        seed.extend_from_slice(&d);
        crate::hash::mgf1_sha256(&seed, p.m)
    } else {
        let d = continued::<128, Sha512>(sha512::H0, 0, &prefix[..used], msg);
        seed.extend_from_slice(&d);
        crate::hash::mgf1_sha512(&seed, p.m)
    }
}

fn randomizer<const N: usize>(key: &[u8; N], random: &[u8; N], ctx: &[u8], msg: &[u8]) -> [u8; N] {
    let domain = [0, ctx.len() as u8];
    let mut prefix = [0; 32 + 2 + 255];
    prefix[..N].copy_from_slice(random);
    prefix[N..N + 2].copy_from_slice(&domain);
    let used = N + 2 + ctx.len();
    prefix[N + 2..used].copy_from_slice(ctx);
    macro_rules! hmac {
        ($sha:ident,$b:literal,$d:literal,$hash:ty) => {{
            let mut pad = [0x36; $b];
            for i in 0..N {
                pad[i] ^= key[i];
            }
            let state = $sha::compress(&$sha::H0, &pad, 0);
            let inner = continued::<$b, $hash>(state, $b, &prefix[..used], msg);
            pad.fill(0x5c);
            for i in 0..N {
                pad[i] ^= key[i];
            }
            let outer = $sha::compress(&$sha::H0, &pad, 0);
            // The inner HMAC digest and both key-derived blocks remain on the stack.
            pad.fill(0);
            pad[..$d].copy_from_slice(&inner);
            pad[$d] = 0x80;
            pad[$b - 2..].copy_from_slice(&((($b + $d) * 8) as u16).to_be_bytes());
            let mut result = [0u8; N];
            result.copy_from_slice(&$sha::digest(&$sha::compress(&outer, &pad, 0))[..N]);
            result
        }};
    }
    if N == 16 {
        hmac!(sha256, 64, 32, Sha256)
    } else {
        hmac!(sha512, 128, 64, Sha512)
    }
}

pub(super) fn sign<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sk: &[u8],
    addrnd: &[u8; N],
) -> Vec<u8> {
    let sk_seed = block::<N>(sk, 0);
    let sk_prf = block::<N>(sk, 1);
    let pk_seed = block::<N>(sk, 2);
    let pk_root = block::<N>(sk, 3);
    let r = randomizer(&sk_prf, addrnd, ctx, m);
    let digest = digest(p, &r, &pk_seed, &pk_root, ctx, m);
    sign_digest!(N, p, sk_seed, pk_seed, r, digest)
}

pub(super) fn verify<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sig: &[u8],
    pk: &[u8],
) -> bool {
    let sig_bytes = p.sig_bytes();
    if sig.len() != sig_bytes {
        return false;
    }
    let fors_end = N + p.fors_sig_bytes();
    let pk_seed = block::<N>(pk, 0);
    let pk_root = block::<N>(pk, 1);
    let r = block::<N>(sig, 0);
    let digest = digest(p, &r, &pk_seed, &pk_root, ctx, m);
    verify_digest!(N, p, pk_seed, pk_root, sig, sig_bytes, fors_end, digest)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check<const N: usize>(p: &Params) {
        let r = [0xab; N];
        let seed = [0x23; N];
        let root = [0x17; N];
        let bytes: [u8; 2305] = core::array::from_fn(|i| (i * 19 + i / 13) as u8);
        for context_len in [0, 1, 15, 63, 64, 127, 128, 254, 255] {
            let ctx = &bytes[..context_len];
            for n in [
                0, 1, 55, 56, 63, 64, 111, 112, 127, 128, 1023, 1024, 1025, 2305,
            ] {
                let msg = &bytes[..n];
                let joined = with_context(msg, ctx);
                assert_eq!(randomizer(&seed, &r, ctx, msg), prf_msg(&seed, &r, &joined));
                assert_eq!(
                    digest(p, &r, &seed, &root, ctx, msg),
                    h_msg(p, &r, &seed, &root, &joined)
                );
            }
        }
    }

    #[test]
    fn domain_and_context_match_contiguous_input() {
        check::<16>(&crate::sha2_128s::params::PARAMS);
        check::<24>(&crate::sha2_192s::params::PARAMS);
        check::<32>(&crate::sha2_256s::params::PARAMS);
    }
}
