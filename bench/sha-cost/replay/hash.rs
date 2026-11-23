//! Capture values at the hash boundaries of the library's portable SLH schedule.
use crate::{address::Adrs, params::Params, trace::*};
use native::hash as real;
pub use real::{pair_block, short_block, value, Seed};

pub fn seed_ctx<const N: usize>(pk: &[u8; N]) -> Seed<N> {
    capture(|t| t.ops.push(Op::Seed(t.id(pk))));
    real::seed_ctx(pk)
}

pub fn chain_blocks<const N: usize>(
    state: &[u32; 8],
    blocks: &mut [[u8; 64]],
    starts: &[u32],
    ends: &[u32],
) {
    capture(|t| {
        let mut lanes = Vec::with_capacity(blocks.len());
        for (i, b) in blocks.iter().enumerate() {
            let payload = usize::from(u16::from_be_bytes([b[62], b[63]])) / 8 - 86;
            assert!(payload == N || payload == 2 * N);
            let left = t.id(&b[22..22 + N]);
            let right = (payload == 2 * N).then(|| t.id(&b[22 + N..22 + 2 * N]));
            let mut template = *b;
            template[22..22 + payload].fill(0);
            lanes.push(Lane {
                template,
                left,
                right,
                start: starts[i],
                end: ends[i],
            });
        }
        real::chain_blocks::<N>(state, blocks, starts, ends);
        let out = t.values.len();
        for b in blocks.iter() {
            t.output(&b[22..22 + N]);
        }
        t.ops.push(Op::Chains { lanes, out });
    })
}

fn record<const N: usize>(addr: &Adrs, inputs: &[u8], kind: Kind, result: [u8; N]) -> [u8; N] {
    capture(|t| {
        assert_eq!(inputs.len() % N, 0);
        let ids = inputs.chunks_exact(N).map(|v| t.id(v)).collect();
        let out = t.output(&result);
        t.ops.push(Op::Hash {
            addr: *addr,
            ids,
            kind,
            out,
        });
    });
    result
}
pub fn thash_short<const N: usize>(s: &Seed<N>, a: &Adrs, m: &[u8]) -> [u8; N] {
    record(a, m, Kind::Short, real::thash_short(s, a, m))
}
pub fn thash_pair<const N: usize>(s: &Seed<N>, a: &Adrs, l: &[u8; N], r: &[u8; N]) -> [u8; N] {
    record(
        a,
        &[l.as_slice(), r.as_slice()].concat(),
        Kind::Pair,
        real::thash_pair(s, a, l, r),
    )
}
pub fn thash<const N: usize>(s: &Seed<N>, a: &Adrs, m: &[u8]) -> [u8; N] {
    record(a, m, Kind::Many, real::thash(s, a, m))
}
pub fn thash_values<const N: usize>(s: &Seed<N>, a: &Adrs, b: &[[u8; 64]]) -> [u8; N] {
    let m = b
        .iter()
        .flat_map(|x| &x[22..22 + N])
        .copied()
        .collect::<Vec<_>>();
    record(a, &m, Kind::Endpoints, real::thash_values(s, a, b))
}
pub fn prf_msg<const N: usize>(key: &[u8; N], rnd: &[u8; N], m: &[u8]) -> [u8; N] {
    let value = real::prf_msg(key, rnd, m);
    capture(|t| {
        let (k, r) = (t.id(key), t.id(rnd));
        let o = t.output(&value);
        t.ops.push(Op::Random(k, r, m.into(), o));
    });
    value
}
pub fn h_msg<const N: usize>(
    p: &Params,
    r: &[u8; N],
    pk: &[u8; N],
    root: &[u8; N],
    m: &[u8],
) -> Vec<u8> {
    let digest = real::h_msg(p, r, pk, root, m);
    capture(|t| {
        t.ops
            .push(Op::Message(t.id(r), t.id(pk), t.id(root), m.into()));
        t.digest = digest.clone();
    });
    digest
}
