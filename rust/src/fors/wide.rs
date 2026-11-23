//! Compute the leaves and reduce one FORS subtree in place.
use super::*;

pub(super) fn subtree<const N: usize>(
    sk_seed: &[u8; N],
    index: u32,
    height: u32,
    seed: &Seed<N>,
    adrs: Adrs,
) -> [u8; N] {
    let n = 1usize << height;
    let mut nodes = [[0u8; N]; BATCH];
    crate::sha256::x86::fors_leaves(&seed.state, sk_seed, adrs, index << height, &mut nodes[..n]);
    for level in 1..=height {
        let first = index << (height - level);
        let address = adrs.with_word2(level);
        let count = n >> level;
        let done = if N == 16 {
            crate::sha256::x86::fors_parents(&seed.state, address, first, &mut nodes, count)
        } else {
            crate::sha512::parents::parents(&seed.state512, address, first, &mut nodes, count)
        };
        for j in done..count {
            nodes[j] = thash_pair(
                seed,
                &address.with_word3(first + j as u32),
                &nodes[2 * j],
                &nodes[2 * j + 1],
            );
        }
    }
    nodes[0]
}
