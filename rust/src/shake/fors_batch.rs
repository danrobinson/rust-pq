//! Parallel FORS trees: horizontal 8-way subtree batching for signing (zero wasted
//! lanes even on a single tree) and active-lane zero-copy climbing for recovery.
use super::batch::{adrs_words, pair_active, seed_words, short_active};
use super::hash::{digest, start, thash_pair};
use crate::address::{Adrs, FORS_PRF, FORS_ROOTS, FORS_TREE};
use crate::params::{Params, K_MAX};
use crate::shake256::parallel::{self, States, WIDTH};
use alloc::vec::Vec;

#[inline(always)]
fn word(input: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(input[i * 8..i * 8 + 8].try_into().unwrap())
}

/// Fused `FORS_PRF` followed immediately by level-0 `FORS_TREE` hashing in place,
/// avoiding intermediate byte serialization between secret generation and leaf hashing.
pub(super) fn fors_leaves_fused<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    indices: &[u32; WIDTH],
    active: usize,
) -> [[u8; N]; WIDTH] {
    let n = N / 8;
    let offset = n + 4;
    let pad = offset + n;
    let sw = seed_words(seed);
    let skw = seed_words(sk);
    let aw_prf = adrs_words(&addr.with_type(FORS_PRF).with_keypair(addr.keypair));
    let aw_tree = adrs_words(&addr.with_type(FORS_TREE).with_keypair(addr.keypair));
    let mut w3 = [0u64; WIDTH];
    for lane in 0..active {
        w3[lane] = u64::from(indices[lane].swap_bytes()) << 32;
    }

    let mut state: States = [[0; WIDTH]; 25];
    for j in 0..n {
        state[j] = [sw[j]; WIDTH];
        state[offset + j] = [skw[j]; WIDTH];
    }
    state[n] = [aw_prf[0]; WIDTH];
    state[n + 1] = [aw_prf[1]; WIDTH];
    state[n + 2] = [aw_prf[2]; WIDTH];
    state[n + 3] = w3;
    state[pad] = [0x1f; WIDTH];
    state[16] = [1u64 << 63; WIDTH];
    parallel::permute_active(&mut state, active);

    // Refill in place for level-0 FORS_TREE: same seed, layer, tree, keypair, and word3.
    for j in 0..n {
        state[offset + j] = state[j];
        state[j] = [sw[j]; WIDTH];
    }
    state[n] = [aw_tree[0]; WIDTH];
    state[n + 1] = [aw_tree[1]; WIDTH];
    state[n + 2] = [aw_tree[2]; WIDTH];
    state[n + 3] = w3;
    state[pad] = [0x1f; WIDTH];
    for w in &mut state[pad + 1..25] {
        *w = [0; WIDTH];
    }
    state[16] = [1u64 << 63; WIDTH];
    parallel::permute_active(&mut state, active);

    let mut out = [[0u8; N]; WIDTH];
    for j in 0..n {
        for lane in 0..active {
            out[lane][8 * j..8 * j + 8].copy_from_slice(&state[j][lane].to_le_bytes());
        }
    }
    out
}

/// Compute a FORS subtree of `height >= 3` horizontally in 8-way batches (zero heap
/// allocation, zero wasted lanes, fused PRF -> leaf hash, and 8-way parent hashing).
pub(super) fn fors_subtree_horiz<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    node_index: u32,
    height: u32,
) -> [u8; N] {
    let z = height as usize;
    debug_assert!(z <= 15);
    let tree_adrs = addr.with_type(FORS_TREE).with_keypair(addr.keypair);
    let mut buf = [[[0u8; N]; 16]; 16];
    let mut len = [0usize; 16];
    let mut next_idx = [0u32; 16];
    for h in 0..=z {
        next_idx[h] = node_index << (z - h);
    }

    let blocks = 1u32 << (height - 3);
    let first_leaf = node_index << height;
    let mut addrs = [tree_adrs; WIDTH];
    let mut left = [[0u8; N]; WIDTH];
    let mut right = [[0u8; N]; WIDTH];

    for b in 0..blocks {
        let base_leaf = first_leaf + b * 8;
        let indices: [u32; WIDTH] = core::array::from_fn(|lane| base_leaf + lane as u32);
        let leaves = fors_leaves_fused(sk, seed, addr, &indices, 8);
        let dst = len[0];
        buf[0][dst..dst + 8].copy_from_slice(&leaves);
        len[0] = dst + 8;

        for h in 0..z {
            if len[h] < 16 {
                break;
            }
            let base = next_idx[h + 1];
            let lvl = (h + 1) as u32;
            for k in 0..8 {
                addrs[k] = tree_adrs.with_word2(lvl).with_word3(base + k as u32);
                left[k] = buf[h][2 * k];
                right[k] = buf[h][2 * k + 1];
            }
            let parents = pair_active(seed, &addrs, &left, &right, 8);
            len[h] = 0;
            let pdst = len[h + 1];
            buf[h + 1][pdst..pdst + 8].copy_from_slice(&parents);
            len[h + 1] = pdst + 8;
            next_idx[h + 1] = base + 8;
        }
    }

    for h in 0..z {
        let count = len[h] / 2;
        if count == 0 {
            continue;
        }
        let base = next_idx[h + 1];
        let lvl = (h + 1) as u32;
        if count == 1 {
            let parent_adrs = tree_adrs.with_word2(lvl).with_word3(base);
            let p = thash_pair(seed, &parent_adrs, &buf[h][0], &buf[h][1]);
            let pdst = len[h + 1];
            buf[h + 1][pdst] = p;
            len[h + 1] = pdst + 1;
            next_idx[h + 1] = base + 1;
        } else {
            for k in 0..count {
                addrs[k] = tree_adrs.with_word2(lvl).with_word3(base + k as u32);
                left[k] = buf[h][2 * k];
                right[k] = buf[h][2 * k + 1];
            }
            let parents = pair_active(seed, &addrs, &left, &right, count);
            let pdst = len[h + 1];
            buf[h + 1][pdst..pdst + count].copy_from_slice(&parents[..count]);
            len[h + 1] = pdst + count;
            next_idx[h + 1] = base + count as u32;
        }
        len[h] = 0;
    }

    buf[z][0]
}

fn batch_leaves_slice<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    indices: &[u32],
    out: &mut [[u8; N]],
) {
    let mut i = 0;
    while i < indices.len() {
        let active = (indices.len() - i).min(WIDTH);
        let mut batch = [0u32; WIDTH];
        batch[..active].copy_from_slice(&indices[i..i + active]);
        let leaves = fors_leaves_fused(sk, seed, addr, &batch, active);
        out[i..i + active].copy_from_slice(&leaves[..active]);
        i += active;
    }
}

fn batch_pairs_slice<const N: usize>(
    seed: &[u8; N],
    tree_adrs: Adrs,
    level: u32,
    node_indices: &[u32],
    children: &[[u8; N]],
    out: &mut [[u8; N]],
) {
    let mut addrs = [tree_adrs; WIDTH];
    let mut left = [[0u8; N]; WIDTH];
    let mut right = [[0u8; N]; WIDTH];
    let mut i = 0;
    while i < node_indices.len() {
        let active = (node_indices.len() - i).min(WIDTH);
        for lane in 0..active {
            addrs[lane] = tree_adrs
                .with_word2(level)
                .with_word3(node_indices[i + lane]);
            left[lane] = children[2 * (i + lane)];
            right[lane] = children[2 * (i + lane) + 1];
        }
        let parents = pair_active(seed, &addrs, &left, &right, active);
        out[i..i + active].copy_from_slice(&parents[..active]);
        i += active;
    }
}

fn nodes_fallback<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    indices: [u32; WIDTH],
    level: u32,
    active: usize,
) -> [[u8; N]; WIDTH] {
    if level == 0 {
        fors_leaves_fused(sk, seed, addr, &indices, active)
    } else {
        let left = nodes_fallback(sk, seed, addr, indices.map(|i| i * 2), level - 1, active);
        let right = nodes_fallback(
            sk,
            seed,
            addr,
            indices.map(|i| i * 2 + 1),
            level - 1,
            active,
        );
        let addresses = indices.map(|i| addr.with_word2(level).with_word3(i));
        pair_active(seed, &addresses, &left, &right, active)
    }
}

pub(super) fn sign<const N: usize>(
    p: &Params,
    selections: &[u32],
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
) -> Vec<u8> {
    let k = selections.len();
    let a = p.a;
    let stride = (a as usize + 1) * N;
    let mut sig = alloc::vec![0u8; k * stride];
    let prf = addr.with_type(FORS_PRF).with_keypair(addr.keypair);
    let tree_adrs = addr.with_type(FORS_TREE).with_keypair(addr.keypair);

    // 1. Secret values for all `k` trees in batches of WIDTH (exact active tail).
    let mut first = 0;
    while first < k {
        let active = (k - first).min(WIDTH);
        let addrs: [Adrs; WIDTH] = core::array::from_fn(|lane| {
            let tree = first + lane.min(active - 1);
            prf.with_word3(((tree as u32) << a) + selections[tree])
        });
        let sec = short_active(seed, &addrs, &[*sk; WIDTH], active);
        for lane in 0..active {
            sig[(first + lane) * stride..(first + lane) * stride + N].copy_from_slice(&sec[lane]);
        }
        first += active;
    }

    if WIDTH != 8 {
        for first in (0..k).step_by(WIDTH) {
            let active = (k - first).min(WIDTH);
            let indices: [u32; WIDTH] = core::array::from_fn(|lane| {
                let tree = first + lane.min(active - 1);
                ((tree as u32) << a) + selections[tree]
            });
            for j in 0..a {
                let siblings =
                    nodes_fallback(sk, seed, addr, indices.map(|i| (i >> j) ^ 1), j, active);
                for lane in 0..active {
                    let pos = (first + lane) * stride + (j as usize + 1) * N;
                    sig[pos..pos + N].copy_from_slice(&siblings[lane]);
                }
            }
        }
        return sig;
    }

    // 2. Small auth subtrees (heights 0, 1, 2): batch horizontally across all `k` trees.
    debug_assert!(k <= K_MAX);
    // Height 0: `k` single leaves.
    if a > 0 {
        let mut idx0 = [0u32; K_MAX];
        for tree in 0..k {
            idx0[tree] = (((tree as u32) << a) + selections[tree]) ^ 1;
        }
        let mut out0 = [[0u8; N]; K_MAX];
        batch_leaves_slice(sk, seed, addr, &idx0[..k], &mut out0[..k]);
        for tree in 0..k {
            let pos = tree * stride + N;
            sig[pos..pos + N].copy_from_slice(&out0[tree]);
        }
    }
    // Height 1: `2k` leaves -> `k` level-1 parents.
    if a > 1 {
        let mut leaf_idx = [0u32; 2 * K_MAX];
        let mut node_idx = [0u32; K_MAX];
        for tree in 0..k {
            let sib = ((((tree as u32) << a) + selections[tree]) >> 1) ^ 1;
            node_idx[tree] = sib;
            leaf_idx[2 * tree] = 2 * sib;
            leaf_idx[2 * tree + 1] = 2 * sib + 1;
        }
        let mut leaves = [[0u8; N]; 2 * K_MAX];
        let mut lvl1 = [[0u8; N]; K_MAX];
        batch_leaves_slice(sk, seed, addr, &leaf_idx[..2 * k], &mut leaves[..2 * k]);
        batch_pairs_slice(
            seed,
            tree_adrs,
            1,
            &node_idx[..k],
            &leaves[..2 * k],
            &mut lvl1[..k],
        );
        for tree in 0..k {
            let pos = tree * stride + 2 * N;
            sig[pos..pos + N].copy_from_slice(&lvl1[tree]);
        }
    }
    // Height 2: `4k` leaves -> `2k` level-1 -> `k` level-2 parents.
    if a > 2 {
        let mut leaf_idx = [0u32; 4 * K_MAX];
        let mut n1_idx = [0u32; 2 * K_MAX];
        let mut n2_idx = [0u32; K_MAX];
        for tree in 0..k {
            let sib = ((((tree as u32) << a) + selections[tree]) >> 2) ^ 1;
            n2_idx[tree] = sib;
            n1_idx[2 * tree] = 2 * sib;
            n1_idx[2 * tree + 1] = 2 * sib + 1;
            for c in 0..4 {
                leaf_idx[4 * tree + c] = 4 * sib + c as u32;
            }
        }
        let mut leaves = [[0u8; N]; 4 * K_MAX];
        let mut lvl1 = [[0u8; N]; 2 * K_MAX];
        let mut lvl2 = [[0u8; N]; K_MAX];
        batch_leaves_slice(sk, seed, addr, &leaf_idx[..4 * k], &mut leaves[..4 * k]);
        batch_pairs_slice(
            seed,
            tree_adrs,
            1,
            &n1_idx[..2 * k],
            &leaves[..4 * k],
            &mut lvl1[..2 * k],
        );
        batch_pairs_slice(
            seed,
            tree_adrs,
            2,
            &n2_idx[..k],
            &lvl1[..2 * k],
            &mut lvl2[..k],
        );
        for tree in 0..k {
            let pos = tree * stride + 3 * N;
            sig[pos..pos + N].copy_from_slice(&lvl2[tree]);
        }
    }

    // 3. Heights >= 3: each sibling subtree has 2^j >= 8 leaves, batched horizontally 8-way.
    for tree in 0..k {
        let leaf = ((tree as u32) << a) + selections[tree];
        for j in 3..a {
            let sib = (leaf >> j) ^ 1;
            let node = fors_subtree_horiz(sk, seed, addr, sib, j);
            let pos = tree * stride + (j as usize + 1) * N;
            sig[pos..pos + N].copy_from_slice(&node);
        }
    }
    sig
}

/// Zero-copy active-lane FORS public key recovery: keeps running node hashes in Keccak
/// word arrays across all `a + 1` levels and uses `permute_active` on partial batches.
pub(super) fn recover<const N: usize>(
    p: &Params,
    selections: &[u32],
    sig: &[u8],
    seed: &[u8; N],
    addr: Adrs,
) -> [u8; N] {
    let n = N / 8;
    let offset = n + 4;
    let pad_short = offset + n;
    let pad_pair = offset + 2 * n;
    let stride = p.a as usize + 1;
    let sw = seed_words(seed);
    let aw = adrs_words(&addr.with_type(FORS_TREE).with_keypair(addr.keypair));

    let mut pk = start(seed, &addr.with_type(FORS_ROOTS).with_keypair(addr.keypair));
    let mut state: States = [[0; WIDTH]; 25];

    for first in (0..selections.len()).step_by(WIDTH) {
        let active = (selections.len() - first).min(WIDTH);
        let mut indices = [0u32; WIDTH];
        for lane in 0..active {
            let tree = first + lane;
            indices[lane] = ((tree as u32) << p.a) + selections[tree];
        }

        // Level 0: hash secret leaves into level-0 tree nodes.
        for j in 0..n {
            state[j] = [sw[j]; WIDTH];
        }
        state[n] = [aw[0]; WIDTH];
        state[n + 1] = [aw[1]; WIDTH];
        state[n + 2] = [aw[2]; WIDTH];
        for lane in 0..active {
            state[n + 3][lane] = u64::from(indices[lane].swap_bytes()) << 32;
            let blk = &sig[(first + lane) * stride * N..((first + lane) * stride + 1) * N];
            for j in 0..n {
                state[offset + j][lane] = word(blk, j);
            }
        }
        state[pad_short] = [0x1f; WIDTH];
        for w in &mut state[pad_short + 1..25] {
            *w = [0; WIDTH];
        }
        state[16] = [1u64 << 63; WIDTH];
        parallel::permute_active(&mut state, active);

        // Levels 1..=a: climb auth paths in place without byte re-serialization.
        for lvl in 0..p.a {
            let mut cur = [[0u64; WIDTH]; 4];
            for j in 0..n {
                cur[j] = state[j];
                state[j] = [sw[j]; WIDTH];
            }
            state[n] = [aw[0]; WIDTH];
            state[n + 1] = [aw[1]; WIDTH];
            state[n + 2] = [aw[2]; WIDTH];
            let lvl_lo = u64::from((lvl + 1).swap_bytes());
            for lane in 0..active {
                let idx = indices[lane];
                let parent = idx >> 1;
                indices[lane] = parent;
                state[n + 3][lane] = lvl_lo | (u64::from(parent.swap_bytes()) << 32);
                let sib_blk_idx = (first + lane) * stride + lvl as usize + 1;
                let sib = &sig[sib_blk_idx * N..(sib_blk_idx + 1) * N];
                if idx & 1 == 0 {
                    for j in 0..n {
                        state[offset + j][lane] = cur[j][lane];
                        state[offset + n + j][lane] = word(sib, j);
                    }
                } else {
                    for j in 0..n {
                        state[offset + j][lane] = word(sib, j);
                        state[offset + n + j][lane] = cur[j][lane];
                    }
                }
            }
            for w in &mut state[pad_pair + 1..25] {
                *w = [0; WIDTH];
            }
            state[pad_pair] = [0x1f; WIDTH];
            for v in &mut state[16] {
                *v |= 1u64 << 63;
            }
            parallel::permute_active(&mut state, active);
        }

        for lane in 0..active {
            let mut root = [0u8; N];
            for j in 0..n {
                root[8 * j..8 * j + 8].copy_from_slice(&state[j][lane].to_le_bytes());
            }
            pk.absorb(&root);
        }
    }
    digest(pk)
}
