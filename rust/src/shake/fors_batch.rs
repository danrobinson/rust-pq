//! Parallel FORS trees. A lane keeps its tree number through every hash level.
use super::batch::{pair, short};
use super::hash::{digest, start};
use crate::address::{Adrs, FORS_PRF, FORS_ROOTS};
use crate::params::Params;
use crate::shake256::parallel::WIDTH;
use crate::util::block;
use alloc::vec::Vec;

fn secrets<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    indices: [u32; WIDTH],
) -> [[u8; N]; WIDTH] {
    let prf = addr.with_type(FORS_PRF).with_keypair(addr.keypair);
    short(seed, &indices.map(|i| prf.with_word3(i)), &[*sk; WIDTH])
}

fn nodes<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    indices: [u32; WIDTH],
    level: u32,
) -> [[u8; N]; WIDTH] {
    let addresses = indices.map(|i| addr.with_word2(level).with_word3(i));
    if level == 0 {
        short(seed, &addresses, &secrets(sk, seed, addr, indices))
    } else {
        let left = nodes(sk, seed, addr, indices.map(|i| i * 2), level - 1);
        let right = nodes(sk, seed, addr, indices.map(|i| i * 2 + 1), level - 1);
        pair(seed, &addresses, &left, &right)
    }
}

pub(super) fn sign<const N: usize>(
    p: &Params,
    selections: &[u32],
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
) -> Vec<u8> {
    let stride = (p.a as usize + 1) * N;
    let mut sig = alloc::vec![0; selections.len()*stride];
    for first in (0..selections.len()).step_by(WIDTH) {
        let active = (selections.len() - first).min(WIDTH);
        // A partial batch repeats its last valid tree in the spare lanes.
        let indices = core::array::from_fn(|lane| {
            let tree = first + lane.min(active - 1);
            ((tree as u32) << p.a) + selections[tree]
        });
        let secret = secrets(sk, seed, addr, indices);
        for lane in 0..active {
            sig[(first + lane) * stride..(first + lane) * stride + N]
                .copy_from_slice(&secret[lane]);
        }
        for j in 0..p.a {
            let siblings = nodes(sk, seed, addr, indices.map(|i| (i >> j) ^ 1), j);
            for lane in 0..active {
                let pos = (first + lane) * stride + (j as usize + 1) * N;
                sig[pos..pos + N].copy_from_slice(&siblings[lane]);
            }
        }
    }
    sig
}

pub(super) fn recover<const N: usize>(
    p: &Params,
    selections: &[u32],
    sig: &[u8],
    seed: &[u8; N],
    addr: Adrs,
) -> [u8; N] {
    let stride = p.a as usize + 1;
    let mut pk = start(seed, &addr.with_type(FORS_ROOTS).with_keypair(addr.keypair));
    for first in (0..selections.len()).step_by(WIDTH) {
        let active = (selections.len() - first).min(WIDTH);
        let trees: [usize; WIDTH] = core::array::from_fn(|lane| first + lane.min(active - 1));
        let mut indices = trees.map(|tree| ((tree as u32) << p.a) + selections[tree]);
        let leaves = trees.map(|tree| block(sig, tree * stride));
        let mut values = short(
            seed,
            &indices.map(|i| addr.with_word2(0).with_word3(i)),
            &leaves,
        );
        for j in 0..p.a {
            let siblings = trees.map(|tree| block(sig, tree * stride + j as usize + 1));
            let left = core::array::from_fn(|lane| {
                if indices[lane] & 1 == 0 {
                    values[lane]
                } else {
                    siblings[lane]
                }
            });
            let right = core::array::from_fn(|lane| {
                if indices[lane] & 1 == 0 {
                    siblings[lane]
                } else {
                    values[lane]
                }
            });
            indices = indices.map(|i| i >> 1);
            values = pair(
                seed,
                &indices.map(|i| addr.with_word2(j + 1).with_word3(i)),
                &left,
                &right,
            );
        }
        for value in &values[..active] {
            pk.absorb(value);
        }
    }
    digest(pk)
}
