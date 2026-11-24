// Compute the XMSS authentication nodes as soon as the message digest fixes
// the tree addresses. Only the WOTS signatures depend on the preceding root.
use super::super::hash::Seed;
use super::super::wots::wots_sign;
use super::super::xmss::xmss_pk_from_sig;
use super::*;
use crate::address::WOTS_HASH;
use core::sync::atomic::{AtomicUsize, Ordering};
use std::{sync::OnceLock, thread};

// Worker stacks can be recycled by the OS after a scoped thread exits. Keep
// the secret computation below a frame from which we can scrub its scratch,
// just as the compatibility API does for the calling thread.
#[inline(never)]
fn run_worker(fill: &impl Fn()) {
    fill();
}

#[inline(never)]
fn scrub_worker_stack() {
    use zeroize::Zeroize;
    let mut scratch = [0u8; 64 * 1024];
    scratch.zeroize();
}

pub(super) fn sign<const N: usize>(
    p: &Params,
    md: &[u8],
    sk: &[u8; N],
    seed: &Seed<N>,
    fors_addr: Adrs,
    r: &[u8; N],
    mut tree: u64,
    mut leaf: u32,
) -> Option<Vec<u8>> {
    let workers = thread::available_parallelism()
        .ok()?
        .get()
        .min(p.d as usize + 1);
    if workers < 2 || p.hp == 0 {
        return None;
    }
    let mut layers = Vec::with_capacity(p.d as usize);
    for j in 0..p.d {
        layers.push((Adrs::new().with_layer(j).with_tree(tree), leaf));
        leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
        tree >>= p.hp;
    }
    let nodes: Vec<OnceLock<[u8; N]>> = (0..layers.len() * p.hp as usize)
        .map(|_| OnceLock::new())
        .collect();
    let next = AtomicUsize::new(0);
    let fill = || loop {
        let job = next.fetch_add(1, Ordering::Relaxed);
        let Some(slot) = nodes.get(job) else { break };
        // Largest subtrees first to avoid a single expensive job at the end.
        let height = p.hp - 1 - (job / layers.len()) as u32;
        let (addr, index) = layers[job % layers.len()];
        let value = xmss_node(sk, (index >> height) ^ 1, height, seed, addr);
        slot.set(value).expect("unique XMSS job");
    };

    let (fors, mut root) = thread::scope(|scope| {
        for _ in 1..workers {
            // The caller drains the same queue when the OS declines a worker.
            if thread::Builder::new()
                .spawn_scoped(scope, || {
                    run_worker(&fill);
                    scrub_worker_stack();
                })
                .is_err()
            {
                break;
            }
        }
        let fors = fors_sign(p, md, sk, seed, fors_addr);
        let root = fors_pk_from_sig(p, &fors, md, seed, fors_addr);
        fill();
        (fors, root)
    });

    let mut signature = Vec::with_capacity(p.sig_bytes());
    signature.extend_from_slice(r);
    signature.extend_from_slice(&fors);
    for (j, &(addr, index)) in layers.iter().enumerate() {
        let start = signature.len();
        signature.extend(wots_sign(
            &root,
            sk,
            seed,
            addr.with_type(WOTS_HASH).with_keypair(index),
        ));
        for height in 0..p.hp {
            let job = (p.hp - 1 - height) as usize * layers.len() + j;
            signature.extend_from_slice(nodes[job].get().expect("all XMSS jobs joined"));
        }
        if j + 1 < layers.len() {
            root = xmss_pk_from_sig(p, index, &signature[start..], &root, seed, addr);
        }
    }
    Some(signature)
}
