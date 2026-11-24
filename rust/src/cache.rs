//! Hypertree top-tree caching for SLH-DSA (all twelve SHA-2 and SHAKE parameter sets).
//!
//! In FIPS 205, the top XMSS tree (layer `d - 1`, tree `0`) is completely static for
//! the lifetime of a signing key and contains only public Merkle tree nodes (WOTS+ public
//! keys and internal hashes — zero secret key material). Precomputing all `2^(h' + 1) - 1`
//! nodes of this tree eliminates `1/d` of the hypertree work on every signature while
//! producing **100% byte-for-byte identical** FIPS 205 signatures.
//!
//! Memory footprint of the top tree:
//! - `128s`: 1,023 × 16 B = 16,368 B (~16 KiB)
//! - `128f`:    15 × 16 B =    240 B
//! - `192s`: 1,023 × 24 B = 24,552 B (~24 KiB)
//! - `192f`:    15 × 24 B =    360 B
//! - `256s`:   511 × 32 B = 16,352 B (~16 KiB)
//! - `256f`:    31 × 32 B =    992 B
//!
//! Optional layer `d - 2` subtree caching is also supported in two modes:
//! - Upfront precomputation via [`TopTreeCache::precompute_layer_d2`] (especially compact
//!   for `-f` sets: 1.9 KiB for 128f, 2.9 KiB for 192f, 15.9 KiB for 256f), usable from
//!   immutable `&TopTreeCache` across threads with zero locking.
//! - On-demand MRU caching via [`TopTreeCache::with_layer_d2_capacity`] and
//!   [`TopTreeCache::sign_mut`] / [`TopTreeCache::sign_deterministic_mut`].

use alloc::vec;
use alloc::vec::Vec;
use crate::address::{Adrs, FORS_TREE, TREE, WOTS_HASH};
use crate::params::Params;
use crate::util::{block, to_int};

/// The underlying hash family of an SLH-DSA parameter set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HashFamily {
    /// FIPS 205 §11.2 SHA-2 instantiation (SHA-256 / SHA-512).
    Sha2,
    /// FIPS 205 §11.1 SHAKE instantiation (SHAKE256).
    Shake,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct LayerD2Entry<const N: usize> {
    tree_index: u64,
    nodes: Vec<[u8; N]>,
}

// Shared by immutable cache misses and the mutable move-to-front path.
fn find_cached_index<const N: usize>(entries: &[LayerD2Entry<N>], tree_index: u64) -> Option<usize> {
    let mut pos = 0;
    while pos < entries.len() {
        if entries[pos].tree_index == tree_index {
            return Some(pos);
        }
        pos += 1;
    }
    None
}

/// Public Merkle-tree cache for the static top XMSS tree (layer `d - 1`) and optional
/// layer `d - 2` subtrees of an SLH-DSA signing key.
///
/// Stores only public tree nodes and `PK.seed` — **never** `SK.seed` or `SK.prf`.
/// Safe to share immutably across threads (`Send + Sync`) with zero synchronization
/// overhead during [`TopTreeCache::sign`] / [`TopTreeCache::sign_deterministic`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TopTreeCache<const N: usize> {
    family: HashFamily,
    hp: u32,
    d: u32,
    pk_seed: [u8; N],
    /// Complete top XMSS tree (layer `d - 1`, tree `0`), stored level by level from
    /// level `0` (`2^hp` leaves) up to level `hp` (1 root).
    top_tree: Vec<[u8; N]>,
    /// Optional cached layer `d - 2` subtrees, keyed by tree index (`0..2^hp`).
    /// Maintained in MRU order when populated dynamically via `*_mut` methods.
    layer_d2: Vec<LayerD2Entry<N>>,
    /// Maximum number of layer `d - 2` subtrees to keep during mutable cached signing.
    layer_d2_capacity: usize,
}

/// Byte offset (in nodes) of level `height` (`0 <= height <= hp`) in a level-contiguous
/// full binary Merkle tree of height `hp`.
#[inline(always)]
fn level_offset(hp: u32, height: u32) -> usize {
    (1usize << (hp + 1)) - (1usize << (hp + 1 - height))
}

/// Number of nodes in a complete binary tree of height `hp`: `2^(hp + 1) - 1`.
#[inline(always)]
fn tree_node_count(hp: u32) -> usize {
    (1usize << (hp + 1)) - 1
}

/// Extracts the `hp` authentication-path sibling nodes for `leaf` from a precomputed
/// level-contiguous tree of height `hp`.
#[inline]
fn append_auth_path<const N: usize>(tree: &[[u8; N]], hp: u32, leaf: u32, out: &mut Vec<u8>) {
    for h in 0..hp {
        let sib = ((leaf >> h) ^ 1) as usize;
        let off = level_offset(hp, h) + sib;
        out.extend_from_slice(&tree[off]);
    }
}

/// The root node of a level-contiguous tree.
#[inline(always)]
fn tree_root<const N: usize>(tree: &[[u8; N]]) -> [u8; N] {
    tree[tree.len() - 1]
}

/// The tree index encoded in the message digest: `h - h/d` bits (at most 64).
#[inline]
fn digest_tree(p: &Params, digest: &[u8]) -> u64 {
    let lo = p.md_bytes();
    to_int(&digest[lo..lo + p.tree_bytes()]) & (u64::MAX >> (64 - p.tree_bits()))
}

/// The leaf index encoded in the message digest: `h/d` bits.
#[inline]
fn digest_leaf(p: &Params, digest: &[u8]) -> u32 {
    let lo = p.md_bytes() + p.tree_bytes();
    (to_int(&digest[lo..lo + p.leaf_bytes()]) & ((1u64 << p.hp) - 1)) as u32
}

/// Builds `M' = toByte(0, 1) || toByte(|ctx|, 1) || ctx || M` (Algorithms 22 and 24).
fn with_pure_context(m: &[u8], ctx: &[u8]) -> Vec<u8> {
    let mut mp = Vec::with_capacity(2 + ctx.len() + m.len());
    mp.push(0);
    mp.push(ctx.len() as u8);
    mp.extend_from_slice(ctx);
    mp.extend_from_slice(m);
    mp
}

// ============================================================================
// SHA-2 family helpers (reusing crate's public SHA-2 / HW / platform kernels)
// ============================================================================

mod sha2_ops {
    use super::*;
    use crate::fors::{fors_pk_from_sig, fors_sign};
    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    use crate::fors::{fors_node, fors_sk_gen};
    use crate::hash::{h_msg, mgf1_sha256, mgf1_sha512, prf_msg, seed_ctx};
    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    use crate::hash::Seed;
    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    use crate::util::base_2b;
    use crate::wots::{wots_pk_gen, wots_sign};
    use crate::xmss::{hash2, xmss_pk_from_sig, xmss_sign};
    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    use crate::xmss::xmss_node;
    use crate::{sha256, sha512};

    fn continued_sha256(mut state: [u32; 8], pre: usize, prefix: &[u8], msg: &[u8]) -> [u8; 32] {
        let mut pos = 0;
        while prefix.len() - pos >= 64 {
            state = sha256::compress(&state, prefix, pos);
            pos += 64;
        }
        let consumed = pre + pos;
        let tail = &prefix[pos..];
        let off = tail.len();
        if off == 0 {
            return sha256::sha256_from(&state, consumed, msg);
        }
        let mut head = [0u8; 64];
        head[..off].copy_from_slice(tail);
        let n = (64 - off).min(msg.len());
        head[off..off + n].copy_from_slice(&msg[..n]);
        if off + n < 64 {
            return sha256::sha256_from(&state, consumed, &head[..off + n]);
        }
        state = sha256::compress(&state, &head, 0);
        sha256::sha256_from(&state, consumed + 64, &msg[n..])
    }

    fn continued_sha512(mut state: [u64; 8], pre: usize, prefix: &[u8], msg: &[u8]) -> [u8; 64] {
        let mut pos = 0;
        while prefix.len() - pos >= 128 {
            state = sha512::compress(&state, prefix, pos);
            pos += 128;
        }
        let consumed = pre + pos;
        let tail = &prefix[pos..];
        let off = tail.len();
        if off == 0 {
            return sha512::sha512_from(&state, consumed, msg);
        }
        let mut head = [0u8; 128];
        head[..off].copy_from_slice(tail);
        let n = (128 - off).min(msg.len());
        head[off..off + n].copy_from_slice(&msg[..n]);
        if off + n < 128 {
            return sha512::sha512_from(&state, consumed, &head[..off + n]);
        }
        state = sha512::compress(&state, &head, 0);
        sha512::sha512_from(&state, consumed + 128, &msg[n..])
    }

    /// Zero-copy `PRF_msg` and `H_msg` for pure signing with long messages (`m.len() >= 1024`).
    pub(super) fn pure_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        ctx: &[u8],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        if m.len() < 1024 {
            let mp = with_pure_context(m, ctx);
            let r = prf_msg::<N>(sk_prf, addrnd, &mp);
            let digest = h_msg::<N>(p, &r, pk_seed, pk_root, &mp);
            return (r, digest);
        }

        // Segmented PRF_msg (identical to slh/message.rs)
        let domain = [0u8, ctx.len() as u8];
        let mut prf_prefix = [0u8; 32 + 2 + 255];
        prf_prefix[..N].copy_from_slice(addrnd);
        prf_prefix[N..N + 2].copy_from_slice(&domain);
        let prf_used = N + 2 + ctx.len();
        prf_prefix[N + 2..prf_used].copy_from_slice(ctx);

        let r = if N == 16 {
            let mut pad = [0x36u8; 64];
            for i in 0..N {
                pad[i] ^= sk_prf[i];
            }
            let inner_st = sha256::compress(&sha256::H0, &pad, 0);
            let inner = continued_sha256(inner_st, 64, &prf_prefix[..prf_used], m);
            pad.fill(0x5c);
            for i in 0..N {
                pad[i] ^= sk_prf[i];
            }
            let outer_st = sha256::compress(&sha256::H0, &pad, 0);
            pad.fill(0);
            pad[..32].copy_from_slice(&inner);
            pad[32] = 0x80;
            pad[62..].copy_from_slice(&(((64 + 32) * 8) as u16).to_be_bytes());
            let mut out = [0u8; N];
            out.copy_from_slice(&sha256::digest(&sha256::compress(&outer_st, &pad, 0))[..N]);
            out
        } else {
            let mut pad = [0x36u8; 128];
            for i in 0..N {
                pad[i] ^= sk_prf[i];
            }
            let inner_st = sha512::compress(&sha512::H0, &pad, 0);
            let inner = continued_sha512(inner_st, 128, &prf_prefix[..prf_used], m);
            pad.fill(0x5c);
            for i in 0..N {
                pad[i] ^= sk_prf[i];
            }
            let outer_st = sha512::compress(&sha512::H0, &pad, 0);
            pad.fill(0);
            pad[..64].copy_from_slice(&inner);
            pad[64] = 0x80;
            pad[126..].copy_from_slice(&(((128 + 64) * 8) as u16).to_be_bytes());
            let mut out = [0u8; N];
            out.copy_from_slice(&sha512::digest(&sha512::compress(&outer_st, &pad, 0))[..N]);
            out
        };

        // Segmented H_msg
        let mut h_prefix = [0u8; 3 * 32 + 2 + 255];
        h_prefix[..N].copy_from_slice(&r);
        h_prefix[N..2 * N].copy_from_slice(pk_seed);
        h_prefix[2 * N..3 * N].copy_from_slice(pk_root);
        h_prefix[3 * N..3 * N + 2].copy_from_slice(&domain);
        let h_used = 3 * N + 2 + ctx.len();
        h_prefix[3 * N + 2..h_used].copy_from_slice(ctx);

        let mut seed_buf = Vec::with_capacity(2 * N + 64);
        seed_buf.extend_from_slice(&r);
        seed_buf.extend_from_slice(pk_seed);
        let digest = if N == 16 {
            let d = continued_sha256(sha256::H0, 0, &h_prefix[..h_used], m);
            seed_buf.extend_from_slice(&d);
            mgf1_sha256(&seed_buf, p.m)
        } else {
            let d = continued_sha512(sha512::H0, 0, &h_prefix[..h_used], m);
            seed_buf.extend_from_slice(&d);
            mgf1_sha512(&seed_buf, p.m)
        };
        (r, digest)
    }

    pub(super) fn internal_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        let r = prf_msg::<N>(sk_prf, addrnd, m);
        let digest = h_msg::<N>(p, &r, pk_seed, pk_root, m);
        (r, digest)
    }

    /// Computes all `2^(hp + 1) - 1` nodes of one XMSS tree at `(layer, tree_index)`.
    pub(super) fn build_xmss_tree<const N: usize>(
        hp: u32,
        layer: u32,
        tree_index: u64,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
    ) -> Vec<[u8; N]> {
        let seed = seed_ctx::<N>(pk_seed);
        let adrs = Adrs::new().with_layer(layer).with_tree(tree_index);
        let num_leaves = 1usize << hp;
        let total = tree_node_count(hp);
        let mut nodes = vec![[0u8; N]; total];

        // Compute all 2^hp WOTS+ leaf public keys.
        #[cfg(all(feature = "parallel", not(target_os = "none")))]
        let built_parallel = build_leaves_parallel(num_leaves, sk_seed, &seed, adrs, &mut nodes[..num_leaves]);
        #[cfg(not(all(feature = "parallel", not(target_os = "none"))))]
        let built_parallel = false;

        if !built_parallel {
            for i in 0..num_leaves {
                nodes[i] = wots_pk_gen::<N>(
                    sk_seed,
                    &seed,
                    adrs.with_type(WOTS_HASH).with_keypair(i as u32),
                );
            }
        }

        // Hash up internal Merkle levels 1..=hp.
        for z in 1..=hp {
            let prev = level_offset(hp, z - 1);
            let cur = level_offset(hp, z);
            let count = num_leaves >> z;
            for i in 0..count {
                let a = adrs.with_type(TREE).with_word2(z).with_word3(i as u32);
                nodes[cur + i] = hash2::<N>(&seed, &a, &nodes[prev + 2 * i], &nodes[prev + 2 * i + 1]);
            }
        }
        nodes
    }

    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    fn build_leaves_parallel<const N: usize>(
        num_leaves: usize,
        sk_seed: &[u8; N],
        seed: &Seed<N>,
        adrs: Adrs,
        leaves: &mut [[u8; N]],
    ) -> bool {
        use core::sync::atomic::{AtomicUsize, Ordering};

        if num_leaves < 16 {
            return false;
        }
        let workers = crate::pool::available_threads().min(num_leaves / 4);
        if workers < 2 {
            return false;
        }
        // Chunk into small contiguous slices so each worker writes disjoint memory cleanly.
        let chunk = (num_leaves / (workers * 4)).max(4);
        let num_chunks = (num_leaves + chunk - 1) / chunk;
        let slots: Vec<std::sync::OnceLock<Vec<[u8; N]>>> =
            (0..num_chunks).map(|_| std::sync::OnceLock::new()).collect();
        let next = AtomicUsize::new(0);
        let fill = || loop {
            let id = next.fetch_add(1, Ordering::Relaxed);
            let Some(slot) = slots.get(id) else { break };
            let start = id * chunk;
            let end = (start + chunk).min(num_leaves);
            let mut out = Vec::with_capacity(end - start);
            for i in start..end {
                out.push(wots_pk_gen::<N>(
                    sk_seed,
                    seed,
                    adrs.with_type(WOTS_HASH).with_keypair(i as u32),
                ));
            }
            let _ = slot.set(out);
        };

        crate::pool::execute(workers, true, &fill);

        for (id, slot) in slots.into_iter().enumerate() {
            let start = id * chunk;
            let batch = slot.into_inner().expect("all leaf chunks completed");
            leaves[start..start + batch.len()].copy_from_slice(&batch);
        }
        true
    }

    pub(super) fn sign_from_digest<const N: usize>(
        p: &Params,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        r: &[u8; N],
        digest: &[u8],
        top_tree: &[[u8; N]],
        layer_d2_hit: Option<&[[u8; N]]>,
    ) -> Vec<u8> {
        let idx_tree = digest_tree(p, digest);
        let idx_leaf = digest_leaf(p, digest);
        let fors_adrs = Adrs::new()
            .with_tree(idx_tree)
            .with_type(FORS_TREE)
            .with_keypair(idx_leaf);
        let seed = seed_ctx::<N>(pk_seed);
        let md = &digest[0..p.md_bytes()];

        #[cfg(all(feature = "parallel", not(target_os = "none")))]
        if let Some(sig) = sign_parallel(
            p,
            md,
            sk_seed,
            &seed,
            fors_adrs,
            r,
            idx_tree,
            idx_leaf,
            top_tree,
            layer_d2_hit,
        ) {
            return sig;
        }

        let sig_fors = fors_sign::<N>(p, md, sk_seed, &seed, fors_adrs);
        let mut root = fors_pk_from_sig::<N>(p, &sig_fors, md, &seed, fors_adrs);

        let mut sig = Vec::with_capacity(p.sig_bytes());
        sig.extend_from_slice(r);
        sig.extend_from_slice(&sig_fors);

        let mut tree = idx_tree;
        let mut leaf = idx_leaf;
        for j in 0..p.d {
            let adrs = Adrs::new().with_layer(j).with_tree(tree);
            if j == p.d - 1 {
                // Top XMSS layer: 100% cache hit! Only WOTS+ signature needed.
                let wots = wots_sign::<N>(
                    &root,
                    sk_seed,
                    &seed,
                    adrs.with_type(WOTS_HASH).with_keypair(leaf),
                );
                sig.extend_from_slice(&wots);
                append_auth_path(top_tree, p.hp, leaf, &mut sig);
            } else if j + 2 == p.d {
                if let Some(d2_tree) = layer_d2_hit {
                    // Layer d - 2 cache hit! Skip both auth path AND xmss_pk_from_sig.
                    let wots = wots_sign::<N>(
                        &root,
                        sk_seed,
                        &seed,
                        adrs.with_type(WOTS_HASH).with_keypair(leaf),
                    );
                    sig.extend_from_slice(&wots);
                    append_auth_path(d2_tree, p.hp, leaf, &mut sig);
                    root = tree_root(d2_tree);
                } else {
                    let s = xmss_sign::<N>(p, &root, sk_seed, leaf, &seed, adrs);
                    root = xmss_pk_from_sig::<N>(p, leaf, &s, &root, &seed, adrs);
                    sig.extend_from_slice(&s);
                }
            } else {
                let s = xmss_sign::<N>(p, &root, sk_seed, leaf, &seed, adrs);
                root = xmss_pk_from_sig::<N>(p, leaf, &s, &root, &seed, adrs);
                sig.extend_from_slice(&s);
            }
            leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
            tree >>= p.hp;
        }
        sig
    }

    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    #[allow(clippy::too_many_arguments)]
    fn sign_parallel<const N: usize>(
        p: &Params,
        md: &[u8],
        sk_seed: &[u8; N],
        seed: &Seed<N>,
        fors_adrs: Adrs,
        r: &[u8; N],
        mut tree: u64,
        mut leaf: u32,
        top_tree: &[[u8; N]],
        layer_d2_hit: Option<&[[u8; N]]>,
    ) -> Option<Vec<u8>> {
        use core::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::OnceLock;

        let cached_layers = if layer_d2_hit.is_some() && p.d >= 2 { 2 } else { 1 };
        let active_layers = (p.d as usize).saturating_sub(cached_layers);
        let workers = crate::pool::available_threads();
        if workers < 2 || p.hp == 0 {
            return None;
        }

        let mut layers = Vec::with_capacity(p.d as usize);
        for j in 0..p.d {
            layers.push((Adrs::new().with_layer(j).with_tree(tree), leaf));
            leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
            tree >>= p.hp;
        }

        let fors_indices = base_2b(md, p.a, p.k as usize);
        let fors_stride = p.a as usize + 1;
        let xmss_count = active_layers * p.hp as usize;
        let fors_total_nodes = p.k as usize * fors_stride;

        enum Job {
            /// One uncached XMSS auth-path node at `(layer_idx, height)`.
            Xmss { layer: usize, height: u32, slot: usize },
            /// One tall FORS auth-path node at `height`.
            ForsNode { height: u32, node_idx: u32, slot: usize },
            /// Secret leaf + small FORS auth-path nodes `0..small_end` for one FORS tree.
            ForsSmall { tree: u32, idx: u32, small_end: u32 },
        }

        // Build unified job list sorted largest-work-first (weight = approx hash calls).
        let mut weighted_jobs: Vec<(u64, Job)> = Vec::with_capacity(xmss_count + p.k as usize * 8);
        for j in 0..active_layers {
            for height in 0..p.hp {
                let slot = j * p.hp as usize + height as usize;
                let weight = (1u64 << height) * 512;
                weighted_jobs.push((weight, Job::Xmss { layer: j, height, slot }));
            }
        }
        let small_end = p.a.min(8);
        for (i, &idx) in fors_indices.iter().enumerate() {
            let t = i as u32;
            let small_weight = (1u64 << small_end) * 3;
            weighted_jobs.push((small_weight, Job::ForsSmall { tree: t, idx, small_end }));
            for h in small_end..p.a {
                let s = (idx >> h) ^ 1;
                let node_idx = (t << (p.a - h)) + s;
                let slot = i * fors_stride + 1 + h as usize;
                let weight = (1u64 << h) * 3;
                weighted_jobs.push((weight, Job::ForsNode { height: h, node_idx, slot }));
            }
        }
        weighted_jobs.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        let jobs: Vec<Job> = weighted_jobs.into_iter().map(|(_, j)| j).collect();

        let xmss_slots: Vec<OnceLock<[u8; N]>> = (0..xmss_count).map(|_| OnceLock::new()).collect();
        let fors_slots: Vec<OnceLock<[u8; N]>> =
            (0..fors_total_nodes).map(|_| OnceLock::new()).collect();

        let active_workers = workers.min(jobs.len().max(1));
        let next = AtomicUsize::new(0);
        let fill = || loop {
            let id = next.fetch_add(1, Ordering::Relaxed);
            let Some(job) = jobs.get(id) else { break };
            match *job {
                Job::Xmss { layer, height, slot } => {
                    let (addr, index) = layers[layer];
                    let val = xmss_node(sk_seed, (index >> height) ^ 1, height, seed, addr);
                    xmss_slots[slot].set(val).expect("unique XMSS slot");
                }
                Job::ForsNode { height, node_idx, slot } => {
                    let val = fors_node(sk_seed, node_idx, height, seed, fors_adrs);
                    fors_slots[slot].set(val).expect("unique FORS slot");
                }
                Job::ForsSmall { tree, idx, small_end } => {
                    let base = tree as usize * fors_stride;
                    let sk = fors_sk_gen(sk_seed, seed, fors_adrs, (tree << p.a) + idx);
                    fors_slots[base].set(sk).expect("unique FORS sk slot");
                    for h in 0..small_end {
                        let s = (idx >> h) ^ 1;
                        let val = fors_node(sk_seed, (tree << (p.a - h)) + s, h, seed, fors_adrs);
                        fors_slots[base + 1 + h as usize]
                            .set(val)
                            .expect("unique FORS small slot");
                    }
                }
            }
        };

        crate::pool::execute(active_workers, true, &fill);

        let mut sig = Vec::with_capacity(p.sig_bytes());
        sig.extend_from_slice(r);
        let fors_start = sig.len();
        for slot in &fors_slots {
            sig.extend_from_slice(slot.get().expect("all FORS jobs joined"));
        }
        let mut root = fors_pk_from_sig(p, &sig[fors_start..], md, seed, fors_adrs);

        for (j, &(addr, index)) in layers.iter().enumerate() {
            let start = sig.len();
            sig.extend(wots_sign(
                &root,
                sk_seed,
                seed,
                addr.with_type(WOTS_HASH).with_keypair(index),
            ));
            if j == p.d as usize - 1 {
                append_auth_path(top_tree, p.hp, index, &mut sig);
            } else if j + 2 == p.d as usize {
                if let Some(d2_tree) = layer_d2_hit {
                    append_auth_path(d2_tree, p.hp, index, &mut sig);
                    root = tree_root(d2_tree);
                    continue;
                }
                for height in 0..p.hp {
                    let slot = j * p.hp as usize + height as usize;
                    sig.extend_from_slice(xmss_slots[slot].get().expect("all XMSS jobs joined"));
                }
                root = xmss_pk_from_sig(p, index, &sig[start..], &root, seed, addr);
            } else {
                for height in 0..p.hp {
                    let slot = j * p.hp as usize + height as usize;
                    sig.extend_from_slice(xmss_slots[slot].get().expect("all XMSS jobs joined"));
                }
                if j + 1 < layers.len() {
                    root = xmss_pk_from_sig(p, index, &sig[start..], &root, seed, addr);
                }
            }
        }
        Some(sig)
    }
}

// ============================================================================
// SHAKE family helpers (using crate::shake256::{Sponge, parallel})
// ============================================================================

mod shake_ops {
    use super::*;
    use crate::address::{FORS_PRF, FORS_ROOTS, WOTS_PK, WOTS_PRF};
    use crate::params::{LEN2, W};
    use crate::shake256::Sponge;
    use crate::util::base_2b;
    use crate::wots::wots_digits;

    #[cfg(any(
        all(target_arch = "aarch64", target_endian = "little"),
        all(target_arch = "x86_64", target_feature = "sse2")
    ))]
    mod simd {
        use super::*;
        use crate::shake256::parallel::{self, States, WIDTH};

        #[inline(always)]
        pub(super) fn available<const N: usize>() -> bool {
            matches!(N, 16 | 24 | 32) && parallel::available()
        }

        #[inline(always)]
        fn word(input: &[u8], i: usize) -> u64 {
            u64::from_le_bytes(input[i * 8..i * 8 + 8].try_into().unwrap())
        }

        fn header<const N: usize>(seed: &[u8; N], addresses: &[Adrs; WIDTH], size: usize) -> States {
            let mut s = [[0u64; WIDTH]; 25];
            for i in 0..N / 8 {
                s[i] = [word(seed, i); WIDTH];
            }
            for lane in 0..WIDTH {
                let addr = addresses[lane].full();
                for j in 0..4 {
                    s[N / 8 + j][lane] = word(&addr, j);
                }
            }
            s[size / 8] = [0x1f; WIDTH];
            for v in &mut s[16] {
                *v |= 1 << 63;
            }
            s
        }

        fn put<const N: usize>(s: &mut States, offset: usize, values: &[[u8; N]; WIDTH]) {
            for i in 0..N / 8 {
                for lane in 0..WIDTH {
                    s[offset + i][lane] = word(&values[lane], i);
                }
            }
        }

        fn read<const N: usize>(s: &States) -> [[u8; N]; WIDTH] {
            let mut values = [[0u8; N]; WIDTH];
            for i in 0..N / 8 {
                for lane in 0..WIDTH {
                    values[lane][8 * i..8 * i + 8].copy_from_slice(&s[i][lane].to_le_bytes());
                }
            }
            values
        }

        fn short<const N: usize>(
            seed: &[u8; N],
            addresses: &[Adrs; WIDTH],
            values: &[[u8; N]; WIDTH],
        ) -> [[u8; N]; WIDTH] {
            let mut s = header(seed, addresses, 2 * N + 32);
            put(&mut s, N / 8 + 4, values);
            parallel::permute(&mut s);
            read(&s)
        }

        fn pair<const N: usize>(
            seed: &[u8; N],
            addresses: &[Adrs; WIDTH],
            left: &[[u8; N]; WIDTH],
            right: &[[u8; N]; WIDTH],
        ) -> [[u8; N]; WIDTH] {
            let mut s = header(seed, addresses, 3 * N + 32);
            put(&mut s, N / 8 + 4, left);
            put(&mut s, 2 * N / 8 + 4, right);
            parallel::permute(&mut s);
            read(&s)
        }

        fn secrets<const N: usize>(
            seed: &[u8; N],
            sk: &[u8; N],
            addr: Adrs,
            ids: [usize; WIDTH],
        ) -> [[u8; N]; WIDTH] {
            let prf = addr.with_type(WOTS_PRF).with_keypair(addr.keypair);
            let addresses = core::array::from_fn(|lane| prf.with_word2(ids[lane] as u32));
            short(seed, &addresses, &[*sk; WIDTH])
        }

        fn chains<const N: usize>(
            seed: &[u8; N],
            addr: Adrs,
            ids: [usize; WIDTH],
            values: &[[u8; N]; WIDTH],
            mut index: [u32; WIDTH],
            end: [u32; WIDTH],
        ) -> [[u8; N]; WIDTH] {
            let addresses =
                core::array::from_fn(|lane| addr.with_word2(ids[lane] as u32).with_word3(0));
            let mut input = header(seed, &addresses, 2 * N + 32);
            let offset = N / 8 + 4;
            put(&mut input, offset, values);
            while index != end {
                let mut output = input;
                for lane in 0..WIDTH {
                    output[offset - 1][lane] |= u64::from(index[lane].swap_bytes()) << 32;
                }
                parallel::permute(&mut output);
                for lane in 0..WIDTH {
                    if index[lane] < end[lane] {
                        for j in 0..N / 8 {
                            input[offset + j][lane] = output[j][lane];
                        }
                        index[lane] += 1;
                    }
                }
            }
            let mut result = [[0u8; N]; WIDTH];
            for j in 0..N / 8 {
                for lane in 0..WIDTH {
                    result[lane][8 * j..8 * j + 8]
                        .copy_from_slice(&input[offset + j][lane].to_le_bytes());
                }
            }
            result
        }

        /// Computes `WIDTH` full WOTS+ public keys simultaneously in lockstep — zero
        /// wasted SIMD lanes regardless of `len = 35, 51, 67`, fusing PRF + chains + WOTS_PK.
        pub(super) fn wots_pk_gen_batch<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            keys: [u32; WIDTH],
        ) -> [[u8; N]; WIDTH] {
            let addresses = |typ| keys.map(|key| addr.with_type(typ).with_keypair(key));
            let offset = N / 8 + 4;
            let mut pk = header(seed, &addresses(WOTS_PK), N + 32);
            pk[offset] = [0; WIDTH];
            pk[16] = [0; WIDTH];
            let mut pos = offset;
            let mut prf = header(seed, &addresses(WOTS_PRF), 2 * N + 32);
            put(&mut prf, offset, &[*sk; WIDTH]);
            let mut input = header(seed, &addresses(WOTS_HASH), 2 * N + 32);
            for chain in 0..2 * N + LEN2 {
                let id = u64::from((chain as u32).swap_bytes());
                prf[offset - 1] = [id; WIDTH];
                let mut state = prf;
                parallel::permute(&mut state);
                for step in 0..W - 1 {
                    input[offset - 1] = [id | (u64::from(step.swap_bytes()) << 32); WIDTH];
                    input[offset..offset + N / 8].copy_from_slice(&state[..N / 8]);
                    state = input;
                    parallel::permute(&mut state);
                }
                for word in &state[..N / 8] {
                    for lane in 0..WIDTH {
                        pk[pos][lane] ^= word[lane];
                    }
                    pos += 1;
                    if pos == 17 {
                        parallel::permute(&mut pk);
                        pos = 0;
                    }
                }
            }
            for lane in 0..WIDTH {
                pk[pos][lane] ^= 0x1f;
                pk[16][lane] ^= 1 << 63;
            }
            parallel::permute(&mut pk);
            read::<N>(&pk)
        }

        /// Computes a range of XMSS leaf WOTS+ public keys `[start..end]` batched `WIDTH` at a time.
        pub(super) fn fill_xmss_leaves<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            start: usize,
            out: &mut [[u8; N]],
        ) {
            let len = out.len();
            let mut off = 0;
            while off < len {
                let active = (len - off).min(WIDTH);
                let keys = core::array::from_fn(|lane| (start + off + lane.min(active - 1)) as u32);
                let batch = wots_pk_gen_batch(sk, seed, addr, keys);
                out[off..off + active].copy_from_slice(&batch[..active]);
                off += active;
            }
        }

        /// Computes one XMSS internal node at height `z`, index `i` using `WIDTH`-batched leaves
        /// and batched parent hashing.
        pub(super) fn xmss_node<const N: usize>(
            sk: &[u8; N],
            i: u32,
            z: u32,
            seed: &[u8; N],
            addr: Adrs,
        ) -> [u8; N] {
            if z == 0 {
                return wots_pk_gen_single(sk, seed, addr.with_type(WOTS_HASH).with_keypair(i));
            }
            let num_leaves = 1usize << z;
            if num_leaves <= 512 {
                let base = (i as usize) << z;
                let mut cur = vec![[0u8; N]; num_leaves];
                fill_xmss_leaves(sk, seed, addr, base, &mut cur);
                for h in 1..=z {
                    let count = num_leaves >> h;
                    let level_base = (i as usize) << (z - h);
                    let mut next = vec![[0u8; N]; count];
                    hash_pairs(seed, addr, h, level_base, &cur, &mut next);
                    cur = next;
                }
                return cur[0];
            }
            let l = xmss_node(sk, 2 * i, z - 1, seed, addr);
            let r = xmss_node(sk, 2 * i + 1, z - 1, seed, addr);
            let a = addr.with_type(TREE).with_word2(z).with_word3(i);
            super::thash_pair(seed, &a, &l, &r)
        }

        /// Batches parent node hashing at height `h`, starting at tree index `base_index`.
        pub(super) fn hash_pairs<const N: usize>(
            seed: &[u8; N],
            addr: Adrs,
            height: u32,
            base_index: usize,
            children: &[[u8; N]],
            parents: &mut [[u8; N]],
        ) {
            let count = parents.len();
            let mut off = 0;
            while off < count {
                let active = (count - off).min(WIDTH);
                let ids: [usize; WIDTH] =
                    core::array::from_fn(|lane| off + lane.min(active - 1));
                let addresses = ids.map(|k| {
                    addr.with_type(TREE)
                        .with_word2(height)
                        .with_word3((base_index + k) as u32)
                });
                let left = ids.map(|k| children[2 * k]);
                let right = ids.map(|k| children[2 * k + 1]);
                let batch = pair(seed, &addresses, &left, &right);
                parents[off..off + active].copy_from_slice(&batch[..active]);
                off += active;
            }
        }

        pub(super) fn wots_pk_gen_single<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
        ) -> [u8; N] {
            let len = 2 * N + LEN2;
            let mut pk = super::start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
            for i in (0..len).step_by(WIDTH) {
                let ids = core::array::from_fn(|lane| i + lane);
                let values = secrets(seed, sk, addr, ids);
                let values = chains(seed, addr, ids, &values, [0; WIDTH], [W - 1; WIDTH]);
                for v in &values[..(len - i).min(WIDTH)] {
                    pk.absorb(v);
                }
            }
            super::digest(pk)
        }

        fn chain_order(digits: &[u32]) -> [usize; 67] {
            let mut offsets = [0usize; 16];
            for &digit in digits {
                offsets[digit as usize] += 1;
            }
            let mut start = 0;
            for offset in &mut offsets {
                let count = *offset;
                *offset = start;
                start += count;
            }
            let mut order = [0usize; 67];
            for (index, &digit) in digits.iter().enumerate() {
                let at = &mut offsets[digit as usize];
                order[*at] = index;
                *at += 1;
            }
            order
        }

        pub(super) fn wots_sign<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            digits: &[u32],
        ) -> Vec<u8> {
            let order = chain_order(digits);
            let mut sig = vec![0u8; N * digits.len()];
            for batch in order[..digits.len()].chunks(WIDTH) {
                let ids = core::array::from_fn(|i| batch[i.min(batch.len() - 1)]);
                let values = secrets(seed, sk, addr, ids);
                let values = chains(seed, addr, ids, &values, [0; WIDTH], ids.map(|i| digits[i]));
                for (lane, &id) in batch.iter().enumerate() {
                    sig[id * N..(id + 1) * N].copy_from_slice(&values[lane]);
                }
            }
            sig
        }

        pub(super) fn wots_pk_from_sig<const N: usize>(
            sig: &[u8],
            seed: &[u8; N],
            addr: Adrs,
            digits: &[u32],
        ) -> [u8; N] {
            let order = chain_order(digits);
            let mut endpoints = [[0u8; N]; 67];
            for batch in order[..digits.len()].chunks(WIDTH) {
                let ids = core::array::from_fn(|i| batch[i.min(batch.len() - 1)]);
                let values = ids.map(|i| block(sig, i));
                let values = chains(
                    seed,
                    addr,
                    ids,
                    &values,
                    ids.map(|i| digits[i]),
                    [W - 1; WIDTH],
                );
                for (lane, &id) in batch.iter().enumerate() {
                    endpoints[id] = values[lane];
                }
            }
            let mut pk = super::start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
            for key in &endpoints[..digits.len()] {
                pk.absorb(key);
            }
            super::digest(pk)
        }

        fn fors_secrets<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            indices: [u32; WIDTH],
        ) -> [[u8; N]; WIDTH] {
            let prf = addr.with_type(FORS_PRF).with_keypair(addr.keypair);
            short(seed, &indices.map(|i| prf.with_word3(i)), &[*sk; WIDTH])
        }

        fn fors_nodes<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            indices: [u32; WIDTH],
            level: u32,
        ) -> [[u8; N]; WIDTH] {
            let addresses = indices.map(|i| addr.with_word2(level).with_word3(i));
            if level == 0 {
                short(seed, &addresses, &fors_secrets(sk, seed, addr, indices))
            } else {
                let left = fors_nodes(sk, seed, addr, indices.map(|i| i * 2), level - 1);
                let right = fors_nodes(sk, seed, addr, indices.map(|i| i * 2 + 1), level - 1);
                pair(seed, &addresses, &left, &right)
            }
        }

        pub(super) fn fors_sign<const N: usize>(
            p: &Params,
            selections: &[u32],
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
        ) -> Vec<u8> {
            let stride = (p.a as usize + 1) * N;
            let mut sig = vec![0u8; selections.len() * stride];
            for first in (0..selections.len()).step_by(WIDTH) {
                let active = (selections.len() - first).min(WIDTH);
                let indices = core::array::from_fn(|lane| {
                    let tree = first + lane.min(active - 1);
                    ((tree as u32) << p.a) + selections[tree]
                });
                let secret = fors_secrets(sk, seed, addr, indices);
                for lane in 0..active {
                    sig[(first + lane) * stride..(first + lane) * stride + N]
                        .copy_from_slice(&secret[lane]);
                }
                for j in 0..p.a {
                    let siblings = fors_nodes(sk, seed, addr, indices.map(|i| (i >> j) ^ 1), j);
                    for lane in 0..active {
                        let pos = (first + lane) * stride + (j as usize + 1) * N;
                        sig[pos..pos + N].copy_from_slice(&siblings[lane]);
                    }
                }
            }
            sig
        }

        /// Computes one FORS height `j` across a SIMD group of up to `WIDTH` trees starting at `first`.
        #[cfg(all(feature = "parallel", not(target_os = "none")))]
        pub(super) fn fors_group_level<const N: usize>(
            p: &Params,
            selections: &[u32],
            first: usize,
            active: usize,
            j: u32,
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
        ) -> [[u8; N]; WIDTH] {
            let indices = core::array::from_fn(|lane| {
                let tree = first + lane.min(active - 1);
                ((tree as u32) << p.a) + selections[tree]
            });
            fors_nodes(sk, seed, addr, indices.map(|i| (i >> j) ^ 1), j)
        }

        /// Computes FORS secret leaves across a SIMD group of up to `WIDTH` trees starting at `first`.
        #[cfg(all(feature = "parallel", not(target_os = "none")))]
        pub(super) fn fors_group_secrets<const N: usize>(
            p: &Params,
            selections: &[u32],
            first: usize,
            active: usize,
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
        ) -> [[u8; N]; WIDTH] {
            let indices = core::array::from_fn(|lane| {
                let tree = first + lane.min(active - 1);
                ((tree as u32) << p.a) + selections[tree]
            });
            fors_secrets(sk, seed, addr, indices)
        }

        pub(super) fn fors_pk_from_sig<const N: usize>(
            p: &Params,
            selections: &[u32],
            sig: &[u8],
            seed: &[u8; N],
            addr: Adrs,
        ) -> [u8; N] {
            let stride = p.a as usize + 1;
            let mut pk = super::start(seed, &addr.with_type(FORS_ROOTS).with_keypair(addr.keypair));
            for first in (0..selections.len()).step_by(WIDTH) {
                let active = (selections.len() - first).min(WIDTH);
                let trees: [usize; WIDTH] =
                    core::array::from_fn(|lane| first + lane.min(active - 1));
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
            super::digest(pk)
        }
    }

    #[inline]
    fn start<const N: usize>(seed: &[u8; N], adrs: &Adrs) -> Sponge {
        let mut sponge = Sponge::new();
        sponge.absorb(seed);
        sponge.absorb(&adrs.full());
        sponge
    }

    #[inline]
    fn digest<const N: usize>(sponge: Sponge) -> [u8; N] {
        let mut out = [0u8; N];
        sponge.finish(&mut out);
        out
    }

    #[inline]
    fn thash<const N: usize>(seed: &[u8; N], adrs: &Adrs, value: &[u8; N]) -> [u8; N] {
        let mut sponge = start(seed, adrs);
        sponge.absorb(value);
        digest(sponge)
    }

    #[inline]
    fn thash_pair<const N: usize>(
        seed: &[u8; N],
        adrs: &Adrs,
        a: &[u8; N],
        b: &[u8; N],
    ) -> [u8; N] {
        let mut sponge = start(seed, adrs);
        sponge.absorb(a);
        sponge.absorb(b);
        digest(sponge)
    }

    /// Zero-copy `PRF_msg` + `H_msg` for pure signing (`M' = 0x00 || |ctx| || ctx || M`).
    pub(super) fn pure_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        ctx: &[u8],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        let domain = [0u8, ctx.len() as u8];
        let mut prf = Sponge::new();
        prf.absorb(sk_prf);
        prf.absorb(addrnd);
        prf.absorb(&domain);
        prf.absorb(ctx);
        prf.absorb(m);
        let r = digest::<N>(prf);

        let mut h = Sponge::new();
        h.absorb(&r);
        h.absorb(pk_seed);
        h.absorb(pk_root);
        h.absorb(&domain);
        h.absorb(ctx);
        h.absorb(m);
        let mut d = vec![0u8; p.m];
        h.finish(&mut d);
        (r, d)
    }

    pub(super) fn internal_digest<const N: usize>(
        p: &Params,
        sk_prf: &[u8; N],
        pk_seed: &[u8; N],
        pk_root: &[u8; N],
        addrnd: &[u8; N],
        m: &[u8],
    ) -> ([u8; N], Vec<u8>) {
        let mut prf = Sponge::new();
        prf.absorb(sk_prf);
        prf.absorb(addrnd);
        prf.absorb(m);
        let r = digest::<N>(prf);

        let mut h = Sponge::new();
        h.absorb(&r);
        h.absorb(pk_seed);
        h.absorb(pk_root);
        h.absorb(m);
        let mut d = vec![0u8; p.m];
        h.finish(&mut d);
        (r, d)
    }

    fn wots_secret<const N: usize>(sk: &[u8; N], seed: &[u8; N], adrs: Adrs, i: usize) -> [u8; N] {
        let a = adrs
            .with_type(WOTS_PRF)
            .with_keypair(adrs.keypair)
            .with_word2(i as u32);
        thash(seed, &a, sk)
    }

    fn wots_chain<const N: usize>(
        mut value: [u8; N],
        seed: &[u8; N],
        adrs: Adrs,
        mut j: u32,
        end: u32,
    ) -> [u8; N] {
        while j < end {
            value = thash(seed, &adrs.with_word3(j), &value);
            j += 1;
        }
        value
    }

    fn wots_pk_gen_portable<const N: usize>(sk: &[u8; N], seed: &[u8; N], adrs: Adrs) -> [u8; N] {
        let mut pk = start(seed, &adrs.with_type(WOTS_PK).with_keypair(adrs.keypair));
        for i in 0..2 * N + LEN2 {
            let end = wots_chain(
                wots_secret(sk, seed, adrs, i),
                seed,
                adrs.with_word2(i as u32),
                0,
                W - 1,
            );
            pk.absorb(&end);
        }
        digest(pk)
    }

    fn wots_sign<const N: usize>(
        msg: &[u8; N],
        sk: &[u8; N],
        seed: &[u8; N],
        adrs: Adrs,
    ) -> Vec<u8> {
        let digits = wots_digits(msg);
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if simd::available::<N>() {
            return simd::wots_sign(sk, seed, adrs, &digits);
        }
        let mut sig = Vec::with_capacity(digits.len() * N);
        for (i, &d) in digits.iter().enumerate() {
            let v = wots_chain(
                wots_secret(sk, seed, adrs, i),
                seed,
                adrs.with_word2(i as u32),
                0,
                d,
            );
            sig.extend_from_slice(&v);
        }
        sig
    }

    fn wots_pk_from_sig<const N: usize>(
        sig: &[u8],
        msg: &[u8; N],
        seed: &[u8; N],
        adrs: Adrs,
    ) -> [u8; N] {
        let digits = wots_digits(msg);
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if simd::available::<N>() {
            return simd::wots_pk_from_sig(sig, seed, adrs, &digits);
        }
        let mut pk = start(seed, &adrs.with_type(WOTS_PK).with_keypair(adrs.keypair));
        for (i, &d) in digits.iter().enumerate() {
            let end = wots_chain(
                block::<N>(sig, i),
                seed,
                adrs.with_word2(i as u32),
                d,
                W - 1,
            );
            pk.absorb(&end);
        }
        digest(pk)
    }

    fn climb<const N: usize>(
        mut node: [u8; N],
        mut index: u32,
        auth: &[u8],
        first: usize,
        height: u32,
        seed: &[u8; N],
        adrs: Adrs,
    ) -> [u8; N] {
        for k in 0..height {
            let sibling = block::<N>(auth, first + k as usize);
            let parent = index >> 1;
            let a = adrs.with_word2(k + 1).with_word3(parent);
            node = if index & 1 == 0 {
                thash_pair(seed, &a, &node, &sibling)
            } else {
                thash_pair(seed, &a, &sibling, &node)
            };
            index = parent;
        }
        node
    }

    fn xmss_node<const N: usize>(
        sk: &[u8; N],
        i: u32,
        z: u32,
        seed: &[u8; N],
        adrs: Adrs,
    ) -> [u8; N] {
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if simd::available::<N>() {
            return simd::xmss_node(sk, i, z, seed, adrs);
        }
        if z == 0 {
            wots_pk_gen_portable(sk, seed, adrs.with_type(WOTS_HASH).with_keypair(i))
        } else {
            let l = xmss_node(sk, 2 * i, z - 1, seed, adrs);
            let r = xmss_node(sk, 2 * i + 1, z - 1, seed, adrs);
            let a = adrs.with_type(TREE).with_word2(z).with_word3(i);
            thash_pair(seed, &a, &l, &r)
        }
    }

    fn xmss_sign<const N: usize>(
        p: &Params,
        m: &[u8; N],
        sk: &[u8; N],
        idx: u32,
        seed: &[u8; N],
        adrs: Adrs,
    ) -> Vec<u8> {
        let mut sig = wots_sign(m, sk, seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
        for j in 0..p.hp {
            let k = (idx >> j) ^ 1;
            let node = xmss_node(sk, k, j, seed, adrs);
            sig.extend_from_slice(&node);
        }
        sig
    }

    fn xmss_pk_from_sig<const N: usize>(
        p: &Params,
        idx: u32,
        sig: &[u8],
        m: &[u8; N],
        seed: &[u8; N],
        adrs: Adrs,
    ) -> [u8; N] {
        let node = wots_pk_from_sig(sig, m, seed, adrs.with_type(WOTS_HASH).with_keypair(idx));
        climb(node, idx, sig, 2 * N + LEN2, p.hp, seed, adrs.with_type(TREE))
    }

    fn fors_sk_gen<const N: usize>(sk: &[u8; N], seed: &[u8; N], adrs: Adrs, idx: u32) -> [u8; N] {
        let a = adrs
            .with_type(FORS_PRF)
            .with_keypair(adrs.keypair)
            .with_word3(idx);
        thash(seed, &a, sk)
    }

    fn fors_node_portable<const N: usize>(
        sk: &[u8; N],
        i: u32,
        z: u32,
        seed: &[u8; N],
        adrs: Adrs,
    ) -> [u8; N] {
        let a = adrs.with_word2(z).with_word3(i);
        if z == 0 {
            thash(seed, &a, &fors_sk_gen(sk, seed, adrs, i))
        } else {
            let left = fors_node_portable(sk, 2 * i, z - 1, seed, adrs);
            let right = fors_node_portable(sk, 2 * i + 1, z - 1, seed, adrs);
            thash_pair(seed, &a, &left, &right)
        }
    }

    fn fors_sign<const N: usize>(
        p: &Params,
        md: &[u8],
        sk: &[u8; N],
        seed: &[u8; N],
        adrs: Adrs,
    ) -> Vec<u8> {
        let indices = base_2b(md, p.a, p.k as usize);
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if simd::available::<N>() {
            return simd::fors_sign(p, &indices, sk, seed, adrs);
        }
        let mut sig = Vec::with_capacity(p.fors_sig_bytes());
        for (i, &idx) in indices.iter().enumerate() {
            let tree = i as u32;
            sig.extend_from_slice(&fors_sk_gen(sk, seed, adrs, (tree << p.a) + idx));
            for j in 0..p.a {
                let s = (idx >> j) ^ 1;
                let node = fors_node_portable(sk, (tree << (p.a - j)) + s, j, seed, adrs);
                sig.extend_from_slice(&node);
            }
        }
        sig
    }

    fn fors_pk_from_sig<const N: usize>(
        p: &Params,
        sig: &[u8],
        md: &[u8],
        seed: &[u8; N],
        adrs: Adrs,
    ) -> [u8; N] {
        let indices = base_2b(md, p.a, p.k as usize);
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if simd::available::<N>() {
            return simd::fors_pk_from_sig(p, &indices, sig, seed, adrs);
        }
        let mut roots = start(seed, &adrs.with_type(FORS_ROOTS).with_keypair(adrs.keypair));
        for (i, &sel) in indices.iter().enumerate() {
            let offset = i * (1 + p.a as usize);
            let idx = ((i as u32) << p.a) + sel;
            let value = thash(
                seed,
                &adrs.with_word2(0).with_word3(idx),
                &block::<N>(sig, offset),
            );
            let root = climb(value, idx, sig, offset + 1, p.a, seed, adrs);
            roots.absorb(&root);
        }
        digest(roots)
    }

    fn fill_leaves_chunk<const N: usize>(
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        adrs: Adrs,
        start: usize,
        out: &mut [[u8; N]],
    ) {
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if simd::available::<N>() {
            simd::fill_xmss_leaves(sk_seed, pk_seed, adrs, start, out);
            return;
        }
        for (k, slot) in out.iter_mut().enumerate() {
            *slot = wots_pk_gen_portable(
                sk_seed,
                pk_seed,
                adrs.with_type(WOTS_HASH).with_keypair((start + k) as u32),
            );
        }
    }

    /// Computes all `2^(hp + 1) - 1` nodes of one SHAKE XMSS tree at `(layer, tree_index)`.
    pub(super) fn build_xmss_tree<const N: usize>(
        hp: u32,
        layer: u32,
        tree_index: u64,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
    ) -> Vec<[u8; N]> {
        let adrs = Adrs::new().with_layer(layer).with_tree(tree_index);
        let num_leaves = 1usize << hp;
        let total = tree_node_count(hp);
        let mut nodes = vec![[0u8; N]; total];

        #[cfg(all(feature = "parallel", not(target_os = "none")))]
        let built_parallel = build_leaves_parallel(num_leaves, sk_seed, pk_seed, adrs, &mut nodes[..num_leaves]);
        #[cfg(not(all(feature = "parallel", not(target_os = "none"))))]
        let built_parallel = false;

        if !built_parallel {
            fill_leaves_chunk(sk_seed, pk_seed, adrs, 0, &mut nodes[..num_leaves]);
        }

        for z in 1..=hp {
            let prev = level_offset(hp, z - 1);
            let cur = level_offset(hp, z);
            let count = num_leaves >> z;
            let (children_slice, parents_slice) = nodes.split_at_mut(cur);
            let children = &children_slice[prev..prev + 2 * count];
            let parents = &mut parents_slice[..count];

            #[cfg(any(
                all(target_arch = "aarch64", target_endian = "little"),
                all(target_arch = "x86_64", target_feature = "sse2")
            ))]
            if simd::available::<N>() {
                simd::hash_pairs(pk_seed, adrs, z, 0, children, parents);
                continue;
            }
            for i in 0..count {
                let a = adrs.with_type(TREE).with_word2(z).with_word3(i as u32);
                parents[i] = thash_pair(pk_seed, &a, &children[2 * i], &children[2 * i + 1]);
            }
        }
        nodes
    }

    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    fn build_leaves_parallel<const N: usize>(
        num_leaves: usize,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        adrs: Adrs,
        leaves: &mut [[u8; N]],
    ) -> bool {
        use core::sync::atomic::{AtomicUsize, Ordering};

        if num_leaves < 16 {
            return false;
        }
        let workers = crate::pool::available_threads().min(num_leaves / 4);
        if workers < 2 {
            return false;
        }
        let chunk = (num_leaves / (workers * 4)).max(4);
        let num_chunks = (num_leaves + chunk - 1) / chunk;
        let slots: Vec<std::sync::OnceLock<Vec<[u8; N]>>> =
            (0..num_chunks).map(|_| std::sync::OnceLock::new()).collect();
        let next = AtomicUsize::new(0);
        let fill = || loop {
            let id = next.fetch_add(1, Ordering::Relaxed);
            let Some(slot) = slots.get(id) else { break };
            let start = id * chunk;
            let end = (start + chunk).min(num_leaves);
            let mut out = vec![[0u8; N]; end - start];
            fill_leaves_chunk(sk_seed, pk_seed, adrs, start, &mut out);
            let _ = slot.set(out);
        };

        crate::pool::execute(workers, true, &fill);

        for (id, slot) in slots.into_iter().enumerate() {
            let start = id * chunk;
            let batch = slot.into_inner().expect("all leaf chunks completed");
            leaves[start..start + batch.len()].copy_from_slice(&batch);
        }
        true
    }

    pub(super) fn sign_from_digest<const N: usize>(
        p: &Params,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        r: &[u8; N],
        digest: &[u8],
        top_tree: &[[u8; N]],
        layer_d2_hit: Option<&[[u8; N]]>,
    ) -> Vec<u8> {
        let idx_tree = digest_tree(p, digest);
        let idx_leaf = digest_leaf(p, digest);
        let fors_adrs = Adrs::new()
            .with_tree(idx_tree)
            .with_type(FORS_TREE)
            .with_keypair(idx_leaf);
        let md = &digest[0..p.md_bytes()];

        #[cfg(all(feature = "parallel", not(target_os = "none")))]
        if let Some(sig) = sign_parallel(
            p,
            md,
            sk_seed,
            pk_seed,
            fors_adrs,
            r,
            idx_tree,
            idx_leaf,
            top_tree,
            layer_d2_hit,
        ) {
            return sig;
        }

        let sig_fors = fors_sign::<N>(p, md, sk_seed, pk_seed, fors_adrs);
        let mut root = fors_pk_from_sig::<N>(p, &sig_fors, md, pk_seed, fors_adrs);

        let mut sig = Vec::with_capacity(p.sig_bytes());
        sig.extend_from_slice(r);
        sig.extend_from_slice(&sig_fors);

        let mut tree = idx_tree;
        let mut leaf = idx_leaf;
        for j in 0..p.d {
            let adrs = Adrs::new().with_layer(j).with_tree(tree);
            if j == p.d - 1 {
                let wots = wots_sign::<N>(
                    &root,
                    sk_seed,
                    pk_seed,
                    adrs.with_type(WOTS_HASH).with_keypair(leaf),
                );
                sig.extend_from_slice(&wots);
                append_auth_path(top_tree, p.hp, leaf, &mut sig);
            } else if j + 2 == p.d {
                if let Some(d2_tree) = layer_d2_hit {
                    let wots = wots_sign::<N>(
                        &root,
                        sk_seed,
                        pk_seed,
                        adrs.with_type(WOTS_HASH).with_keypair(leaf),
                    );
                    sig.extend_from_slice(&wots);
                    append_auth_path(d2_tree, p.hp, leaf, &mut sig);
                    root = tree_root(d2_tree);
                } else {
                    let s = xmss_sign::<N>(p, &root, sk_seed, leaf, pk_seed, adrs);
                    root = xmss_pk_from_sig::<N>(p, leaf, &s, &root, pk_seed, adrs);
                    sig.extend_from_slice(&s);
                }
            } else {
                let s = xmss_sign::<N>(p, &root, sk_seed, leaf, pk_seed, adrs);
                root = xmss_pk_from_sig::<N>(p, leaf, &s, &root, pk_seed, adrs);
                sig.extend_from_slice(&s);
            }
            leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
            tree >>= p.hp;
        }
        sig
    }

    #[cfg(all(feature = "parallel", not(target_os = "none")))]
    #[allow(clippy::too_many_arguments)]
    fn sign_parallel<const N: usize>(
        p: &Params,
        md: &[u8],
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        fors_adrs: Adrs,
        r: &[u8; N],
        mut tree: u64,
        mut leaf: u32,
        top_tree: &[[u8; N]],
        layer_d2_hit: Option<&[[u8; N]]>,
    ) -> Option<Vec<u8>> {
        use core::sync::atomic::{AtomicUsize, Ordering};
        use std::sync::OnceLock;

        let cached_layers = if layer_d2_hit.is_some() && p.d >= 2 { 2 } else { 1 };
        let active_layers = (p.d as usize).saturating_sub(cached_layers);
        let workers = crate::pool::available_threads();
        if workers < 2 || p.hp == 0 {
            return None;
        }

        let mut layers = Vec::with_capacity(p.d as usize);
        for j in 0..p.d {
            layers.push((Adrs::new().with_layer(j).with_tree(tree), leaf));
            leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
            tree >>= p.hp;
        }

        let fors_indices = base_2b(md, p.a, p.k as usize);
        let fors_stride = p.a as usize + 1;
        let xmss_count = active_layers * p.hp as usize;
        let fors_total_nodes = p.k as usize * fors_stride;

        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        let group_w = if simd::available::<N>() {
            crate::shake256::parallel::WIDTH
        } else {
            1
        };
        #[cfg(not(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        )))]
        let group_w = 1usize;

        enum Job {
            Xmss { layer: usize, height: u32, slot: usize },
            ForsGroupLevel { first: usize, active: usize, height: u32 },
            ForsGroupSmall { first: usize, active: usize, small_end: u32 },
        }

        let mut weighted_jobs: Vec<(u64, Job)> = Vec::with_capacity(xmss_count + p.k as usize * 8);
        for j in 0..active_layers {
            for height in 0..p.hp {
                let slot = j * p.hp as usize + height as usize;
                let weight = (1u64 << height) * 512;
                weighted_jobs.push((weight, Job::Xmss { layer: j, height, slot }));
            }
        }
        let small_end = p.a.min(7);
        for first in (0..p.k as usize).step_by(group_w) {
            let active = (p.k as usize - first).min(group_w);
            let small_weight = (1u64 << small_end) * 3;
            weighted_jobs.push((
                small_weight,
                Job::ForsGroupSmall {
                    first,
                    active,
                    small_end,
                },
            ));
            for h in small_end..p.a {
                let weight = (1u64 << h) * 3;
                weighted_jobs.push((
                    weight,
                    Job::ForsGroupLevel {
                        first,
                        active,
                        height: h,
                    },
                ));
            }
        }
        weighted_jobs.sort_unstable_by(|a, b| b.0.cmp(&a.0));
        let jobs: Vec<Job> = weighted_jobs.into_iter().map(|(_, j)| j).collect();

        let xmss_slots: Vec<OnceLock<[u8; N]>> = (0..xmss_count).map(|_| OnceLock::new()).collect();
        let fors_slots: Vec<OnceLock<[u8; N]>> =
            (0..fors_total_nodes).map(|_| OnceLock::new()).collect();

        let active_workers = workers.min(jobs.len().max(1));
        let next = AtomicUsize::new(0);
        let fill = || loop {
            let id = next.fetch_add(1, Ordering::Relaxed);
            let Some(job) = jobs.get(id) else { break };
            match *job {
                Job::Xmss { layer, height, slot } => {
                    let (addr, index) = layers[layer];
                    let val = xmss_node(sk_seed, (index >> height) ^ 1, height, pk_seed, addr);
                    xmss_slots[slot].set(val).expect("unique XMSS slot");
                }
                Job::ForsGroupLevel { first, active, height } => {
                    #[cfg(any(
                        all(target_arch = "aarch64", target_endian = "little"),
                        all(target_arch = "x86_64", target_feature = "sse2")
                    ))]
                    if simd::available::<N>() {
                        let vals = simd::fors_group_level(
                            p,
                            &fors_indices,
                            first,
                            active,
                            height,
                            sk_seed,
                            pk_seed,
                            fors_adrs,
                        );
                        for lane in 0..active {
                            let slot = (first + lane) * fors_stride + 1 + height as usize;
                            fors_slots[slot].set(vals[lane]).expect("unique FORS slot");
                        }
                        continue;
                    }
                    for lane in 0..active {
                        let t = (first + lane) as u32;
                        let idx = fors_indices[first + lane];
                        let s = (idx >> height) ^ 1;
                        let val = fors_node_portable(
                            sk_seed,
                            (t << (p.a - height)) + s,
                            height,
                            pk_seed,
                            fors_adrs,
                        );
                        let slot = (first + lane) * fors_stride + 1 + height as usize;
                        fors_slots[slot].set(val).expect("unique FORS slot");
                    }
                }
                Job::ForsGroupSmall { first, active, small_end } => {
                    #[cfg(any(
                        all(target_arch = "aarch64", target_endian = "little"),
                        all(target_arch = "x86_64", target_feature = "sse2")
                    ))]
                    if simd::available::<N>() {
                        let secs = simd::fors_group_secrets(
                            p,
                            &fors_indices,
                            first,
                            active,
                            sk_seed,
                            pk_seed,
                            fors_adrs,
                        );
                        for lane in 0..active {
                            fors_slots[(first + lane) * fors_stride]
                                .set(secs[lane])
                                .expect("unique FORS sk slot");
                        }
                        for h in 0..small_end {
                            let vals = simd::fors_group_level(
                                p,
                                &fors_indices,
                                first,
                                active,
                                h,
                                sk_seed,
                                pk_seed,
                                fors_adrs,
                            );
                            for lane in 0..active {
                                let slot = (first + lane) * fors_stride + 1 + h as usize;
                                fors_slots[slot].set(vals[lane]).expect("unique FORS small slot");
                            }
                        }
                        continue;
                    }
                    for lane in 0..active {
                        let t = (first + lane) as u32;
                        let idx = fors_indices[first + lane];
                        let base = (first + lane) * fors_stride;
                        let sk = fors_sk_gen(sk_seed, pk_seed, fors_adrs, (t << p.a) + idx);
                        fors_slots[base].set(sk).expect("unique FORS sk slot");
                        for h in 0..small_end {
                            let s = (idx >> h) ^ 1;
                            let val = fors_node_portable(
                                sk_seed,
                                (t << (p.a - h)) + s,
                                h,
                                pk_seed,
                                fors_adrs,
                            );
                            fors_slots[base + 1 + h as usize]
                                .set(val)
                                .expect("unique FORS small slot");
                        }
                    }
                }
            }
        };

        crate::pool::execute(active_workers, true, &fill);

        let mut sig = Vec::with_capacity(p.sig_bytes());
        sig.extend_from_slice(r);
        let fors_start = sig.len();
        for slot in &fors_slots {
            sig.extend_from_slice(slot.get().expect("all FORS jobs joined"));
        }
        let mut root = fors_pk_from_sig(p, &sig[fors_start..], md, pk_seed, fors_adrs);

        for (j, &(addr, index)) in layers.iter().enumerate() {
            let start = sig.len();
            sig.extend(wots_sign(
                &root,
                sk_seed,
                pk_seed,
                addr.with_type(WOTS_HASH).with_keypair(index),
            ));
            if j == p.d as usize - 1 {
                append_auth_path(top_tree, p.hp, index, &mut sig);
            } else if j + 2 == p.d as usize {
                if let Some(d2_tree) = layer_d2_hit {
                    append_auth_path(d2_tree, p.hp, index, &mut sig);
                    root = tree_root(d2_tree);
                    continue;
                }
                for height in 0..p.hp {
                    let slot = j * p.hp as usize + height as usize;
                    sig.extend_from_slice(xmss_slots[slot].get().expect("all XMSS jobs joined"));
                }
                root = xmss_pk_from_sig(p, index, &sig[start..], &root, pk_seed, addr);
            } else {
                for height in 0..p.hp {
                    let slot = j * p.hp as usize + height as usize;
                    sig.extend_from_slice(xmss_slots[slot].get().expect("all XMSS jobs joined"));
                }
                if j + 1 < layers.len() {
                    root = xmss_pk_from_sig(p, index, &sig[start..], &root, pk_seed, addr);
                }
            }
        }
        Some(sig)
    }
}

// ============================================================================
// TopTreeCache implementation
// ============================================================================

impl<const N: usize> TopTreeCache<N> {
    /// Precomputes the complete static top XMSS tree (layer `d - 1`) for `sk`.
    ///
    /// Panics if `N != p.n`, `sk.len() != 4 * N`, or the computed root does not match
    /// `PK.root` in `sk`.
    #[inline(never)]
    pub fn new(family: HashFamily, p: &Params, sk: &[u8]) -> Self {
        assert_eq!(N, p.n, "TopTreeCache: N must match p.n");
        assert_eq!(sk.len(), 4 * N, "TopTreeCache: secret key must be 4*N bytes");
        let sk_seed = block::<N>(sk, 0);
        let pk_seed = block::<N>(sk, 2);
        let pk_root = block::<N>(sk, 3);
        let top_tree = match family {
            HashFamily::Sha2 => sha2_ops::build_xmss_tree(p.hp, p.d - 1, 0, &sk_seed, &pk_seed),
            HashFamily::Shake => shake_ops::build_xmss_tree(p.hp, p.d - 1, 0, &sk_seed, &pk_seed),
        };
        assert_eq!(
            tree_root(&top_tree),
            pk_root,
            "TopTreeCache: secret key PK.root does not match computed top-tree root"
        );
        Self {
            family,
            hp: p.hp,
            d: p.d,
            pk_seed,
            top_tree,
            layer_d2: Vec::new(),
            layer_d2_capacity: 0,
        }
    }

    /// Precomputes the top XMSS tree for a SHA-2 parameter set.
    #[inline(never)]
    pub fn new_sha2(p: &Params, sk: &[u8]) -> Self {
        Self::new(HashFamily::Sha2, p, sk)
    }

    /// Precomputes the top XMSS tree for a SHAKE parameter set.
    #[inline(never)]
    pub fn new_shake(p: &Params, sk: &[u8]) -> Self {
        Self::new(HashFamily::Shake, p, sk)
    }

    /// Configures the maximum number of layer `d - 2` subtrees to cache lazily during
    /// [`Self::sign_mut`] / [`Self::sign_deterministic_mut`] (MRU eviction).
    pub fn with_layer_d2_capacity(mut self, capacity: usize) -> Self {
        self.set_layer_d2_capacity(capacity);
        self
    }

    /// Updates the maximum number of dynamically cached layer `d - 2` subtrees.
    /// Truncates least-recently-used entries if `capacity` is smaller than the current count.
    pub fn set_layer_d2_capacity(&mut self, capacity: usize) {
        self.layer_d2_capacity = capacity;
        if self.layer_d2.len() > capacity {
            self.layer_d2.truncate(capacity);
        }
    }

    /// Precomputes all `2^hp` subtrees at layer `d - 2` so every signature skips both
    /// layer `d - 1` and layer `d - 2` even when signing with an immutable `&self`.
    ///
    /// Especially practical for fast (`-f`) parameter sets (`2^hp = 8` for 128f/192f,
    /// `16` for 256f; < 16 KiB total).
    #[inline(never)]
    pub fn precompute_layer_d2(&mut self, p: &Params, sk: &[u8]) {
        self.assert_compatible(p, sk);
        if p.d < 2 {
            return;
        }
        let sk_seed = block::<N>(sk, 0);
        let pk_seed = block::<N>(sk, 2);
        let count = 1u64 << p.hp;
        let mut entries = Vec::with_capacity(count as usize);
        for tree_idx in 0..count {
            let nodes = match self.family {
                HashFamily::Sha2 => {
                    sha2_ops::build_xmss_tree(p.hp, p.d - 2, tree_idx, &sk_seed, &pk_seed)
                }
                HashFamily::Shake => {
                    shake_ops::build_xmss_tree(p.hp, p.d - 2, tree_idx, &sk_seed, &pk_seed)
                }
            };
            entries.push(LayerD2Entry {
                tree_index: tree_idx,
                nodes,
            });
        }
        self.layer_d2 = entries;
        if self.layer_d2_capacity < count as usize {
            self.layer_d2_capacity = count as usize;
        }
    }

    /// The hash family this cache was built for.
    #[inline]
    pub fn family(&self) -> HashFamily {
        self.family
    }

    /// The public seed (`PK.seed`) associated with this cache.
    #[inline]
    pub fn pk_seed(&self) -> &[u8; N] {
        &self.pk_seed
    }

    /// The public root (`PK.root`) of the cached top XMSS tree.
    #[inline]
    pub fn pk_root(&self) -> &[u8; N] {
        &self.top_tree[self.top_tree.len() - 1]
    }

    /// Returns `true` if `sk` has length `4 * N` and matches this cache's `PK.seed` and `PK.root`.
    pub fn matches_key(&self, sk: &[u8]) -> bool {
        sk.len() == 4 * N
            && sk[2 * N..3 * N] == self.pk_seed[..]
            && sk[3 * N..4 * N] == self.pk_root()[..]
    }

    /// Number of Merkle nodes stored for the top XMSS tree (`2^(hp + 1) - 1`).
    #[inline]
    pub fn top_tree_nodes(&self) -> usize {
        self.top_tree.len()
    }

    /// Number of layer `d - 2` subtrees currently cached.
    #[inline]
    pub fn layer_d2_cached_trees(&self) -> usize {
        self.layer_d2.len()
    }

    /// Total memory occupied by cached Merkle tree nodes, in bytes.
    pub fn memory_bytes(&self) -> usize {
        let mut nodes = self.top_tree.len();
        for entry in &self.layer_d2 {
            nodes += entry.nodes.len();
        }
        nodes * N
    }

    pub(crate) fn assert_family(&self, expected: HashFamily) {
        assert_eq!(self.family, expected, "TopTreeCache: hash family mismatch");
    }

    fn assert_compatible(&self, p: &Params, sk: &[u8]) {
        assert_eq!(N, p.n, "TopTreeCache: N must match p.n");
        assert_eq!(self.hp, p.hp, "TopTreeCache: parameter set h' mismatch");
        assert_eq!(self.d, p.d, "TopTreeCache: parameter set d mismatch");
        assert!(
            self.matches_key(sk),
            "TopTreeCache: cache does not match the provided secret key"
        );
    }

    fn lookup_d2(&self, tree_d2: u64) -> Option<&[[u8; N]]> {
        lookup_cached_index(&self.layer_d2, tree_d2).map(|pos| self.layer_d2[pos].nodes.as_slice())
    }

    fn lookup_or_populate_d2(
        &mut self,
        p: &Params,
        sk_seed: &[u8; N],
        pk_seed: &[u8; N],
        tree_d2: u64,
    ) -> Option<&[[u8; N]]> {
        if self.layer_d2_capacity == 0 && self.layer_d2.is_empty() {
            return None;
        }
        if let Some(pos) = find_cached_index(&self.layer_d2, tree_d2) {
            if pos != 0 && self.layer_d2.len() < (1usize << p.hp) {
                let entry = self.layer_d2.remove(pos);
                self.layer_d2.insert(0, entry);
                return Some(&self.layer_d2[0].nodes);
            }
            return Some(&self.layer_d2[pos].nodes);
        }
        if self.layer_d2_capacity == 0 || p.d < 2 {
            return None;
        }
        let nodes = match self.family {
            HashFamily::Sha2 => {
                sha2_ops::build_xmss_tree(p.hp, p.d - 2, tree_d2, sk_seed, pk_seed)
            }
            HashFamily::Shake => {
                shake_ops::build_xmss_tree(p.hp, p.d - 2, tree_d2, sk_seed, pk_seed)
            }
        };
        if self.layer_d2.len() >= self.layer_d2_capacity {
            self.layer_d2.pop();
        }
        self.layer_d2.insert(
            0,
            LayerD2Entry {
                tree_index: tree_d2,
                nodes,
            },
        );
        Some(&self.layer_d2[0].nodes)
    }

    /// Computes the layer `d - 2` tree index implied by `digest`.
    #[inline]
    fn layer_d2_tree_index(p: &Params, digest: &[u8]) -> u64 {
        if p.d < 2 {
            return 0;
        }
        let idx_tree = digest_tree(p, digest);
        idx_tree >> ((p.d - 2) * p.hp)
    }

    /// Algorithm 19 (`slh_sign_internal`) using this cache (immutable, thread-safe).
    /// Produces signatures 100% byte-for-byte identical to `slh_sign_internal`.
    #[inline(never)]
    pub fn sign_internal(
        &self,
        p: &Params,
        m: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Vec<u8> {
        self.assert_compatible(p, sk);
        let sk_seed = block::<N>(sk, 0);
        let sk_prf = block::<N>(sk, 1);
        let pk_seed = block::<N>(sk, 2);
        let pk_root = block::<N>(sk, 3);
        let (r, digest) = match self.family {
            HashFamily::Sha2 => {
                sha2_ops::internal_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, m)
            }
            HashFamily::Shake => {
                shake_ops::internal_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, m)
            }
        };
        let d2_hit = if self.layer_d2.is_empty() {
            None
        } else {
            self.lookup_d2(Self::layer_d2_tree_index(p, &digest))
        };
        match self.family {
            HashFamily::Sha2 => sha2_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
            HashFamily::Shake => shake_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
        }
    }

    /// Algorithm 19 (`slh_sign_internal`) using this cache, populating the dynamic
    /// layer `d - 2` MRU cache on misses when `layer_d2_capacity > 0`.
    #[inline(never)]
    pub fn sign_internal_mut(
        &mut self,
        p: &Params,
        m: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Vec<u8> {
        self.assert_compatible(p, sk);
        let sk_seed = block::<N>(sk, 0);
        let sk_prf = block::<N>(sk, 1);
        let pk_seed = block::<N>(sk, 2);
        let pk_root = block::<N>(sk, 3);
        let (r, digest) = match self.family {
            HashFamily::Sha2 => {
                sha2_ops::internal_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, m)
            }
            HashFamily::Shake => {
                shake_ops::internal_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, m)
            }
        };
        let tree_d2 = Self::layer_d2_tree_index(p, &digest);
        let has_d2 = self
            .lookup_or_populate_d2(p, &sk_seed, &pk_seed, tree_d2)
            .is_some();
        let d2_hit = if has_d2 {
            self.lookup_d2(tree_d2)
        } else {
            None
        };
        match self.family {
            HashFamily::Sha2 => sha2_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
            HashFamily::Shake => shake_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
        }
    }

    /// Algorithm 22 (`slh_sign`, hedged pure signing) using this cache.
    /// Returns `None` if `ctx.len() > 255`.
    #[inline(never)]
    pub fn sign(
        &self,
        p: &Params,
        m: &[u8],
        ctx: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Option<Vec<u8>> {
        if ctx.len() > 255 {
            return None;
        }
        self.assert_compatible(p, sk);
        let sk_seed = block::<N>(sk, 0);
        let sk_prf = block::<N>(sk, 1);
        let pk_seed = block::<N>(sk, 2);
        let pk_root = block::<N>(sk, 3);
        let (r, digest) = match self.family {
            HashFamily::Sha2 => {
                sha2_ops::pure_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, ctx, m)
            }
            HashFamily::Shake => {
                shake_ops::pure_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, ctx, m)
            }
        };
        let d2_hit = if self.layer_d2.is_empty() {
            None
        } else {
            self.lookup_d2(Self::layer_d2_tree_index(p, &digest))
        };
        let sig = match self.family {
            HashFamily::Sha2 => sha2_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
            HashFamily::Shake => shake_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
        };
        Some(sig)
    }

    /// Algorithm 22 (`slh_sign`, deterministic pure signing) using this cache.
    /// Returns `None` if `ctx.len() > 255`.
    pub fn sign_deterministic(
        &self,
        p: &Params,
        m: &[u8],
        ctx: &[u8],
        sk: &[u8],
    ) -> Option<Vec<u8>> {
        if ctx.len() > 255 {
            return None;
        }
        let pk_seed = block::<N>(sk, 2);
        self.sign(p, m, ctx, sk, &pk_seed)
    }

    /// Algorithm 22 (`slh_sign`, hedged pure signing) with dynamic layer `d - 2` MRU caching.
    /// Returns `None` if `ctx.len() > 255`.
    #[inline(never)]
    pub fn sign_mut(
        &mut self,
        p: &Params,
        m: &[u8],
        ctx: &[u8],
        sk: &[u8],
        addrnd: &[u8; N],
    ) -> Option<Vec<u8>> {
        if ctx.len() > 255 {
            return None;
        }
        self.assert_compatible(p, sk);
        let sk_seed = block::<N>(sk, 0);
        let sk_prf = block::<N>(sk, 1);
        let pk_seed = block::<N>(sk, 2);
        let pk_root = block::<N>(sk, 3);
        let (r, digest) = match self.family {
            HashFamily::Sha2 => {
                sha2_ops::pure_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, ctx, m)
            }
            HashFamily::Shake => {
                shake_ops::pure_digest(p, &sk_prf, &pk_seed, &pk_root, addrnd, ctx, m)
            }
        };
        let tree_d2 = Self::layer_d2_tree_index(p, &digest);
        let has_d2 = self
            .lookup_or_populate_d2(p, &sk_seed, &pk_seed, tree_d2)
            .is_some();
        let d2_hit = if has_d2 {
            self.lookup_d2(tree_d2)
        } else {
            None
        };
        let sig = match self.family {
            HashFamily::Sha2 => sha2_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
            HashFamily::Shake => shake_ops::sign_from_digest(
                p,
                &sk_seed,
                &pk_seed,
                &r,
                &digest,
                &self.top_tree,
                d2_hit,
            ),
        };
        Some(sig)
    }

    /// Algorithm 22 (`slh_sign`, deterministic pure signing) with dynamic layer `d - 2` MRU caching.
    /// Returns `None` if `ctx.len() > 255`.
    pub fn sign_deterministic_mut(
        &mut self,
        p: &Params,
        m: &[u8],
        ctx: &[u8],
        sk: &[u8],
    ) -> Option<Vec<u8>> {
        if ctx.len() > 255 {
            return None;
        }
        let pk_seed = block::<N>(sk, 2);
        self.sign_mut(p, m, ctx, sk, &pk_seed)
    }
}

// ============================================================================
// Free generic entry points
// ============================================================================

/// Algorithm 21 (`slh_keygen`) that simultaneously captures the top XMSS tree into a
/// [`TopTreeCache`] at **zero extra hash cost** compared to uncached key generation.
#[inline(never)]
pub fn keygen_with_cache<const N: usize>(
    family: HashFamily,
    p: &Params,
    seeds: &[u8],
    sk: &mut [u8],
    pk: &mut [u8],
) -> TopTreeCache<N> {
    assert_eq!(N, p.n, "keygen_with_cache: N must match p.n");
    assert_eq!(seeds.len(), 3 * N, "keygen_with_cache: seeds must be 3*N bytes");
    assert_eq!(sk.len(), 4 * N, "keygen_with_cache: sk must be 4*N bytes");
    assert_eq!(pk.len(), 2 * N, "keygen_with_cache: pk must be 2*N bytes");
    let sk_seed = block::<N>(seeds, 0);
    let sk_prf = block::<N>(seeds, 1);
    let pk_seed = block::<N>(seeds, 2);
    let top_tree = match family {
        HashFamily::Sha2 => sha2_ops::build_xmss_tree(p.hp, p.d - 1, 0, &sk_seed, &pk_seed),
        HashFamily::Shake => shake_ops::build_xmss_tree(p.hp, p.d - 1, 0, &sk_seed, &pk_seed),
    };
    let pk_root = tree_root(&top_tree);
    sk[0..N].copy_from_slice(&sk_seed);
    sk[N..2 * N].copy_from_slice(&sk_prf);
    sk[2 * N..3 * N].copy_from_slice(&pk_seed);
    sk[3 * N..4 * N].copy_from_slice(&pk_root);
    pk[0..N].copy_from_slice(&pk_seed);
    pk[N..2 * N].copy_from_slice(&pk_root);
    TopTreeCache {
        family,
        hp: p.hp,
        d: p.d,
        pk_seed,
        top_tree,
        layer_d2: Vec::new(),
        layer_d2_capacity: 0,
    }
}

/// Hedged pure SLH-DSA signing using a precomputed [`TopTreeCache`].
pub fn sign_cached<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sk: &[u8],
    addrnd: &[u8; N],
    cache: &TopTreeCache<N>,
) -> Option<Vec<u8>> {
    cache.sign(p, m, ctx, sk, addrnd)
}

/// Deterministic pure SLH-DSA signing using a precomputed [`TopTreeCache`].
pub fn sign_deterministic_cached<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sk: &[u8],
    cache: &TopTreeCache<N>,
) -> Option<Vec<u8>> {
    cache.sign_deterministic(p, m, ctx, sk)
}

/// Hedged pure SLH-DSA signing with dynamic layer `d - 2` MRU caching.
pub fn sign_cached_mut<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sk: &[u8],
    addrnd: &[u8; N],
    cache: &mut TopTreeCache<N>,
) -> Option<Vec<u8>> {
    cache.sign_mut(p, m, ctx, sk, addrnd)
}

/// Deterministic pure SLH-DSA signing with dynamic layer `d - 2` MRU caching.
pub fn sign_deterministic_cached_mut<const N: usize>(
    p: &Params,
    m: &[u8],
    ctx: &[u8],
    sk: &[u8],
    cache: &mut TopTreeCache<N>,
) -> Option<Vec<u8>> {
    cache.sign_deterministic_mut(p, m, ctx, sk)
}

// ============================================================================
// Typed per-parameter-set modules for all 12 FIPS 205 sets
// ============================================================================

macro_rules! cache_set {
    ($name:ident, $family:expr, $doc:expr) => {
        #[doc = $doc]
        pub mod $name {
            use alloc::vec::Vec;
            use super::{HashFamily, TopTreeCache};
            use crate::$name::params::{N, PARAMS, PK_BYTES, SEED_BYTES, SK_BYTES};

            /// Fixed-width top-tree cache for this parameter set.
            pub type Cache = TopTreeCache<N>;

            /// Precomputes the top XMSS tree (layer `d - 1`) for `sk`.
            #[inline(never)]
            pub fn new(sk: &[u8; SK_BYTES]) -> Cache {
                TopTreeCache::new($family, &PARAMS, sk)
            }

            /// Generates `(sk, pk)` and its [`Cache`] in a single top-tree pass.
            #[inline(never)]
            pub fn keygen_with_cache(
                seeds: &[u8; SEED_BYTES],
                sk: &mut [u8; SK_BYTES],
                pk: &mut [u8; PK_BYTES],
            ) -> Cache {
                super::keygen_with_cache::<N>($family, &PARAMS, seeds, sk, pk)
            }

            /// Precomputes all `2^h'` subtrees at layer `d - 2` into `cache`.
            #[inline(never)]
            pub fn precompute_layer_d2(cache: &mut Cache, sk: &[u8; SK_BYTES]) {
                cache.assert_family($family);
                cache.precompute_layer_d2(&PARAMS, sk);
            }

            /// Algorithm 19 (`slh_sign_internal`) using `cache`.
            pub fn sign_internal_cached(
                m: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
                cache: &Cache,
            ) -> Vec<u8> {
                cache.assert_family($family);
                cache.sign_internal(&PARAMS, m, sk, addrnd)
            }

            /// Algorithm 22 (`slh_sign`, hedged) using `cache`.
            pub fn sign_cached(
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
                cache: &Cache,
            ) -> Option<Vec<u8>> {
                cache.assert_family($family);
                cache.sign(&PARAMS, m, ctx, sk, addrnd)
            }

            /// Algorithm 22 (`slh_sign`, deterministic) using `cache`.
            pub fn sign_deterministic_cached(
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
                cache: &Cache,
            ) -> Option<Vec<u8>> {
                cache.assert_family($family);
                cache.sign_deterministic(&PARAMS, m, ctx, sk)
            }

            /// Algorithm 22 (`slh_sign`, hedged) with dynamic layer `d - 2` MRU caching.
            pub fn sign_cached_mut(
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
                addrnd: &[u8; N],
                cache: &mut Cache,
            ) -> Option<Vec<u8>> {
                cache.assert_family($family);
                cache.sign_mut(&PARAMS, m, ctx, sk, addrnd)
            }

            /// Algorithm 22 (`slh_sign`, deterministic) with dynamic layer `d - 2` MRU caching.
            pub fn sign_deterministic_cached_mut(
                m: &[u8],
                ctx: &[u8],
                sk: &[u8; SK_BYTES],
                cache: &mut Cache,
            ) -> Option<Vec<u8>> {
                cache.assert_family($family);
                cache.sign_deterministic_mut(&PARAMS, m, ctx, sk)
            }
        }
    };
}

cache_set!(sha2_128s, HashFamily::Sha2, "Top-tree caching for SLH-DSA-SHA2-128s.");
cache_set!(sha2_128f, HashFamily::Sha2, "Top-tree caching for SLH-DSA-SHA2-128f.");
cache_set!(sha2_192s, HashFamily::Sha2, "Top-tree caching for SLH-DSA-SHA2-192s.");
cache_set!(sha2_192f, HashFamily::Sha2, "Top-tree caching for SLH-DSA-SHA2-192f.");
cache_set!(sha2_256s, HashFamily::Sha2, "Top-tree caching for SLH-DSA-SHA2-256s.");
cache_set!(sha2_256f, HashFamily::Sha2, "Top-tree caching for SLH-DSA-SHA2-256f.");

cache_set!(shake_128s, HashFamily::Shake, "Top-tree caching for SLH-DSA-SHAKE-128s.");
cache_set!(shake_128f, HashFamily::Shake, "Top-tree caching for SLH-DSA-SHAKE-128f.");
cache_set!(shake_192s, HashFamily::Shake, "Top-tree caching for SLH-DSA-SHAKE-192s.");
cache_set!(shake_192f, HashFamily::Shake, "Top-tree caching for SLH-DSA-SHAKE-192f.");
cache_set!(shake_256s, HashFamily::Shake, "Top-tree caching for SLH-DSA-SHAKE-256s.");
cache_set!(shake_256f, HashFamily::Shake, "Top-tree caching for SLH-DSA-SHAKE-256f.");

// Immutable lookup also handles fully precomputed trees by direct index.
#[inline]
fn lookup_cached_index<const N: usize>(entries: &[LayerD2Entry<N>], tree_d2: u64) -> Option<usize> {
    if entries.is_empty() {
        return None;
    }
    // Fast O(1) direct index when all 2^hp layer d - 2 trees were precomputed in order.
    let idx = tree_d2 as usize;
    if idx < entries.len() && entries[idx].tree_index == tree_d2 {
        return Some(idx);
    }
    find_cached_index(entries, tree_d2)
}
