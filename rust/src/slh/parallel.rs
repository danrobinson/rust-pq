// Unified multicore parallel key generation and signing for both SHA-2 and SHAKE.
//
// Signing decomposes ALL independent work — FORS trees (splitting tall subtrees),
// XMSS authentication nodes (splitting tall subtrees), and XMSS signing-leaf
// public keys — into one lock-free work queue ordered largest-work-first, then
// runs all `d` WOTS+ signatures in parallel once the layer roots are climbed.
use super::super::fors::{fors_node, fors_sk_gen};
use super::super::hash::Seed;
use super::super::wots::wots_sign;
use super::super::xmss::hash2;
use super::*;
use crate::address::{TREE, WOTS_HASH};
use crate::util::base_2b;
use core::sync::atomic::{AtomicU8, AtomicUsize, Ordering};
use std::sync::{Condvar, Mutex, OnceLock};

/// Reduce `1 << split_depth` subtree roots at height `sub_h` up to `(root_idx, height)`.
#[inline]
fn reduce_tree<const N: usize>(
    slots: &[OnceLock<[u8; N]>],
    seed: &Seed<N>,
    adrs: Adrs,
    root_idx: u32,
    sub_h: u32,
    height: u32,
) -> [u8; N] {
    let mut cur: Vec<[u8; N]> = slots
        .iter()
        .map(|slot| *slot.get().expect("subtree job completed"))
        .collect();
    for lvl in (sub_h + 1)..=height {
        let shift = height - lvl;
        let base = root_idx << shift;
        let next_len = cur.len() / 2;
        for idx in 0..next_len {
            let a = adrs.with_word2(lvl).with_word3(base + idx as u32);
            cur[idx] = hash2::<N>(seed, &a, &cur[2 * idx], &cur[2 * idx + 1]);
        }
        cur.truncate(next_len);
    }
    cur[0]
}

/// Parallel top-tree key generation for `slh_keygen_internal`.
pub(super) fn keygen<const N: usize>(
    p: &Params,
    sk_seed: &[u8; N],
    seed: &Seed<N>,
    adrs: Adrs,
) -> Option<[u8; N]> {
    let threads = crate::pool::available_threads();
    if threads < 2 || p.hp < 3 {
        return None;
    }
    // Split tall trees (`hp >= 8`) into 64 balanced subtrees (height 3 for hp=9,
    // height 2 for hp=8 on non-x86 / height 3 on x86_64 for AVX-512 subtree8);
    // split small trees (`hp == 3..4`) down to leaves.
    #[cfg(target_arch = "x86_64")]
    let sub_h = if p.hp >= 8 {
        3
    } else if p.hp >= 6 {
        2
    } else {
        0
    };
    #[cfg(not(target_arch = "x86_64"))]
    let sub_h = if p.hp >= 9 {
        3
    } else if p.hp >= 6 {
        2
    } else {
        0
    };
    let split = p.hp - sub_h;
    let count = 1usize << split;
    let nodes: Vec<OnceLock<[u8; N]>> = (0..count).map(|_| OnceLock::new()).collect();
    let next = AtomicUsize::new(0);
    let fill = || loop {
        let job = next.fetch_add(1, Ordering::Relaxed);
        let Some(slot) = nodes.get(job) else { break };
        let value = xmss_node::<N>(sk_seed, job as u32, sub_h, seed, adrs);
        slot.set(value).expect("unique keygen subtree job");
    };
    crate::pool::execute(threads.min(count), true, &fill);
    Some(reduce_tree(
        &nodes,
        seed,
        adrs.with_type(TREE),
        0,
        sub_h,
        p.hp,
    ))
}

shake_only! {
    #[cfg(any(
        all(target_arch = "aarch64", target_endian = "little"),
        all(target_arch = "x86_64", target_feature = "sse2")
    ))]
    mod shake_fors_simd {
        use super::super::super::batch::{pair_active, short_active};
        use super::super::super::fors_batch::{fors_leaves_fused, fors_subtree_horiz};
        use crate::address::{Adrs, FORS_PRF};
        use crate::shake256::parallel::WIDTH;

        pub(super) fn secrets<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            indices: [u32; WIDTH],
            active: usize,
        ) -> [[u8; N]; WIDTH] {
            let prf = addr.with_type(FORS_PRF).with_keypair(addr.keypair);
            short_active(seed, &indices.map(|i| prf.with_word3(i)), &[*sk; WIDTH], active)
        }

        /// Compute `active` (`1..=WIDTH`) FORS nodes at `level`. When `WIDTH == 8`
        /// and `level >= 3`, run each active subtree horizontally at full 8-way SIMD
        /// width with zero wasted lanes.
        pub(super) fn nodes_active<const N: usize>(
            sk: &[u8; N],
            seed: &[u8; N],
            addr: Adrs,
            indices: [u32; WIDTH],
            active: usize,
            level: u32,
        ) -> [[u8; N]; WIDTH] {
            if WIDTH == 8 && level >= 3 {
                let mut out = [[0u8; N]; WIDTH];
                for lane in 0..active {
                    out[lane] = fors_subtree_horiz(sk, seed, addr, indices[lane], level);
                }
                return out;
            }
            if level == 0 {
                fors_leaves_fused(sk, seed, addr, &indices, active)
            } else {
                let left = nodes_active(sk, seed, addr, indices.map(|i| i * 2), active, level - 1);
                let right = nodes_active(
                    sk,
                    seed,
                    addr,
                    indices.map(|i| i * 2 + 1),
                    active,
                    level - 1,
                );
                let addresses = indices.map(|i| addr.with_word2(level).with_word3(i));
                pair_active(seed, &addresses, &left, &right, active)
            }
        }
    }
}

struct XmssAuthMeta {
    slot_start: usize,
    split: u32,
    root_idx: u32,
    height: u32,
}

struct ForsSplitMeta {
    tree: u32,
    height: u32,
    root_idx: u32,
    sub_h: u32,
    slot_start: usize,
    chunks: usize,
}

#[derive(Clone, Copy)]
enum WorkKind {
    /// Compute an XMSS subtree `(layer, idx, height)` into `xmss_slots[slot]`.
    XmssSubtree {
        layer: u16,
        idx: u32,
        height: u32,
        slot: usize,
    },
    /// Compute the WOTS+ public key of the signing leaf on `layer` into `leaf_pks[layer]`.
    XmssLeafPk { layer: u16 },
    /// Compute secret + auth heights `0..low_h` for one FORS tree (scalar / SHA-2 path).
    ForsTreeLow { tree: u32, low_h: u32 },
    /// Compute one FORS node `(idx, height)` directly into `fors_direct[slot]`.
    ForsNodeDirect { idx: u32, height: u32, slot: usize },
    /// Compute one split FORS subtree `(idx, height)` into `fors_split[slot]`.
    ForsNodeSplit { idx: u32, height: u32, slot: usize },
    /// SHAKE SIMD group: compute secrets + auth heights `0..low_h` for `active` trees starting at `first`.
    #[allow(dead_code)]
    ForsShakeLow {
        first: u16,
        active: u8,
        low_h: u8,
    },
    /// SHAKE SIMD group: compute auth height `height` directly into `fors_direct` for `active` trees.
    #[allow(dead_code)]
    ForsShakeDirect {
        first: u16,
        active: u8,
        height: u8,
    },
    /// SHAKE SIMD group: compute chunk `chunk` of split auth height `height` (subtree height `sub_h`).
    #[allow(dead_code)]
    ForsShakeSplit {
        first: u16,
        active: u8,
        height: u8,
        sub_h: u8,
        chunk: u32,
        split_base: usize,
        chunks: usize,
    },
}

#[derive(Clone, Copy)]
struct WorkItem {
    weight: u32,
    kind: WorkKind,
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
    let threads = crate::pool::available_threads();
    if threads < 2 || p.hp == 0 {
        return None;
    }

    let d = p.d as usize;
    let hp = p.hp as usize;
    let k = p.k as usize;
    let a = p.a;

    let mut layers = Vec::with_capacity(d);
    for j in 0..p.d {
        layers.push((Adrs::new().with_layer(j).with_tree(tree), leaf));
        leaf = (tree & ((1u64 << p.hp) - 1)) as u32;
        tree >>= p.hp;
    }
    let fors_indices = base_2b(md, a, k);

    let mut jobs: Vec<WorkItem> = Vec::new();

    // --- 1. XMSS auth path nodes (splitting tall subtrees) + signing leaf PKs ---
    let xmss_target: u32 = if p.hp >= 6 { 3 } else { 2 };
    let mut xmss_meta: Vec<XmssAuthMeta> = Vec::with_capacity(d * hp);
    let mut xmss_slot_count = 0usize;

    for (j, &(_, index)) in layers.iter().enumerate() {
        for h in 0..p.hp {
            let root_idx = (index >> h) ^ 1;
            let split = h.saturating_sub(xmss_target);
            let sub_h = h - split;
            let chunks = 1usize << split;
            let slot_start = xmss_slot_count;
            xmss_slot_count += chunks;
            xmss_meta.push(XmssAuthMeta {
                slot_start,
                split,
                root_idx,
                height: h,
            });
            let weight = 256u32 << sub_h;
            for c in 0..chunks {
                jobs.push(WorkItem {
                    weight,
                    kind: WorkKind::XmssSubtree {
                        layer: j as u16,
                        idx: (root_idx << split) + c as u32,
                        height: sub_h,
                        slot: slot_start + c,
                    },
                });
            }
        }
    }

    // Signing leaf WOTS+ public keys for layers 0..d-1 so all layer roots can be
    // climbed immediately after Phase 1 and all `d` WOTS+ signatures run in parallel.
    let leaf_pk_count = d.saturating_sub(1);
    for j in 0..leaf_pk_count {
        jobs.push(WorkItem {
            weight: 256,
            kind: WorkKind::XmssLeafPk { layer: j as u16 },
        });
    }

    // --- 2. FORS trees (splitting tall subtrees, preserving SIMD on SHAKE) ---
    let fors_stride = a as usize + 1;
    let mut fors_split_meta: Vec<ForsSplitMeta> = Vec::new();
    let mut fors_split_count = 0usize;

    #[allow(unused_mut)]
    let mut built_shake_simd_fors = false;

    shake_only! {
        #[cfg(any(
            all(target_arch = "aarch64", target_endian = "little"),
            all(target_arch = "x86_64", target_feature = "sse2")
        ))]
        if super::super::batch::available::<N>() {
            use crate::shake256::parallel::WIDTH;
            built_shake_simd_fors = true;
            if WIDTH == 8 {
                // Heights 0..3 batch across trees in WIDTH-tree SIMD groups; every
                // height >= 3 runs horizontally inside `fors_subtree_horiz` at full
                // 8-way SIMD width, so emit fine-grained per-tree subtree jobs for
                // optimal multicore load balancing across all cores.
                let low_h = a.min(3);
                for first in (0..k).step_by(WIDTH) {
                    let active = (k - first).min(WIDTH);
                    jobs.push(WorkItem {
                        weight: (active as u32) << low_h,
                        kind: WorkKind::ForsShakeLow {
                            first: first as u16,
                            active: active as u8,
                            low_h: low_h as u8,
                        },
                    });
                }
                let fors_target: u32 = if a >= 10 { 9 } else if a >= 9 { 8 } else { a };
                for t in 0..p.k {
                    let idx = fors_indices[t as usize];
                    for j in low_h..a {
                        let root_idx = (t << (a - j)) + ((idx >> j) ^ 1);
                        let split = j.saturating_sub(fors_target);
                        if split == 0 {
                            jobs.push(WorkItem {
                                weight: 1u32 << j,
                                kind: WorkKind::ForsNodeDirect {
                                    idx: root_idx,
                                    height: j,
                                    slot: t as usize * fors_stride + 1 + j as usize,
                                },
                            });
                        } else {
                            let chunks = 1usize << split;
                            let slot_start = fors_split_count;
                            fors_split_count += chunks;
                            fors_split_meta.push(ForsSplitMeta {
                                tree: t,
                                height: j,
                                root_idx,
                                sub_h: fors_target,
                                slot_start,
                                chunks,
                            });
                            let weight = 1u32 << fors_target;
                            for c in 0..chunks {
                                jobs.push(WorkItem {
                                    weight,
                                    kind: WorkKind::ForsNodeSplit {
                                        idx: (root_idx << split) + c as u32,
                                        height: fors_target,
                                        slot: slot_start + c,
                                    },
                                });
                            }
                        }
                    }
                }
            } else {
                // Split tall FORS trees (`a >= 9` on SHAKE) into height-9 (for `-s`)
                // or height-8 (for 256f) subtrees across WIDTH-tree SIMD groups.
                let fors_target: u32 = if a >= 10 {
                    9
                } else if a >= 9 {
                    8
                } else {
                    a
                };
                let low_h = a.min(fors_target);
                for first in (0..k).step_by(WIDTH) {
                    let active = (k - first).min(WIDTH);
                    jobs.push(WorkItem {
                        weight: 1u32 << low_h,
                        kind: WorkKind::ForsShakeLow {
                            first: first as u16,
                            active: active as u8,
                            low_h: low_h as u8,
                        },
                    });
                    for j in low_h..a {
                        let split = j - fors_target;
                        let chunks = 1usize << split;
                        if split == 0 {
                            jobs.push(WorkItem {
                                weight: 1u32 << j,
                                kind: WorkKind::ForsShakeDirect {
                                    first: first as u16,
                                    active: active as u8,
                                    height: j as u8,
                                },
                            });
                        } else {
                            let split_base = fors_split_count;
                            fors_split_count += active * chunks;
                            for lane in 0..active {
                                let t = (first + lane) as u32;
                                let root_idx = (t << (a - j)) + ((fors_indices[t as usize] >> j) ^ 1);
                                fors_split_meta.push(ForsSplitMeta {
                                    tree: t,
                                    height: j,
                                    root_idx,
                                    sub_h: fors_target,
                                    slot_start: split_base + lane * chunks,
                                    chunks,
                                });
                            }
                            let weight = 1u32 << fors_target;
                            for c in 0..chunks {
                                jobs.push(WorkItem {
                                    weight,
                                    kind: WorkKind::ForsShakeSplit {
                                        first: first as u16,
                                        active: active as u8,
                                        height: j as u8,
                                        sub_h: fors_target as u8,
                                        chunk: c as u32,
                                        split_base,
                                        chunks,
                                    },
                                });
                            }
                        }
                    }
                }
            }
        }
    }

    if !built_shake_simd_fors {
        let fors_target: u32 = if a >= 10 { 9 } else { a };
        let low_h = a.min(fors_target);
        for t in 0..p.k {
            let idx = fors_indices[t as usize];
            jobs.push(WorkItem {
                weight: 1u32 << low_h,
                kind: WorkKind::ForsTreeLow { tree: t, low_h },
            });
            for j in low_h..a {
                let root_idx = (t << (a - j)) + ((idx >> j) ^ 1);
                let split = j - fors_target;
                if split == 0 {
                    jobs.push(WorkItem {
                        weight: 1u32 << j,
                        kind: WorkKind::ForsNodeDirect {
                            idx: root_idx,
                            height: j,
                            slot: t as usize * fors_stride + 1 + j as usize,
                        },
                    });
                } else {
                    let chunks = 1usize << split;
                    let slot_start = fors_split_count;
                    fors_split_count += chunks;
                    fors_split_meta.push(ForsSplitMeta {
                        tree: t,
                        height: j,
                        root_idx,
                        sub_h: fors_target,
                        slot_start,
                        chunks,
                    });
                    let weight = 1u32 << fors_target;
                    for c in 0..chunks {
                        jobs.push(WorkItem {
                            weight,
                            kind: WorkKind::ForsNodeSplit {
                                idx: (root_idx << split) + c as u32,
                                height: fors_target,
                                slot: slot_start + c,
                            },
                        });
                    }
                }
            }
        }
    }

    // Order largest-work-first so slow/straggler cores finish on small tail jobs.
    jobs.sort_unstable_by(|x, y| y.weight.cmp(&x.weight));

    let xmss_slots: Vec<OnceLock<[u8; N]>> = (0..xmss_slot_count).map(|_| OnceLock::new()).collect();
    let leaf_pks: Vec<OnceLock<[u8; N]>> = (0..leaf_pk_count).map(|_| OnceLock::new()).collect();
    let fors_direct: Vec<OnceLock<[u8; N]>> =
        (0..k * fors_stride).map(|_| OnceLock::new()).collect();
    let fors_split: Vec<OnceLock<[u8; N]>> =
        (0..fors_split_count).map(|_| OnceLock::new()).collect();

    // --- Phase 1 + Phase 2 fused in ONE pool dispatch (single barrier & stack scrub) ---
    const PHASE1_RUNNING: u8 = 0;
    const PHASE2_READY: u8 = 1;
    const PHASE_ABORTED: u8 = 2;

    struct AbortGuard<'a> {
        state: &'a AtomicU8,
        lock: &'a Mutex<()>,
        cv: &'a Condvar,
        armed: bool,
    }
    impl Drop for AbortGuard<'_> {
        fn drop(&mut self) {
            if self.armed {
                let _g = self.lock.lock().unwrap_or_else(|e| e.into_inner());
                self.state.store(PHASE_ABORTED, Ordering::Release);
                self.cv.notify_all();
            }
        }
    }

    let total_phase1 = jobs.len();
    let phase1_next = AtomicUsize::new(0);
    let phase1_done = AtomicUsize::new(0);
    let phase2_state = AtomicU8::new(PHASE1_RUNNING);
    let phase2_lock = Mutex::new(());
    let phase2_cv = Condvar::new();
    let sig_fors_cell: OnceLock<Vec<u8>> = OnceLock::new();
    let xmss_auth_cell: OnceLock<Vec<[u8; N]>> = OnceLock::new();
    let roots_cell: OnceLock<Vec<[u8; N]>> = OnceLock::new();
    let phase2_next = AtomicUsize::new(0);
    let wots_sigs: Vec<OnceLock<Vec<u8>>> = (0..d).map(|_| OnceLock::new()).collect();

    let run = || {
        let mut abort_guard = AbortGuard {
            state: &phase2_state,
            lock: &phase2_lock,
            cv: &phase2_cv,
            armed: true,
        };
        loop {
            let job_idx = phase1_next.fetch_add(1, Ordering::Relaxed);
            let Some(&item) = jobs.get(job_idx) else {
                break;
            };
            match item.kind {
                WorkKind::XmssSubtree {
                    layer,
                    idx,
                    height,
                    slot,
                } => {
                    let (addr, _) = layers[layer as usize];
                    let val = xmss_node::<N>(sk, idx, height, seed, addr);
                    xmss_slots[slot].set(val).expect("unique XMSS subtree slot");
                }
                WorkKind::XmssLeafPk { layer } => {
                    let (addr, index) = layers[layer as usize];
                    let val = xmss_node::<N>(sk, index, 0, seed, addr);
                    leaf_pks[layer as usize]
                        .set(val)
                        .expect("unique XMSS leaf PK slot");
                }
                WorkKind::ForsTreeLow { tree: t, low_h } => {
                    let idx = fors_indices[t as usize];
                    let base = t as usize * fors_stride;
                    let secret = fors_sk_gen::<N>(sk, seed, fors_addr, (t << a) + idx);
                    fors_direct[base].set(secret).expect("unique FORS sk slot");
                    for j in 0..low_h {
                        let s = (idx >> j) ^ 1;
                        let node = fors_node::<N>(sk, (t << (a - j)) + s, j, seed, fors_addr);
                        fors_direct[base + 1 + j as usize]
                            .set(node)
                            .expect("unique FORS low node slot");
                    }
                }
                WorkKind::ForsNodeDirect { idx, height, slot } => {
                    let node = fors_node::<N>(sk, idx, height, seed, fors_addr);
                    fors_direct[slot]
                        .set(node)
                        .expect("unique FORS direct slot");
                }
                WorkKind::ForsNodeSplit { idx, height, slot } => {
                    let node = fors_node::<N>(sk, idx, height, seed, fors_addr);
                    fors_split[slot].set(node).expect("unique FORS split slot");
                }
                WorkKind::ForsShakeLow {
                    first,
                    active,
                    low_h,
                } => {
                    let _ = (first, active, low_h);
                    shake_only! {
                        #[cfg(any(
                            all(target_arch = "aarch64", target_endian = "little"),
                            all(target_arch = "x86_64", target_feature = "sse2")
                        ))]
                        {
                            let first = first as usize;
                            let active = active as usize;
                            let indices = core::array::from_fn(|lane| {
                                let t = first + lane.min(active - 1);
                                ((t as u32) << a) + fors_indices[t]
                            });
                            let secret =
                                shake_fors_simd::secrets(sk, seed, fors_addr, indices, active);
                            for lane in 0..active {
                                fors_direct[(first + lane) * fors_stride]
                                    .set(secret[lane])
                                    .expect("unique SHAKE FORS sk slot");
                            }
                            for j in 0..u32::from(low_h) {
                                let sibs = shake_fors_simd::nodes_active(
                                    sk,
                                    seed,
                                    fors_addr,
                                    indices.map(|i| (i >> j) ^ 1),
                                    active,
                                    j,
                                );
                                for lane in 0..active {
                                    fors_direct[(first + lane) * fors_stride + 1 + j as usize]
                                        .set(sibs[lane])
                                        .expect("unique SHAKE FORS low slot");
                                }
                            }
                        }
                    }
                }
                WorkKind::ForsShakeDirect {
                    first,
                    active,
                    height,
                } => {
                    let _ = (first, active, height);
                    shake_only! {
                        #[cfg(any(
                            all(target_arch = "aarch64", target_endian = "little"),
                            all(target_arch = "x86_64", target_feature = "sse2")
                        ))]
                        {
                            let first = first as usize;
                            let active = active as usize;
                            let j = u32::from(height);
                            let indices = core::array::from_fn(|lane| {
                                let t = first + lane.min(active - 1);
                                ((t as u32) << (a - j)) + ((fors_indices[t] >> j) ^ 1)
                            });
                            let sibs = shake_fors_simd::nodes_active(
                                sk, seed, fors_addr, indices, active, j,
                            );
                            for lane in 0..active {
                                fors_direct[(first + lane) * fors_stride + 1 + j as usize]
                                    .set(sibs[lane])
                                    .expect("unique SHAKE FORS direct slot");
                            }
                        }
                    }
                }
                WorkKind::ForsShakeSplit {
                    first,
                    active,
                    height,
                    sub_h,
                    chunk,
                    split_base,
                    chunks,
                } => {
                    let _ = (first, active, height, sub_h, chunk, split_base, chunks);
                    shake_only! {
                        #[cfg(any(
                            all(target_arch = "aarch64", target_endian = "little"),
                            all(target_arch = "x86_64", target_feature = "sse2")
                        ))]
                        {
                            let first = first as usize;
                            let active = active as usize;
                            let j = u32::from(height);
                            let sub = u32::from(sub_h);
                            let split = j - sub;
                            let indices = core::array::from_fn(|lane| {
                                let t = first + lane.min(active - 1);
                                let root_idx =
                                    ((t as u32) << (a - j)) + ((fors_indices[t] >> j) ^ 1);
                                (root_idx << split) + chunk
                            });
                            let vals = shake_fors_simd::nodes_active(
                                sk, seed, fors_addr, indices, active, sub,
                            );
                            for lane in 0..active {
                                fors_split[split_base + lane * chunks + chunk as usize]
                                    .set(vals[lane])
                                    .expect("unique SHAKE FORS split slot");
                            }
                        }
                    }
                }
            }

            // The thread that completes the final Phase 1 job immediately reduces
            // split subtrees, computes the FORS PK, climbs all layer roots, and
            // releases Phase 2 to all waiting threads with zero extra OS wakeups.
            if phase1_done.fetch_add(1, Ordering::AcqRel) + 1 == total_phase1 {
                for meta in &fors_split_meta {
                    let val = reduce_tree(
                        &fors_split[meta.slot_start..meta.slot_start + meta.chunks],
                        seed,
                        fors_addr,
                        meta.root_idx,
                        meta.sub_h,
                        meta.height,
                    );
                    fors_direct[meta.tree as usize * fors_stride + 1 + meta.height as usize]
                        .set(val)
                        .expect("unique reduced FORS slot");
                }

                let mut sig_fors = Vec::with_capacity(p.fors_sig_bytes());
                for slot in &fors_direct {
                    sig_fors.extend_from_slice(slot.get().expect("all FORS slots filled"));
                }

                let mut xmss_auth: Vec<[u8; N]> = Vec::with_capacity(d * hp);
                for j in 0..d {
                    let (addr, _) = layers[j];
                    let tree_addr = addr.with_type(TREE);
                    for h in 0..hp {
                        let meta = &xmss_meta[j * hp + h];
                        let node = if meta.split == 0 {
                            *xmss_slots[meta.slot_start]
                                .get()
                                .expect("XMSS auth slot filled")
                        } else {
                            let count = 1usize << meta.split;
                            reduce_tree(
                                &xmss_slots[meta.slot_start..meta.slot_start + count],
                                seed,
                                tree_addr,
                                meta.root_idx,
                                meta.height - meta.split,
                                meta.height,
                            )
                        };
                        xmss_auth.push(node);
                    }
                }

                let mut roots: Vec<[u8; N]> = Vec::with_capacity(d);
                roots.push(fors_pk_from_sig(p, &sig_fors, md, seed, fors_addr));
                for j in 0..leaf_pk_count {
                    let (addr, leaf_idx) = layers[j];
                    let tree_addr = addr.with_type(TREE);
                    let mut node = *leaf_pks[j].get().expect("leaf PK filled");
                    let mut index = leaf_idx;
                    for h in 0..p.hp {
                        let sibling = &xmss_auth[j * hp + h as usize];
                        let parent = index >> 1;
                        let a_node = tree_addr.with_word2(h + 1).with_word3(parent);
                        node = if index & 1 == 0 {
                            hash2::<N>(seed, &a_node, &node, sibling)
                        } else {
                            hash2::<N>(seed, &a_node, sibling, &node)
                        };
                        index = parent;
                    }
                    roots.push(node);
                }

                let _ = sig_fors_cell.set(sig_fors);
                let _ = xmss_auth_cell.set(xmss_auth);
                let _ = roots_cell.set(roots);
                let _g = phase2_lock.lock().unwrap_or_else(|e| e.into_inner());
                phase2_state.store(PHASE2_READY, Ordering::Release);
                phase2_cv.notify_all();
            }
        }

        // Wait briefly for Phase 2 readiness (then park cleanly on Condvar so
        // waiting threads never starve a preempted worker on the last Phase 1 job).
        let mut spins = 0u32;
        loop {
            let st = phase2_state.load(Ordering::Acquire);
            if st == PHASE2_READY {
                break;
            }
            if st == PHASE_ABORTED {
                abort_guard.armed = false;
                return;
            }
            if spins < 256 {
                core::hint::spin_loop();
                spins += 1;
            } else {
                let mut g = phase2_lock.lock().unwrap_or_else(|e| e.into_inner());
                while phase2_state.load(Ordering::Acquire) == PHASE1_RUNNING {
                    g = phase2_cv.wait(g).unwrap_or_else(|e| e.into_inner());
                }
                if phase2_state.load(Ordering::Acquire) != PHASE2_READY {
                    abort_guard.armed = false;
                    return;
                }
                break;
            }
        }

        let roots = roots_cell.get().expect("roots ready");
        loop {
            let j = phase2_next.fetch_add(1, Ordering::Relaxed);
            let Some(slot) = wots_sigs.get(j) else {
                break;
            };
            let (addr, index) = layers[j];
            let sig = wots_sign(
                &roots[j],
                sk,
                seed,
                addr.with_type(WOTS_HASH).with_keypair(index),
            );
            slot.set(sig).expect("unique WOTS sign job");
        }
        abort_guard.armed = false;
    };

    crate::pool::execute(threads.min(total_phase1), true, &run);

    let sig_fors = sig_fors_cell.get().expect("FORS sig assembled");
    let xmss_auth = xmss_auth_cell.get().expect("XMSS auth assembled");

    // --- Assemble final FIPS 205 signature ---
    let mut signature = Vec::with_capacity(p.sig_bytes());
    signature.extend_from_slice(r);
    signature.extend_from_slice(sig_fors);
    for j in 0..d {
        signature.extend_from_slice(wots_sigs[j].get().expect("all WOTS sigs filled"));
        for h in 0..hp {
            signature.extend_from_slice(&xmss_auth[j * hp + h]);
        }
    }
    Some(signature)
}
