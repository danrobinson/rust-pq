//! One Keccak state per independent address. Short FIPS 205 inputs fit one rate block.
use super::hash::{digest, start, thash_pair};
use crate::address::{Adrs, TREE, WOTS_HASH, WOTS_PK, WOTS_PRF};
use crate::params::{Params, LEN2, LEN_MAX, W};
use crate::shake256::parallel::{self, States, WIDTH};
use crate::util::block;
use crate::wots::wots_digits;
use alloc::vec::Vec;

pub(super) fn available<const N: usize>() -> bool {
    matches!(N, 16 | 24 | 32) && parallel::available()
}

#[inline(always)]
fn word(input: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(input[i * 8..i * 8 + 8].try_into().unwrap())
}

#[inline(always)]
pub(super) fn seed_words<const N: usize>(seed: &[u8; N]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for i in 0..N / 8 {
        out[i] = word(seed, i);
    }
    out
}

#[inline(always)]
pub(super) fn adrs_words(adrs: &Adrs) -> [u64; 4] {
    [
        u64::from(adrs.layer.swap_bytes()),
        adrs.tree.swap_bytes(),
        u64::from(adrs.typ.swap_bytes()) | (u64::from(adrs.keypair.swap_bytes()) << 32),
        u64::from(adrs.word2.swap_bytes()) | (u64::from(adrs.word3.swap_bytes()) << 32),
    ]
}

fn header_active<const N: usize>(
    seed: &[u8; N],
    addresses: &[Adrs; WIDTH],
    size: usize,
    active: usize,
) -> States {
    let mut s = [[0; WIDTH]; 25];
    let sw = seed_words(seed);
    for i in 0..N / 8 {
        s[i] = [sw[i]; WIDTH];
    }
    for lane in 0..active {
        let aw = adrs_words(&addresses[lane]);
        for j in 0..4 {
            s[N / 8 + j][lane] = aw[j];
        }
    }
    // All three digest widths and the address are whole numbers of lanes.
    s[size / 8] = [0x1f; WIDTH];
    for v in &mut s[16] {
        *v |= 1 << 63;
    }
    s
}

#[inline(always)]
fn put_active<const N: usize>(
    s: &mut States,
    offset: usize,
    values: &[[u8; N]; WIDTH],
    active: usize,
) {
    for i in 0..N / 8 {
        for lane in 0..active {
            s[offset + i][lane] = word(&values[lane], i);
        }
    }
}

#[inline(always)]
fn read_active<const N: usize>(s: &States, active: usize) -> [[u8; N]; WIDTH] {
    let mut values = [[0; N]; WIDTH];
    for i in 0..N / 8 {
        for lane in 0..active {
            values[lane][8 * i..8 * i + 8].copy_from_slice(&s[i][lane].to_le_bytes());
        }
    }
    values
}

#[inline(always)]
fn extract_lane<const N: usize>(s: &States, word_offset: usize, lane: usize) -> [u8; N] {
    let mut out = [0u8; N];
    for j in 0..N / 8 {
        out[8 * j..8 * j + 8].copy_from_slice(&s[word_offset + j][lane].to_le_bytes());
    }
    out
}

pub(super) fn short_active<const N: usize>(
    seed: &[u8; N],
    addresses: &[Adrs; WIDTH],
    values: &[[u8; N]; WIDTH],
    active: usize,
) -> [[u8; N]; WIDTH] {
    let mut s = header_active(seed, addresses, 2 * N + 32, active);
    put_active(&mut s, N / 8 + 4, values, active);
    parallel::permute_active(&mut s, active);
    read_active(&s, active)
}

pub(super) fn pair_active<const N: usize>(
    seed: &[u8; N],
    addresses: &[Adrs; WIDTH],
    left: &[[u8; N]; WIDTH],
    right: &[[u8; N]; WIDTH],
    active: usize,
) -> [[u8; N]; WIDTH] {
    let mut s = header_active(seed, addresses, 3 * N + 32, active);
    put_active(&mut s, N / 8 + 4, left, active);
    put_active(&mut s, 2 * N / 8 + 4, right, active);
    parallel::permute_active(&mut s, active);
    read_active(&s, active)
}

/// Refill a Keccak state in place for the next `2*N + 32`-byte SHAKE256 call:
/// copies output words `0..N/8` to `offset..offset+N/8`, writes the prefix words,
/// zeroes the remaining rate/capacity words, and sets the SHAKE256 padding bits.
#[inline(always)]
fn refill_short_inplace<const N: usize>(
    state: &mut States,
    sw: &[u64; 4],
    w0: u64,
    w1: u64,
    w2: &[u64; WIDTH],
    w3: &[u64; WIDTH],
) {
    let n = N / 8;
    let offset = n + 4;
    for j in 0..n {
        state[offset + j] = state[j];
        state[j] = [sw[j]; WIDTH];
    }
    state[n] = [w0; WIDTH];
    state[n + 1] = [w1; WIDTH];
    state[n + 2] = *w2;
    state[n + 3] = *w3;
    let pad = offset + n;
    state[pad] = [0x1f; WIDTH];
    for w in &mut state[pad + 1..25] {
        *w = [0; WIDTH];
    }
    state[16] = [1u64 << 63; WIDTH];
}

/// Fill a fresh Keccak state for a `2*N + 32`-byte SHAKE256 call with fixed `sk` payload.
#[inline(always)]
fn fill_prf<const N: usize>(
    state: &mut States,
    sw: &[u64; 4],
    skw: &[u64; 4],
    w0: u64,
    w1: u64,
    w2: &[u64; WIDTH],
    w3: &[u64; WIDTH],
) {
    let n = N / 8;
    let offset = n + 4;
    for j in 0..n {
        state[j] = [sw[j]; WIDTH];
        state[offset + j] = [skw[j]; WIDTH];
    }
    state[n] = [w0; WIDTH];
    state[n + 1] = [w1; WIDTH];
    state[n + 2] = *w2;
    state[n + 3] = *w3;
    let pad = offset + n;
    state[pad] = [0x1f; WIDTH];
    for w in &mut state[pad + 1..25] {
        *w = [0; WIDTH];
    }
    state[16] = [1u64 << 63; WIDTH];
}

/// Single WOTS+ keygen: batch `WIDTH` chains at a time, using `permute_active` on the
/// final partial batch (exact 3-way batch on Apple Silicon for `len = 35, 51, 67`).
pub(super) fn keygen<const N: usize>(sk: &[u8; N], seed: &[u8; N], addr: Adrs) -> [u8; N] {
    let len = 2 * N + LEN2;
    let sw = seed_words(seed);
    let skw = seed_words(sk);
    let aw_prf = adrs_words(&addr.with_type(WOTS_PRF).with_keypair(addr.keypair));
    let aw_hash = adrs_words(&addr.with_type(WOTS_HASH).with_keypair(addr.keypair));
    let w2_prf = [aw_prf[2]; WIDTH];
    let w2_hash = [aw_hash[2]; WIDTH];
    let mut state: States = [[0; WIDTH]; 25];
    let mut pk = start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));

    for i in (0..len).step_by(WIDTH) {
        let active = (len - i).min(WIDTH);
        let ids: [u64; WIDTH] =
            core::array::from_fn(|lane| u64::from(((i + lane.min(active - 1)) as u32).swap_bytes()));
        fill_prf::<N>(&mut state, &sw, &skw, aw_prf[0], aw_prf[1], &w2_prf, &ids);
        parallel::permute_active(&mut state, active);
        for step in 0..W - 1 {
            let step_hi = u64::from(step.swap_bytes()) << 32;
            let w3 = ids.map(|id| id | step_hi);
            refill_short_inplace::<N>(&mut state, &sw, aw_hash[0], aw_hash[1], &w2_hash, &w3);
            parallel::permute_active(&mut state, active);
        }
        for lane in 0..active {
            pk.absorb(&extract_lane::<N>(&state, 0, lane));
        }
    }
    digest(pk)
}

/// Counting sort of chain indices by descending step count (longest chains first).
/// Returns `(order, count)` containing only chains with `steps[i] > 0`.
fn sort_descending(steps: &[u32]) -> ([usize; LEN_MAX], usize) {
    let mut counts = [0usize; 16];
    let mut total = 0usize;
    for &s in steps {
        if s > 0 {
            counts[s as usize] += 1;
            total += 1;
        }
    }
    let mut offsets = [0usize; 16];
    let mut pos = 0usize;
    for b in (1..16).rev() {
        offsets[b] = pos;
        pos += counts[b];
    }
    let mut order = [0usize; LEN_MAX];
    for (idx, &s) in steps.iter().enumerate() {
        if s > 0 {
            let slot = &mut offsets[s as usize];
            order[*slot] = idx;
            *slot += 1;
        }
    }
    (order, total)
}

/// Dynamic lane-refill WOTS+ signing: computes all `WOTS_PRF` secrets in batches of `WIDTH`,
/// then runs chains with immediate lane refill as each chain completes.
pub(super) fn sign<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    digits: &[u32],
) -> Vec<u8> {
    let len = digits.len();
    let n = N / 8;
    let offset = n + 4;
    let sw = seed_words(seed);
    let skw = seed_words(sk);
    let aw_prf = adrs_words(&addr.with_type(WOTS_PRF).with_keypair(addr.keypair));
    let aw_hash = adrs_words(&addr.with_type(WOTS_HASH).with_keypair(addr.keypair));
    let w2_prf = [aw_prf[2]; WIDTH];

    let mut sig = alloc::vec![0u8; N * len];
    let mut secrets_words = [[0u64; 4]; LEN_MAX];
    let mut state: States = [[0; WIDTH]; 25];

    // Step 1: generate all `len` WOTS_PRF secrets at full width (+ exact tail).
    for i in (0..len).step_by(WIDTH) {
        let active = (len - i).min(WIDTH);
        let ids: [u64; WIDTH] =
            core::array::from_fn(|lane| u64::from(((i + lane.min(active - 1)) as u32).swap_bytes()));
        fill_prf::<N>(&mut state, &sw, &skw, aw_prf[0], aw_prf[1], &w2_prf, &ids);
        parallel::permute_active(&mut state, active);
        for lane in 0..active {
            let id = i + lane;
            if digits[id] == 0 {
                sig[id * N..(id + 1) * N].copy_from_slice(&extract_lane::<N>(&state, 0, lane));
            } else {
                for j in 0..n {
                    secrets_words[id][j] = state[j][lane];
                }
            }
        }
    }

    // Step 2: dynamic lane refill over chains with `digits[id] > 0`, longest first.
    let (order, total) = sort_descending(digits);
    let mut next = 0usize;
    let mut active = total.min(WIDTH);
    let mut lane_id = [0usize; WIDTH];
    let mut lane_step = [0u32; WIDTH];
    let mut lane_end = [0u32; WIDTH];
    let mut lane_val = [[0u64; 4]; WIDTH];

    for lane in 0..active {
        let id = order[next];
        next += 1;
        lane_id[lane] = id;
        lane_step[lane] = 0;
        lane_end[lane] = digits[id];
        lane_val[lane] = secrets_words[id];
    }

    let pad = offset + n;
    while active > 0 {
        for j in 0..n {
            state[j] = [sw[j]; WIDTH];
            for lane in 0..active {
                state[offset + j][lane] = lane_val[lane][j];
            }
        }
        state[n] = [aw_hash[0]; WIDTH];
        state[n + 1] = [aw_hash[1]; WIDTH];
        state[n + 2] = [aw_hash[2]; WIDTH];
        for lane in 0..active {
            state[n + 3][lane] = u64::from((lane_id[lane] as u32).swap_bytes())
                | (u64::from(lane_step[lane].swap_bytes()) << 32);
        }
        state[pad] = [0x1f; WIDTH];
        for w in &mut state[pad + 1..25] {
            *w = [0; WIDTH];
        }
        state[16] = [1u64 << 63; WIDTH];

        parallel::permute_active(&mut state, active);

        let mut lane = 0;
        while lane < active {
            lane_step[lane] += 1;
            if lane_step[lane] == lane_end[lane] {
                let id = lane_id[lane];
                sig[id * N..(id + 1) * N].copy_from_slice(&extract_lane::<N>(&state, 0, lane));
                if next < total {
                    let nid = order[next];
                    next += 1;
                    lane_id[lane] = nid;
                    lane_step[lane] = 0;
                    lane_end[lane] = digits[nid];
                    lane_val[lane] = secrets_words[nid];
                    lane += 1;
                } else {
                    active -= 1;
                    if lane < active {
                        lane_id[lane] = lane_id[active];
                        lane_step[lane] = lane_step[active];
                        lane_end[lane] = lane_end[active];
                        for j in 0..n {
                            state[j][lane] = state[j][active];
                        }
                    }
                }
            } else {
                for j in 0..n {
                    lane_val[lane][j] = state[j][lane];
                }
                lane += 1;
            }
        }
    }
    sig
}

/// Dynamic lane-refill WOTS+ public key recovery (used in verification and hypertree signing).
pub(super) fn recover<const N: usize>(
    sig: &[u8],
    seed: &[u8; N],
    addr: Adrs,
    digits: &[u32],
) -> [u8; N] {
    let len = digits.len();
    let n = N / 8;
    let offset = n + 4;
    let sw = seed_words(seed);
    let aw_hash = adrs_words(&addr.with_type(WOTS_HASH).with_keypair(addr.keypair));

    let mut endpoints = [[0u8; N]; LEN_MAX];
    let mut rem_steps = [0u32; LEN_MAX];
    for i in 0..len {
        let rem = (W - 1) - digits[i];
        rem_steps[i] = rem;
        if rem == 0 {
            endpoints[i] = block(sig, i);
        }
    }

    let (order, total) = sort_descending(&rem_steps[..len]);
    let mut next = 0usize;
    let mut active = total.min(WIDTH);
    let mut lane_id = [0usize; WIDTH];
    let mut lane_step = [0u32; WIDTH];
    let mut lane_val = [[0u64; 4]; WIDTH];

    for lane in 0..active {
        let id = order[next];
        next += 1;
        lane_id[lane] = id;
        lane_step[lane] = digits[id];
        let blk = &sig[id * N..(id + 1) * N];
        for j in 0..n {
            lane_val[lane][j] = word(blk, j);
        }
    }

    let mut state: States = [[0; WIDTH]; 25];
    let pad = offset + n;
    while active > 0 {
        for j in 0..n {
            state[j] = [sw[j]; WIDTH];
            for lane in 0..active {
                state[offset + j][lane] = lane_val[lane][j];
            }
        }
        state[n] = [aw_hash[0]; WIDTH];
        state[n + 1] = [aw_hash[1]; WIDTH];
        state[n + 2] = [aw_hash[2]; WIDTH];
        for lane in 0..active {
            state[n + 3][lane] = u64::from((lane_id[lane] as u32).swap_bytes())
                | (u64::from(lane_step[lane].swap_bytes()) << 32);
        }
        state[pad] = [0x1f; WIDTH];
        for w in &mut state[pad + 1..25] {
            *w = [0; WIDTH];
        }
        state[16] = [1u64 << 63; WIDTH];

        parallel::permute_active(&mut state, active);

        let mut lane = 0;
        while lane < active {
            lane_step[lane] += 1;
            if lane_step[lane] == W - 1 {
                let id = lane_id[lane];
                endpoints[id] = extract_lane::<N>(&state, 0, lane);
                if next < total {
                    let nid = order[next];
                    next += 1;
                    lane_id[lane] = nid;
                    lane_step[lane] = digits[nid];
                    let blk = &sig[nid * N..(nid + 1) * N];
                    for j in 0..n {
                        lane_val[lane][j] = word(blk, j);
                    }
                    lane += 1;
                } else {
                    active -= 1;
                    if lane < active {
                        lane_id[lane] = lane_id[active];
                        lane_step[lane] = lane_step[active];
                        for j in 0..n {
                            state[j][lane] = state[j][active];
                        }
                    }
                }
            } else {
                for j in 0..n {
                    lane_val[lane][j] = state[j][lane];
                }
                lane += 1;
            }
        }
    }

    let mut pk = start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
    for key in &endpoints[..len] {
        pk.absorb(key);
    }
    digest(pk)
}

/// Compute `WIDTH` full WOTS+ leaf public keys (`first_key .. first_key + WIDTH`) in lockstep,
/// fusing `WOTS_PRF`, all 15 `WOTS_HASH` chain steps, and the multi-block `WOTS_PK` sponge.
fn wots_leaves_batch<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    first_key: u32,
    addr: Adrs,
) -> [[u8; N]; WIDTH] {
    let n = N / 8;
    let offset = n + 4;
    let sw = seed_words(seed);
    let skw = seed_words(sk);
    let base = adrs_words(&addr);
    let w0 = base[0];
    let w1 = base[1];
    let w2_pk: [u64; WIDTH] = core::array::from_fn(|lane| {
        u64::from(WOTS_PK.swap_bytes())
            | (u64::from((first_key + lane as u32).swap_bytes()) << 32)
    });
    let w2_prf: [u64; WIDTH] = core::array::from_fn(|lane| {
        u64::from(WOTS_PRF.swap_bytes())
            | (u64::from((first_key + lane as u32).swap_bytes()) << 32)
    });
    let w2_hash: [u64; WIDTH] = core::array::from_fn(|lane| {
        u64::from(WOTS_HASH.swap_bytes())
            | (u64::from((first_key + lane as u32).swap_bytes()) << 32)
    });

    // Initialize the WIDTH-way WOTS_PK sponge with seed || ADRS(WOTS_PK).
    let mut pk: States = [[0; WIDTH]; 25];
    for j in 0..n {
        pk[j] = [sw[j]; WIDTH];
    }
    pk[n] = [w0; WIDTH];
    pk[n + 1] = [w1; WIDTH];
    pk[n + 2] = w2_pk;
    // pk[n + 3] is 0 (word2 = 0, word3 = 0).
    let mut pos = offset;

    let mut state: States = [[0; WIDTH]; 25];
    for chain in 0..2 * N + LEN2 {
        let id = u64::from((chain as u32).swap_bytes());
        let w3_id = [id; WIDTH];
        fill_prf::<N>(&mut state, &sw, &skw, w0, w1, &w2_prf, &w3_id);
        parallel::permute(&mut state);
        for step in 0..W - 1 {
            let w3 = [id | (u64::from(step.swap_bytes()) << 32); WIDTH];
            refill_short_inplace::<N>(&mut state, &sw, w0, w1, &w2_hash, &w3);
            parallel::permute(&mut state);
        }
        for j in 0..n {
            for lane in 0..WIDTH {
                pk[pos][lane] ^= state[j][lane];
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
        pk[16][lane] ^= 1u64 << 63;
    }
    parallel::permute(&mut pk);
    read_active::<N>(&pk, WIDTH)
}

/// Compute `K` WOTS+ leaf public keys (`K` in `{2, 4}`) in parallel when `WIDTH == 8`,
/// batching chains across all `K` keys at full `WIDTH` and compressing all `K` WOTS_PK
/// sponges concurrently with `permute_active(..., K)`.
fn wots_leaves_small<const N: usize, const K: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    first_key: u32,
    addr: Adrs,
) -> [[u8; N]; K] {
    let len = 2 * N + LEN2;
    let total = K * len;
    let n = N / 8;
    let offset = n + 4;
    let sw = seed_words(seed);
    let skw = seed_words(sk);
    let base = adrs_words(&addr);
    let w0 = base[0];
    let w1 = base[1];

    let mut pk: States = [[0; WIDTH]; 25];
    for j in 0..n {
        pk[j] = [sw[j]; WIDTH];
    }
    pk[n] = [w0; WIDTH];
    pk[n + 1] = [w1; WIDTH];
    for k in 0..K {
        pk[n + 2][k] = u64::from(WOTS_PK.swap_bytes())
            | (u64::from((first_key + k as u32).swap_bytes()) << 32);
    }
    let mut pos = offset;

    let mut state: States = [[0; WIDTH]; 25];
    // Iterate in chain-major order (k varies fastest) so every group of K lanes shares the same
    // chain index and advances `pos` in lockstep. Since `total = K * len` and K divides WIDTH (8),
    // `active` is always a multiple of K.
    let mut idx = 0usize;
    while idx < total {
        let active = (total - idx).min(WIDTH);
        let mut w2_prf = [0u64; WIDTH];
        let mut w2_hash = [0u64; WIDTH];
        let mut w3_id = [0u64; WIDTH];
        for lane in 0..active {
            let flat = idx + lane;
            let chain = flat / K;
            let k = flat % K;
            let kp = (first_key + k as u32).swap_bytes();
            w2_prf[lane] = u64::from(WOTS_PRF.swap_bytes()) | (u64::from(kp) << 32);
            w2_hash[lane] = u64::from(WOTS_HASH.swap_bytes()) | (u64::from(kp) << 32);
            w3_id[lane] = u64::from((chain as u32).swap_bytes());
        }
        fill_prf::<N>(&mut state, &sw, &skw, w0, w1, &w2_prf, &w3_id);
        parallel::permute_active(&mut state, active);
        for step in 0..W - 1 {
            let step_hi = u64::from(step.swap_bytes()) << 32;
            let w3 = w3_id.map(|id| id | step_hi);
            refill_short_inplace::<N>(&mut state, &sw, w0, w1, &w2_hash, &w3);
            parallel::permute_active(&mut state, active);
        }
        for group in (0..active).step_by(K) {
            for j in 0..n {
                for k in 0..K {
                    pk[pos][k] ^= state[j][group + k];
                }
                pos += 1;
                if pos == 17 {
                    parallel::permute_active(&mut pk, K);
                    pos = 0;
                }
            }
        }
        idx += active;
    }
    for k in 0..K {
        pk[pos][k] ^= 0x1f;
        pk[16][k] ^= 1u64 << 63;
    }
    parallel::permute_active(&mut pk, K);
    core::array::from_fn(|k| extract_lane::<N>(&pk, 0, k))
}

/// Batched XMSS subtree root at `(tree_index, height)` for `height >= 1`.
/// For `WIDTH == 8` and `height >= 3`, generates 8 full WOTS keys in lockstep and
/// batches all internal Merkle parent hashes 8-way with zero heap allocation.
pub(super) fn xmss_subtree<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    tree_index: u32,
    height: u32,
    addr: Adrs,
) -> [u8; N] {
    if WIDTH != 8 {
        // Fallback for widths != 8 (e.g. non-Apple AArch64 WIDTH = 3).
        return xmss_subtree_fallback(sk, seed, tree_index, height, addr);
    }
    let tree_adrs = addr.with_type(TREE);
    if height == 1 {
        let leaves = wots_leaves_small::<N, 2>(sk, seed, tree_index * 2, addr);
        let parent = tree_adrs.with_word2(1).with_word3(tree_index);
        return thash_pair(seed, &parent, &leaves[0], &leaves[1]);
    }
    if height == 2 {
        let leaves = wots_leaves_small::<N, 4>(sk, seed, tree_index * 4, addr);
        let mut addrs = [tree_adrs; WIDTH];
        let mut left = [[0u8; N]; WIDTH];
        let mut right = [[0u8; N]; WIDTH];
        for k in 0..2 {
            addrs[k] = tree_adrs.with_word2(1).with_word3(tree_index * 2 + k as u32);
            left[k] = leaves[2 * k];
            right[k] = leaves[2 * k + 1];
        }
        let lvl1 = pair_active(seed, &addrs, &left, &right, 2);
        let root_adrs = tree_adrs.with_word2(2).with_word3(tree_index);
        return thash_pair(seed, &root_adrs, &lvl1[0], &lvl1[1]);
    }

    // height >= 3 (max hp in FIPS 205 is 9; support up to height 16 on stack).
    let z = height as usize;
    debug_assert!(z <= 16);
    let mut buf = [[[0u8; N]; 16]; 17];
    let mut len = [0usize; 17];
    let mut next_idx = [0u32; 17];
    for h in 0..=z {
        next_idx[h] = tree_index << (z - h);
    }

    let blocks = 1u32 << (height - 3);
    let first_leaf = tree_index << height;
    let mut addrs = [tree_adrs; WIDTH];
    let mut left = [[0u8; N]; WIDTH];
    let mut right = [[0u8; N]; WIDTH];

    for b in 0..blocks {
        let leaves = wots_leaves_batch::<N>(sk, seed, first_leaf + b * 8, addr);
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

    // Flush the remaining top levels (at most 8, 4, 2 children at the last 3 levels).
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

fn xmss_subtree_fallback<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    tree_index: u32,
    height: u32,
    addr: Adrs,
) -> [u8; N] {
    if height == 0 {
        keygen(sk, seed, addr.with_type(WOTS_HASH).with_keypair(tree_index))
    } else {
        let left = xmss_subtree_fallback(sk, seed, 2 * tree_index, height - 1, addr);
        let right = xmss_subtree_fallback(sk, seed, 2 * tree_index + 1, height - 1, addr);
        let a = addr
            .with_type(TREE)
            .with_word2(height)
            .with_word3(tree_index);
        thash_pair(seed, &a, &left, &right)
    }
}

/// Fused XMSS signing for `p.hp >= 3` and `WIDTH == 8`: runs the signing leaf's WOTS+
/// signature in lockstep with the 7 sibling leaves of its bottom height-3 subtree (making
/// `wots_sign` effectively free), then computes all higher auth-path nodes via `xmss_subtree`.
pub(super) fn xmss_sign_batch<const N: usize>(
    p: &Params,
    m: &[u8; N],
    sk: &[u8; N],
    idx: u32,
    seed: &[u8; N],
    addr: Adrs,
) -> Vec<u8> {
    let digits = wots_digits(m);
    if WIDTH != 8 {
        let mut sig = sign(sk, seed, addr.with_type(WOTS_HASH).with_keypair(idx), &digits);
        for j in 0..p.hp {
            let k = (idx >> j) ^ 1;
            let node = xmss_subtree_fallback(sk, seed, k, j, addr);
            sig.extend_from_slice(&node);
        }
        return sig;
    }

    let len = digits.len();
    let n = N / 8;
    let offset = n + 4;
    let sw = seed_words(seed);
    let skw = seed_words(sk);
    let base_leaf = idx & !7;
    let sig_lane = (idx & 7) as usize;

    let base_adrs = adrs_words(&addr);
    let w0 = base_adrs[0];
    let w1 = base_adrs[1];
    let w2_pk: [u64; WIDTH] = core::array::from_fn(|lane| {
        u64::from(WOTS_PK.swap_bytes())
            | (u64::from((base_leaf + lane as u32).swap_bytes()) << 32)
    });
    let w2_prf: [u64; WIDTH] = core::array::from_fn(|lane| {
        u64::from(WOTS_PRF.swap_bytes())
            | (u64::from((base_leaf + lane as u32).swap_bytes()) << 32)
    });
    let w2_hash: [u64; WIDTH] = core::array::from_fn(|lane| {
        u64::from(WOTS_HASH.swap_bytes())
            | (u64::from((base_leaf + lane as u32).swap_bytes()) << 32)
    });

    let mut sig = alloc::vec![0u8; p.xmss_sig_bytes()];
    let mut pk: States = [[0; WIDTH]; 25];
    for j in 0..n {
        pk[j] = [sw[j]; WIDTH];
    }
    pk[n] = [w0; WIDTH];
    pk[n + 1] = [w1; WIDTH];
    pk[n + 2] = w2_pk;
    let mut pos = offset;

    let mut state: States = [[0; WIDTH]; 25];
    for chain in 0..len {
        let d = digits[chain];
        let id = u64::from((chain as u32).swap_bytes());
        let w3_id = [id; WIDTH];
        fill_prf::<N>(&mut state, &sw, &skw, w0, w1, &w2_prf, &w3_id);
        parallel::permute(&mut state);
        if d == 0 {
            sig[chain * N..(chain + 1) * N].copy_from_slice(&extract_lane::<N>(&state, 0, sig_lane));
        }
        for step in 0..W - 1 {
            let w3 = [id | (u64::from(step.swap_bytes()) << 32); WIDTH];
            refill_short_inplace::<N>(&mut state, &sw, w0, w1, &w2_hash, &w3);
            parallel::permute(&mut state);
            if step + 1 == d {
                sig[chain * N..(chain + 1) * N]
                    .copy_from_slice(&extract_lane::<N>(&state, 0, sig_lane));
            }
        }
        for j in 0..n {
            for lane in 0..WIDTH {
                pk[pos][lane] ^= state[j][lane];
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
        pk[16][lane] ^= 1u64 << 63;
    }
    parallel::permute(&mut pk);
    let nodes = read_active::<N>(&pk, WIDTH);

    let mut out_pos = len * N;
    // j = 0 auth node
    sig[out_pos..out_pos + N].copy_from_slice(&nodes[sig_lane ^ 1]);
    out_pos += N;

    // j = 1 and j = 2 auth nodes: compute all 3 needed level-1 parents in one 3-way batch.
    let tree_adrs = addr.with_type(TREE);
    let p1 = (sig_lane >> 1) ^ 1;
    let h2 = (sig_lane >> 2) ^ 1;
    let pairs = [p1, 2 * h2, 2 * h2 + 1];
    let mut addrs = [tree_adrs; WIDTH];
    let mut left = [[0u8; N]; WIDTH];
    let mut right = [[0u8; N]; WIDTH];
    for (lane, &pr) in pairs.iter().enumerate() {
        addrs[lane] = tree_adrs
            .with_word2(1)
            .with_word3((base_leaf >> 1) + pr as u32);
        left[lane] = nodes[2 * pr];
        right[lane] = nodes[2 * pr + 1];
    }
    let lvl1 = pair_active(seed, &addrs, &left, &right, 3);
    // j = 1 auth node
    sig[out_pos..out_pos + N].copy_from_slice(&lvl1[0]);
    out_pos += N;
    // j = 2 auth node
    let a2 = tree_adrs
        .with_word2(2)
        .with_word3((base_leaf >> 2) + h2 as u32);
    let auth2 = thash_pair(seed, &a2, &lvl1[1], &lvl1[2]);
    sig[out_pos..out_pos + N].copy_from_slice(&auth2);
    out_pos += N;

    // j = 3 .. p.hp auth nodes via batched xmss_subtree.
    for j in 3..p.hp {
        let node = xmss_subtree(sk, seed, (idx >> j) ^ 1, j, addr);
        sig[out_pos..out_pos + N].copy_from_slice(&node);
        out_pos += N;
    }
    sig
}
