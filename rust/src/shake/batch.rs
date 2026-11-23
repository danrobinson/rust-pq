//! One Keccak state per independent address. Short FIPS 205 inputs fit one rate block.
use super::hash::{digest, start};
use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
use crate::params::{LEN2, W};
use crate::shake256::parallel::{self, States, WIDTH};
use crate::util::block;
use alloc::vec::Vec;

pub(super) fn available<const N: usize>() -> bool {
    matches!(N, 16 | 24 | 32) && parallel::available()
}

fn word(input: &[u8], i: usize) -> u64 {
    u64::from_le_bytes(input[i * 8..i * 8 + 8].try_into().unwrap())
}

fn header<const N: usize>(seed: &[u8; N], addresses: &[Adrs; WIDTH], size: usize) -> States {
    let mut s = [[0; WIDTH]; 25];
    for i in 0..N / 8 {
        s[i] = [word(seed, i); WIDTH];
    }
    for lane in 0..WIDTH {
        let addr = addresses[lane].full();
        for j in 0..4 {
            s[N / 8 + j][lane] = word(&addr, j);
        }
    }
    // All three digest widths and the address are whole numbers of lanes.
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
    let mut values = [[0; N]; WIDTH];
    for i in 0..N / 8 {
        for lane in 0..WIDTH {
            values[lane][8 * i..8 * i + 8].copy_from_slice(&s[i][lane].to_le_bytes());
        }
    }
    values
}

pub(super) fn short<const N: usize>(
    seed: &[u8; N],
    addresses: &[Adrs; WIDTH],
    values: &[[u8; N]; WIDTH],
) -> [[u8; N]; WIDTH] {
    let mut s = header(seed, addresses, 2 * N + 32);
    put(&mut s, N / 8 + 4, values);
    parallel::permute(&mut s);
    read(&s)
}

pub(super) fn pair<const N: usize>(
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

/// Reuse the fixed address and padding words over a batch of WOTS chains.
fn chains<const N: usize>(
    seed: &[u8; N],
    addr: Adrs,
    ids: [usize; WIDTH],
    values: &[[u8; N]; WIDTH],
    mut index: [u32; WIDTH],
    end: [u32; WIDTH],
) -> [[u8; N]; WIDTH] {
    let addresses = core::array::from_fn(|lane| addr.with_word2(ids[lane] as u32).with_word3(0));
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
    let mut result = [[0; N]; WIDTH];
    for j in 0..N / 8 {
        for lane in 0..WIDTH {
            result[lane][8 * j..8 * j + 8].copy_from_slice(&input[offset + j][lane].to_le_bytes());
        }
    }
    result
}

pub(super) fn keygen<const N: usize>(sk: &[u8; N], seed: &[u8; N], addr: Adrs) -> [u8; N] {
    let len = 2 * N + LEN2;
    let mut pk = start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
    for i in (0..len).step_by(WIDTH) {
        let ids = core::array::from_fn(|lane| i + lane);
        let values = secrets(seed, sk, addr, ids);
        let values = chains(seed, addr, ids, &values, [0; WIDTH], [W - 1; WIDTH]);
        for v in &values[..(len - i).min(WIDTH)] {
            pk.absorb(v);
        }
    }
    digest(pk)
}

/// Group chains with similar lengths so each SIMD register spends fewer
/// iterations waiting for its longest chain. Output is scattered by chain ID.
fn chain_order(digits: &[u32]) -> [usize; 67] {
    let mut offsets = [0; 16];
    for &digit in digits {
        offsets[digit as usize] += 1;
    }
    let mut start = 0;
    for offset in &mut offsets {
        let count = *offset;
        *offset = start;
        start += count;
    }
    let mut order = [0; 67];
    for (index, &digit) in digits.iter().enumerate() {
        let at = &mut offsets[digit as usize];
        order[*at] = index;
        *at += 1;
    }
    order
}

pub(super) fn sign<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    digits: &[u32],
) -> Vec<u8> {
    let order = chain_order(digits);
    let mut sig = alloc::vec![0; N*digits.len()];
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

pub(super) fn recover<const N: usize>(
    sig: &[u8],
    seed: &[u8; N],
    addr: Adrs,
    digits: &[u32],
) -> [u8; N] {
    let order = chain_order(digits);
    let mut endpoints = [[0; N]; 67];
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
    let mut pk = start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
    for key in &endpoints[..digits.len()] {
        pk.absorb(key);
    }
    digest(pk)
}
