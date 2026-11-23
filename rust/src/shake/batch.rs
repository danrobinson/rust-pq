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

fn secrets<const N: usize>(seed: &[u8; N], sk: &[u8; N], addr: Adrs, i: usize) -> [[u8; N]; WIDTH] {
    let prf = addr.with_type(WOTS_PRF).with_keypair(addr.keypair);
    let addresses = core::array::from_fn(|lane| prf.with_word2((i + lane) as u32));
    short(seed, &addresses, &[*sk; WIDTH])
}

/// Reuse the fixed address and padding words over a batch of WOTS chains.
fn chains<const N: usize>(
    seed: &[u8; N],
    addr: Adrs,
    i: usize,
    values: &[[u8; N]; WIDTH],
    mut index: [u32; WIDTH],
    end: [u32; WIDTH],
) -> [[u8; N]; WIDTH] {
    let addresses = core::array::from_fn(|lane| addr.with_word2((i + lane) as u32).with_word3(0));
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
        let values = secrets(seed, sk, addr, i);
        let values = chains(seed, addr, i, &values, [0; WIDTH], [W - 1; WIDTH]);
        for v in &values[..(len - i).min(WIDTH)] {
            pk.absorb(v);
        }
    }
    digest(pk)
}

pub(super) fn sign<const N: usize>(
    sk: &[u8; N],
    seed: &[u8; N],
    addr: Adrs,
    digits: &[u32],
) -> Vec<u8> {
    let mut sig = Vec::with_capacity(N * digits.len());
    for i in (0..digits.len()).step_by(WIDTH) {
        let values = secrets(seed, sk, addr, i);
        let end = core::array::from_fn(|lane| digits.get(i + lane).copied().unwrap_or(0));
        let values = chains(seed, addr, i, &values, [0; WIDTH], end);
        for v in &values[..(digits.len() - i).min(WIDTH)] {
            sig.extend_from_slice(v);
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
    let mut pk = start(seed, &addr.with_type(WOTS_PK).with_keypair(addr.keypair));
    for i in (0..digits.len()).step_by(WIDTH) {
        let values = core::array::from_fn(|lane| {
            if i + lane < digits.len() {
                block(sig, i + lane)
            } else {
                [0; N]
            }
        });
        let index = core::array::from_fn(|lane| digits.get(i + lane).copied().unwrap_or(W - 1));
        let values = chains(seed, addr, i, &values, index, [W - 1; WIDTH]);
        for v in &values[..(digits.len() - i).min(WIDTH)] {
            pk.absorb(v);
        }
    }
    digest(pk)
}
