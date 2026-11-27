#![no_std]
#[path="ADDRESS_PATH"] mod address;
use address::{Adrs,TREE};
const WIDTH: usize = 8;

extern "C" {
    fn proof_leaves(out: *mut u8, sk: *const u8, seed: *const u8, first: u32, addr: *const u8);
    fn proof_pairs(out: *mut u8, seed: *const u8, addr: *const u8, left: *const u8, right: *const u8, count: usize);
    fn proof_parent(out: *mut u8, seed: *const u8, addr: *const u8, left: *const u8, right: *const u8);
}
fn wots_leaves_batch<const N: usize>(sk: &[u8;N], seed: &[u8;N], first: u32, a: Adrs) -> [[u8;N];WIDTH] {
    let mut result = [[0;N];WIDTH];
    unsafe { proof_leaves(result.as_mut_ptr().cast(), sk.as_ptr(), seed.as_ptr(), first, a.full().as_ptr()); }
    result
}
fn pair_active<const N: usize>(seed: &[u8;N], a: &[Adrs;WIDTH], left: &[[u8;N];WIDTH],
    right: &[[u8;N];WIDTH], count: usize) -> [[u8;N];WIDTH] {
    let mut result = [[0;N];WIDTH];
    let addresses = a.map(|x| x.full());
    unsafe { proof_pairs(result.as_mut_ptr().cast(), seed.as_ptr(), addresses.as_ptr().cast(),
        left.as_ptr().cast(), right.as_ptr().cast(), count); }
    result
}
fn thash_pair<const N: usize>(seed: &[u8;N], a: &Adrs, left: &[u8;N], right: &[u8;N]) -> [u8;N] {
    let mut result = [0;N];
    unsafe { proof_parent(result.as_mut_ptr(),seed.as_ptr(),a.full().as_ptr(),left.as_ptr(),right.as_ptr()); }
    result
}
fn xmss_subtree_fallback<const N: usize>(_: &[u8;N], _: &[u8;N], _:u32, _:u32, _:Adrs) -> [u8;N] { unreachable!() }
fn wots_leaves_small<const N: usize,const K:usize>(_: &[u8;N], _: &[u8;N], _:u32, _:Adrs) -> [[u8;N];K] { unreachable!() }
// PRODUCTION
