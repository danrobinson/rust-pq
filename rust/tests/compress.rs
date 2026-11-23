//! The two functions the `hw-sha2` backend stands in for, against an
//! independent implementation of the compression function (the `sha2`
//! crate's): `sha256::compress` on random states and blocks, and
//! `hash::chain_blocks` on random blocks, step ranges and batch sizes.
//!
//! In this tree `chain_blocks` is generic in the hash length `N`: a step
//! keeps the first `N` bytes of the digest (16, 24 or 32) at bytes 22..22 + N.
//! Every test of the chain runs at all three.
//!
//! Run both ways: `cargo test` checks the portable (verified) code, and
//! `cargo test --features hw-sha2` checks the hardware backend.

use sha2::digest::generic_array::GenericArray;

/// SplitMix64: a small deterministic generator, so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    fn fill(&mut self, out: &mut [u8]) {
        for b in out.iter_mut() {
            *b = self.next() as u8;
        }
    }
}

fn reference(state: &[u32; 8], block: &[u8; 64]) -> [u32; 8] {
    let mut st = *state;
    sha2::compress256(&mut st, &[GenericArray::clone_from_slice(block)]);
    st
}

#[test]
fn compress_matches_reference_on_random_inputs() {
    let mut rng = Rng(0x5348_4132_3536);
    // A buffer longer than one block, so that non-zero offsets are exercised.
    let mut data = [0u8; 64 + 37];
    for case in 0..200_000u32 {
        let mut state = [0u32; 8];
        for s in state.iter_mut() {
            *s = rng.next() as u32;
        }
        rng.fill(&mut data);
        let off = (case % 38) as usize;
        let block: [u8; 64] = data[off..off + 64].try_into().unwrap();
        assert_eq!(slhdsa::sha256::compress(&state, &data, off), reference(&state, &block), "case {case}");
    }
}

#[test]
fn compress_matches_reference_on_edge_inputs() {
    let states = [[0u32; 8], [u32::MAX; 8], slhdsa::sha256::H0, [0x8000_0000; 8], [1; 8]];
    let mut blocks = vec![[0u8; 64], [0xff; 64], [0x80; 64], [0x7f; 64]];
    // One set bit at every position, and one cleared bit at every position.
    for bit in 0..512 {
        let mut one = [0u8; 64];
        one[bit / 8] = 1 << (bit % 8);
        blocks.push(one);
        let mut all_but_one = [0xffu8; 64];
        all_but_one[bit / 8] ^= 1 << (bit % 8);
        blocks.push(all_but_one);
    }
    for state in &states {
        for block in &blocks {
            assert_eq!(slhdsa::sha256::compress(state, block, 0), reference(state, block));
        }
    }
}

#[test]
#[should_panic]
fn compress_panics_past_the_end() {
    let data = [0u8; 100];
    let _ = slhdsa::sha256::compress(&slhdsa::sha256::H0, &data, 37);
}

/// What `chain_blocks` is specified to do, written with the reference
/// compression: block `i` takes steps `start[i]..end[i]`; a step writes its
/// number at bytes 18..22 and then replaces bytes 22..22 + N by the first N
/// bytes of the digest of the block's compression.
fn chain_reference<const N: usize>(state: &[u32; 8], blocks: &mut [[u8; 64]], start: &[u32], end: &[u32]) {
    for i in 0..blocks.len() {
        let mut t = start[i];
        while t < end[i] {
            blocks[i][18..22].copy_from_slice(&t.to_be_bytes());
            let st = reference(state, &blocks[i]);
            for w in 0..N / 4 {
                blocks[i][22 + 4 * w..26 + 4 * w].copy_from_slice(&st[w].to_be_bytes());
            }
            t += 1;
        }
    }
}

/// One random case: `n` blocks, each with a step range drawn by `range`, and
/// with first 16 bytes drawn by `head` (the backend caches work that depends
/// only on those bytes, so equal and unequal neighbours both matter).
fn chain_case<const N: usize>(
    rng: &mut Rng,
    n: usize,
    range: &mut dyn FnMut(&mut Rng, usize) -> (u32, u32),
    head: &mut dyn FnMut(&mut Rng, usize, &mut [u8; 16]),
    what: &str,
) {
    let mut state = [0u32; 8];
    for s in state.iter_mut() {
        *s = rng.next() as u32;
    }
    let mut blocks = vec![[0u8; 64]; n];
    let mut start = vec![0u32; n];
    let mut end = vec![0u32; n];
    for i in 0..n {
        rng.fill(&mut blocks[i]);
        let mut h: [u8; 16] = blocks[i][0..16].try_into().unwrap();
        head(rng, i, &mut h);
        blocks[i][0..16].copy_from_slice(&h);
        (start[i], end[i]) = range(rng, i);
    }
    // Slices longer than `blocks` are allowed.
    if rng.next() % 2 == 0 {
        start.push(7);
        end.push(9);
    }
    let mut want = blocks.clone();
    chain_reference::<N>(&state, &mut want, &start, &end);
    slhdsa::hash::chain_blocks::<N>(&state, &mut blocks, &start, &end);
    for i in 0..n {
        assert_eq!(blocks[i], want[i], "N = {N}, {what}: {n} blocks, block {i}, steps {}..{}", start[i], end[i]);
    }
}

/// Step ranges of every kind the crate uses and more: none, one, fifteen,
/// mixed lengths, empty and reversed ranges, and counters around the points
/// where the step number carries from one byte or word of the block into
/// the next.
#[test]
fn chain_blocks_matches_reference_16() {
    chain_blocks_matches_reference::<16>()
}

#[test]
fn chain_blocks_matches_reference_24() {
    chain_blocks_matches_reference::<24>()
}

#[test]
fn chain_blocks_matches_reference_32() {
    chain_blocks_matches_reference::<32>()
}

fn chain_blocks_matches_reference<const N: usize>() {
    let mut rng = Rng(0x4348_4149_4e53 + N as u64);
    let bases: [u32; 9] = [0, 1, 250, 0xfff8, 0xffff, 0x1_0000, 0xff_fff8, 0x7fff_fff8, u32::MAX - 20];
    let mut random_head = |rng: &mut Rng, _i: usize, h: &mut [u8; 16]| rng.fill(h);
    let mut same_head = |_rng: &mut Rng, _i: usize, h: &mut [u8; 16]| *h = [0x5a; 16];
    let mut mixed_head = |rng: &mut Rng, i: usize, h: &mut [u8; 16]| {
        if i % 3 == 0 {
            rng.fill(h)
        } else {
            *h = [(i / 5) as u8; 16]
        }
    };
    for round in 0..40u32 {
        for n in (0..=41usize).chain([64, 70, 128, 140]) {
            // As in WOTS+ key generation: every chain takes the same steps.
            chain_case::<N>(&mut rng, n, &mut |_, _| (0, 15), &mut same_head, "uniform 0..15");
            // As in WOTS+ signing and verification: mixed lengths.
            chain_case::<N>(
                &mut rng,
                n,
                &mut |rng, _| {
                    let d = (rng.next() % 16) as u32;
                    if round % 2 == 0 { (0, d) } else { (d, 15) }
                },
                &mut same_head,
                "mixed lengths",
            );
            // As in FORS and the tree levels: one step each, numbered by an index.
            chain_case::<N>(
                &mut rng,
                n,
                &mut |rng, i| {
                    let t = (rng.next() as u32 % 60000) + i as u32;
                    (t, t + 1)
                },
                &mut mixed_head,
                "single steps",
            );
            // Anything: empty and reversed ranges, counters near carries.
            chain_case::<N>(
                &mut rng,
                n,
                &mut |rng, _| {
                    let s = bases[(rng.next() % 9) as usize].wrapping_add((rng.next() % 12) as u32);
                    let len = (rng.next() % 22) as u32;
                    match rng.next() % 8 {
                        0 => (s, s),
                        1 => (s, s.saturating_sub(3)),
                        _ => (s, s.saturating_add(len)),
                    }
                },
                &mut random_head,
                "random",
            );
        }
    }
}

/// Chains in one batch must not influence each other: the same block with
/// the same steps gives the same result at any position, next to anything.
#[test]
fn chain_blocks_chains_are_independent() {
    chains_are_independent::<16>();
    chains_are_independent::<24>();
    chains_are_independent::<32>();
}

fn chains_are_independent<const N: usize>() {
    let mut rng = Rng(0x4c41_4e45 + N as u64);
    let state = slhdsa::sha256::H0;
    let mut probe = [0u8; 64];
    rng.fill(&mut probe);
    let mut want = [probe];
    chain_reference::<N>(&state, &mut want, &[3], &[11]);
    for n in 1..=12usize {
        for pos in 0..n {
            let mut blocks = vec![[0u8; 64]; n];
            let mut start = vec![0u32; n];
            let mut end = vec![0u32; n];
            for i in 0..n {
                rng.fill(&mut blocks[i]);
                start[i] = (rng.next() % 9) as u32;
                end[i] = start[i] + (rng.next() % 17) as u32;
            }
            blocks[pos] = probe;
            start[pos] = 3;
            end[pos] = 11;
            slhdsa::hash::chain_blocks::<N>(&state, &mut blocks, &start, &end);
            assert_eq!(blocks[pos], want[0], "N = {N}, batch of {n}, position {pos}");
        }
    }
}

#[test]
#[should_panic]
fn chain_blocks_panics_if_a_range_is_missing() {
    let mut blocks = [[0u8; 64]; 5];
    slhdsa::hash::chain_blocks::<16>(&slhdsa::sha256::H0, &mut blocks, &[0; 5], &[1; 4]);
}

/// With the feature on, the backend must be in use exactly when the CPU has
/// the instructions: otherwise the tests above would be checking the portable
/// code twice.
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64"))]
#[test]
fn hardware_backend_is_active_where_the_cpu_has_it() {
    let cpu_has_it = std::arch::is_aarch64_feature_detected!("sha2");
    assert_eq!(slhdsa::sha256::hw_active(), cpu_has_it);
    // Every Apple Silicon CPU has it; a failure here means detection is broken.
    #[cfg(target_vendor = "apple")]
    assert!(cpu_has_it);
}

/// The SHA-512 compression function (portable in every build) against the
/// `sha2` crate's, at offsets inside a longer buffer.
#[test]
fn sha512_compress_matches_reference() {
    let mut rng = Rng(0x5348_4135_3132);
    let mut data = [0u8; 128 + 41];
    for case in 0..50_000u32 {
        let mut state = [0u64; 8];
        for s in state.iter_mut() {
            *s = rng.next();
        }
        rng.fill(&mut data);
        let off = (case % 42) as usize;
        let mut want = state;
        sha2::compress512(&mut want, &[GenericArray::clone_from_slice(&data[off..off + 128])]);
        assert_eq!(slhdsa::sha512::compress(&state, &data, off), want, "case {case}");
    }
}

#[test]
#[should_panic]
fn chain_blocks_panics_if_a_range_is_missing_32() {
    let mut blocks = [[0u8; 64]; 5];
    slhdsa::hash::chain_blocks::<32>(&slhdsa::sha256::H0, &mut blocks, &[0; 4], &[1; 5]);
}

/// With `hw-sha2`, the SHA-512 backend must be in use exactly when the CPU
/// has the instructions.
#[cfg(all(feature = "hw-sha2", target_arch = "aarch64"))]
#[test]
fn sha512_hardware_backend_is_active_where_the_cpu_has_it() {
    let cpu_has_it = std::arch::is_aarch64_feature_detected!("sha3");
    assert_eq!(slhdsa::sha512::hw_active(), cpu_has_it);
    #[cfg(target_vendor = "apple")]
    assert!(cpu_has_it);
}

/// Exercise continuation from a non-initial midstate, short final blocks,
/// both padding lengths, and the odd and even block counts in the x86 backend.
#[test]
fn continued_hashes_match_at_block_and_padding_boundaries() {
    use sha2::{Digest, Sha256, Sha512};
    let mut bytes = vec![0; 3 * 1024 + 257];
    Rng(0x434f_4e54).fill(&mut bytes);
    let s256 = slhdsa::sha256::compress_portable(&slhdsa::sha256::H0, &bytes, 0);
    let s512 = slhdsa::sha512::compress_portable(&slhdsa::sha512::H0, &bytes, 0);
    for end in (128..=128 * 8 + 1).chain((1..=3).flat_map(|groups| {
        [64, 128].into_iter().flat_map(move |prefix| {
            let boundary = prefix + groups * 1024;
            [boundary - 1, boundary, boundary + 1, boundary + 127]
        })
    })) {
        assert_eq!(slhdsa::sha256::sha256_from(&s256, 64, &bytes[64..end]),
                   Sha256::digest(&bytes[..end]).as_slice(), "SHA-256, length {end}");
        assert_eq!(slhdsa::sha512::sha512_from(&s512, 128, &bytes[128..end]),
                   Sha512::digest(&bytes[..end]).as_slice(), "SHA-512, length {end}");
    }
}
