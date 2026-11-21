//! The SHA-256 compression function, one block at a time (`compress`) and
//! many at once (`compress_many`), against an independent implementation
//! (the `sha2` crate's), on random states and blocks.
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

/// `compress_many` on every batch size the crate uses and more: each output
/// is the reference compression of its own block, whatever its position in
/// the batch, and entries of `out` past the batch are left alone.
#[test]
fn compress_many_matches_reference_on_every_batch_size() {
    let mut rng = Rng(0x4d41_4e59);
    for round in 0..400u32 {
        for n in 0..=41usize {
            let mut state = [0u32; 8];
            for s in state.iter_mut() {
                *s = rng.next() as u32;
            }
            let mut blocks = vec![[0u8; 64]; n];
            for b in blocks.iter_mut() {
                rng.fill(b);
            }
            let extra = (round as usize + n) % 3;
            let mut out = vec![[0xa5a5_a5a5u32; 8]; n + extra];
            slhdsa::sha256::compress_many(&state, &blocks, &mut out);
            for i in 0..n {
                assert_eq!(out[i], reference(&state, &blocks[i]), "round {round}, batch of {n}, block {i}");
                assert_eq!(out[i], slhdsa::sha256::compress(&state, &blocks[i], 0));
            }
            for o in &out[n..] {
                assert_eq!(*o, [0xa5a5_a5a5u32; 8], "round {round}, batch of {n}: wrote past the batch");
            }
        }
    }
}

/// Blocks in one batch must not influence each other: the same block gives
/// the same output next to any neighbours, and equal blocks give equal outputs.
#[test]
fn compress_many_lanes_are_independent() {
    let mut rng = Rng(0x4c41_4e45);
    let state = slhdsa::sha256::H0;
    let mut probe = [0u8; 64];
    rng.fill(&mut probe);
    let want = reference(&state, &probe);
    for n in 1..=9usize {
        for pos in 0..n {
            let mut blocks = vec![[0u8; 64]; n];
            for b in blocks.iter_mut() {
                rng.fill(b);
            }
            blocks[pos] = probe;
            let mut out = vec![[0u32; 8]; n];
            slhdsa::sha256::compress_many(&state, &blocks, &mut out);
            assert_eq!(out[pos], want, "batch of {n}, position {pos}");
        }
        let mut out = vec![[0u32; 8]; n];
        slhdsa::sha256::compress_many(&state, &vec![probe; n], &mut out);
        assert!(out.iter().all(|o| *o == want), "batch of {n} equal blocks");
    }
}

#[test]
#[should_panic]
fn compress_many_panics_if_out_is_too_short() {
    let blocks = [[0u8; 64]; 5];
    let mut out = [[0u32; 8]; 4];
    slhdsa::sha256::compress_many(&slhdsa::sha256::H0, &blocks, &mut out);
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
