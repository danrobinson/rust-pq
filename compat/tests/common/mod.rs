//! Test-only random sources. Neither is random.
#![allow(dead_code)]

use core::convert::Infallible;
use slh_dsa::signature::rand_core::{TryCryptoRng, TryRng};

/// A fixed byte stream (SplitMix64), so that both crates see the same draws.
pub struct TestRng(pub u64);

impl TestRng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    pub fn bytes(&mut self, len: usize) -> Vec<u8> {
        let mut out = vec![0u8; len];
        let Ok(()) = self.try_fill_bytes(&mut out);
        out
    }
}

impl TryRng for TestRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        Ok(self.next() as u32)
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        Ok(self.next())
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        for byte in dst {
            *byte = self.next() as u8;
        }
        Ok(())
    }
}

impl TryCryptoRng for TestRng {}

/// A random source that always fails.
pub struct FailingRng;

#[derive(Debug)]
pub struct Failed;

impl core::fmt::Display for Failed {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("no randomness")
    }
}

impl core::error::Error for Failed {}

impl TryRng for FailingRng {
    type Error = Failed;

    fn try_next_u32(&mut self) -> Result<u32, Failed> {
        Err(Failed)
    }

    fn try_next_u64(&mut self) -> Result<u64, Failed> {
        Err(Failed)
    }

    fn try_fill_bytes(&mut self, _dst: &mut [u8]) -> Result<(), Failed> {
        Err(Failed)
    }
}

impl TryCryptoRng for FailingRng {}
