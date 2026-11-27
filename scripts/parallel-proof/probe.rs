// Compiled in a disposable directory by build.py.
#![no_std]
#[path = "ADDRESS_PATH"]
mod address;
#[path = "PARAMS_PATH"]
mod params;
mod parallel {
    // PRODUCTION_LAYOUT
    extern "C" {
        pub fn proof_permute(states: &mut States, active: usize);
    }
    pub fn permute_active(states: &mut States, active: usize) {
        unsafe { proof_permute(states, active) }
    }
    pub fn permute(states: &mut States) {
        unsafe {
            proof_permute(states, WIDTH);
        }
    }
}
mod hash {
    use super::address::Adrs;
    extern "C" {
        fn proof_parent(out: *mut u8, seed: *const u8, addr: *const u8, l: *const u8, r: *const u8);
    }
    pub(super) fn thash_pair<const N: usize>(
        seed: &[u8; N],
        addr: &Adrs,
        l: &[u8; N],
        r: &[u8; N],
    ) -> [u8; N] {
        let mut out = [0; N];
        unsafe {
            proof_parent(
                out.as_mut_ptr(),
                seed.as_ptr(),
                addr.full().as_ptr(),
                l.as_ptr(),
                r.as_ptr(),
            );
        }
        out
    }
}
mod batch {
    use crate::address::{Adrs, WOTS_HASH, WOTS_PK, WOTS_PRF, TREE};
    use crate::parallel::{self, States, WIDTH};
    use crate::params::{LEN2, W};
    use crate::hash::thash_pair;
    // Exclusive to the width-three fallback. Reaching it fails this width-eight replay.
    fn keygen<const N: usize>(_: &[u8;N], _: &[u8;N], _: Adrs) -> [u8;N] { unreachable!() }
    // PRODUCTION_HELPERS
}
