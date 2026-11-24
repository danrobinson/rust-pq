// Compiled in a disposable directory by build.py.
#![no_std]
#[path = "ADDRESS_PATH"]
mod address;
#[path = "PARAMS_PATH"]
mod params;
mod parallel {
    // PRODUCTION_LAYOUT
    extern "C" {
        pub fn proof_permute(states: &mut States);
    }
    pub fn permute(states: &mut States) {
        unsafe {
            proof_permute(states);
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
    use crate::address::{Adrs, WOTS_PK, WOTS_PRF};
    use crate::parallel::{self, States, WIDTH};
    use crate::params::{LEN2, W};
    // PRODUCTION_HELPERS
}
