// Called at the permutation cut in the actual read_block method.
#[allow(unsafe_code)]
fn peer_select(f: impl FnOnce(keccak::Fn1600)) {
    unsafe extern "C" { fn observed_keccak(state: *mut u64); }
    fn permute(state: &mut [u64; 25]) {
        unsafe { observed_keccak(state.as_mut_ptr()); }
    }
    f(permute)
}

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub fn proof_absorb_bytes(s: &mut State1600, b: &[u8; 136]) {
    xor_block(s, b);
}

#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub fn proof_read_bytes(r: &mut Sha3ReaderCore<digest::typenum::U136>, out: &mut [u8; 136]) {
    out.copy_from_slice(&r.read_block());
}
