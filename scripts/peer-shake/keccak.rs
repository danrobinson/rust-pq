/// Instantiate the released scalar routine at the SHAKE256 round count.
#[unsafe(no_mangle)]
pub fn proof_scalar_keccak(state: &mut [u64; 25]) {
    backends::soft::keccak_p::<u64, 24>(state);
}

/// Run the public SHAKE permutation selector with its real receiver.
#[unsafe(no_mangle)]
pub fn proof_dispatch_keccak(k: &Keccak, state: &mut [u64; 25]) {
    k.with_f1600(|permute| permute(state));
}
