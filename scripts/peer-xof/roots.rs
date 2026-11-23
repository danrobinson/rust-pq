/// Exercise exactly the provider methods used by the benchmark-locked SLH-DSA SHAKE recipes.
pub fn proof_stream_api(input: &[u8], more: &[u8], output: &mut [u8]) {
    use digest::{ExtendableOutput, Update};
    let cached = Shake256::default().chain(input);
    let mut state = cached.clone();
    state.update(more);
    state.finalize_xof_into(output);
}

/// Specialize the standard slice iterator used by UpdateCore to its concrete block type.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub fn proof_iterate_sha3_blocks(
    blocks: &[digest::array::Array<u8, digest::typenum::U136>],
    process: extern "C" fn(*const u8),
) {
    for block in blocks {
        process(block.as_ptr());
    }
}
