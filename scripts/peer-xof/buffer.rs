/// Specialize the published eager buffer to SHAKE256's rate with an observed block consumer.
#[unsafe(no_mangle)]
pub fn proof_eager_update(
    state: &mut EagerBuffer<array::typenum::U136>,
    input: &[u8],
    consume: extern "C" fn(*const u8, usize),
) {
    state.digest_blocks(input, |blocks| consume(blocks.as_ptr().cast(), blocks.len()));
}

/// Finalize uses one fresh reader for the entire requested output.
#[unsafe(no_mangle)]
pub fn proof_read_output(
    out: &mut [u8],
    produce: extern "C" fn(*mut u8),
) {
    let mut state = ReadBuffer::<array::typenum::U136>::default();
    state.read(out, |block| produce(block.as_mut_ptr()));
}
