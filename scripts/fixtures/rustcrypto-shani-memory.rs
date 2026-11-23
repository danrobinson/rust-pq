fn load_block(block: &[u8; 64]) -> [__m128i; 4] {
    let block_ptr: *const __m128i = block.as_ptr().cast();
    let mask = _mm_set_epi64x({MASK_HIGH}, {MASK_LOW});
    core::array::from_fn(|i| {
        let w = unsafe { _mm_loadu_si128(block_ptr.add(i)) };
        _mm_shuffle_epi8(w, mask)
    })
}

#[inline]
#[target_feature(enable = "sse2")]
fn load_state(state: &[u32; 8]) -> [__m128i; 2] {
    let state_ptr: *const __m128i = state.as_ptr().cast();
    core::array::from_fn(|i| unsafe { _mm_loadu_si128(state_ptr.add(i)) })
}

#[inline]
#[target_feature(enable = "sse2")]
fn store_state(state: &mut [u32; 8], [dcba, hgef]: [__m128i; 2]) {
    let state_ptr: *mut __m128i = state.as_mut_ptr().cast();
    unsafe {
        _mm_storeu_si128(state_ptr.add({FIRST_OFFSET}), {FIRST_VALUE});
        _mm_storeu_si128(state_ptr.add({SECOND_OFFSET}), {SECOND_VALUE});
    }
}
