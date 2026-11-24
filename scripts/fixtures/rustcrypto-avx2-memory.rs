fn rk(i: usize) -> __m128i {
    let chunk = &crate::consts::K64[i..][..2];
    unsafe { _mm_loadu_si128(chunk.as_ptr().cast()) }
}

fn cast_ms(ms: &MsgSchedule) -> &[u64; SHA512_BLOCK_WORDS_NUM] {
    unsafe { &*(ms.as_ptr().cast()) }
}

fn cast_rs(rs: &RoundStates) -> &[u64; SHA512_ROUNDS_NUM] {
    unsafe { &*(rs.as_ptr().cast()) }
}

fn load_data_avx(x: &mut [__m128i; 8], ms: &mut MsgSchedule, data: *const __m128i) {
    #[allow(non_snake_case)]
    let MASK = _mm_setr_epi32({MASK128});

    macro_rules! unrolled_iterations {
        ($($i:literal),*) => {$(
            x[$i] = unsafe { _mm_loadu_si128(data.add($i).cast()) };
            x[$i] = _mm_shuffle_epi8(x[$i], MASK);

            let y = _mm_add_epi64(x[$i], rk(2 * $i));

            ms[$i] = y;
        )*};
    }

    unrolled_iterations!(0, 1, 2, 3, 4, 5, 6, 7);
}

fn load_data_avx2(
    x: &mut [__m256i; 8],
    ms: &mut MsgSchedule,
    t2: &mut RoundStates,
    block: &[[u8; 128]; 2],
) {
    #[allow(non_snake_case)]
    let MASK = _mm256_set_epi64x({MASK256});

    let block_ptr: *const __m128i = block.as_ptr().cast();

    macro_rules! unrolled_iterations {
        ($($i:literal),*) => {$(
            let d0 = unsafe { _mm_loadu_si128(block_ptr.add($i)) };
            let d1 = unsafe { _mm_loadu_si128(block_ptr.add(8 + $i)) };
            x[$i] = _mm256_insertf128_si256(x[$i], d1, 1);
            x[$i] = _mm256_insertf128_si256(x[$i], d0, 0);

            x[$i] = _mm256_shuffle_epi8(x[$i], MASK);

            let t = rk(2 * $i);
            let y = _mm256_add_epi64(x[$i], _mm256_set_m128i(t, t));

            ms[$i] = _mm256_extracti128_si256(y, 0);
            t2[$i] = _mm256_extracti128_si256(y, 1);
        )*};
    }

    unrolled_iterations!(0, 1, 2, 3, 4, 5, 6, 7);
}
