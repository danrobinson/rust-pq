/// Instantiate the fixed-size WOTS or FORS endpoint iterator.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub fn ROOT(
    rows: &hybrid_array::Array<hybrid_array::Array<u8, typenum::U<PARAM_N>>, typenum::U<PARAM_L>>,
    consume: extern "C" fn(*const u8, usize),
) {
    rows.iter().for_each(|row| {
        let bytes = row.as_slice();
        consume(bytes.as_ptr(), bytes.len());
    });
}
