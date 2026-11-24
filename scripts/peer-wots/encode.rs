/// Project parsed WOTS fields into the independent FIPS row-major representation.
#[unsafe(no_mangle)]
pub fn DECODE(input: &[u8], output: &mut [[u8; PARAM_N]; PARAM_ROWS]) -> bool {
    let Ok(signature) = WotsSig::<crate::PEER_TYPE>::try_from(input) else {
        return false;
    };
    for (dst, row) in output.iter_mut().zip(signature.0.iter()) {
        dst.copy_from_slice(row.as_slice());
    }
    true
}

/// Build a typed WOTS signature from independent rows and serialize it.
#[unsafe(no_mangle)]
pub fn ENCODE(input: &[[u8; PARAM_N]; PARAM_ROWS], output: &mut [u8; PARAM_SIZE]) {
    let rows = Array::from_fn(|i| Array(input[i]));
    WotsSig::<crate::PEER_TYPE>(rows).write_to(output);
}
