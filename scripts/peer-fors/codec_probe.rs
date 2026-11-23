// Observe every typed field independently of both serializers, in FIPS 205 order.
#[unsafe(no_mangle)]
pub fn PEER_parse(input: &[u8; SIZE], out: &mut [u8; SIZE]) {
    let sig = crate::Signature::<PEER>::try_from(input.as_slice()).unwrap();
    let mut offset = 0;
    for &byte in sig.randomizer.iter() {
        out[offset] = byte;
        offset += 1;
    }
    for row in sig.fors_sig.0.iter() {
        for &byte in row.sk.iter() {
            out[offset] = byte;
            offset += 1;
        }
        for node in row.auth.iter() {
            for &byte in node.iter() {
                out[offset] = byte;
                offset += 1;
            }
        }
    }
    for layer in 0..D_VALUE {
        let row = sig.ht_sig.proof_row(layer);
        for index in 0..W_VALUE {
            for col in 0..N_VALUE {
                out[offset] = row.sig.proof_byte(index, col);
                offset += 1;
            }
        }
        for node in row.auth.iter() {
            for &byte in node.iter() {
                out[offset] = byte;
                offset += 1;
            }
        }
    }
    assert_eq!(offset, SIZE);
}

#[unsafe(no_mangle)]
pub fn PEER_array(input: &[u8; SIZE], out: &mut [u8; SIZE]) {
    let sig = crate::Signature::<PEER>::try_from(input.as_slice()).unwrap();
    *out = sig.to_bytes().0;
}

#[unsafe(no_mangle)]
pub fn PEER_vec(input: &[u8; SIZE], out: &mut [u8; SIZE]) {
    let sig = crate::Signature::<PEER>::try_from(input.as_slice()).unwrap();
    out.copy_from_slice(&sig.to_vec());
}

#[unsafe(no_mangle)]
pub fn PEER_invalid(input: &[u8]) -> u8 {
    if input.len() == SIZE {
        return 2;
    }
    u8::from(crate::Signature::<PEER>::try_from(input).is_ok())
}

#[unsafe(no_mangle)]
pub fn PEER_forest(input: &[u8; FORS_SIZE], out: &mut [u8; FORS_SIZE]) {
    let sig = ForsSignature::<PEER>::try_from(input.as_slice()).unwrap();
    let mut offset = 0;
    for row in sig.0.iter() {
        for &byte in row.sk.iter() {
            out[offset] = byte;
            offset += 1;
        }
        for node in row.auth.iter() {
            for &byte in node.iter() {
                out[offset] = byte;
                offset += 1;
            }
        }
    }
    assert_eq!(offset, FORS_SIZE);
}

#[unsafe(no_mangle)]
pub fn PEER_forest_write(input: &[u8; FORS_SIZE], out: &mut [u8; FORS_SIZE]) {
    let sig = ForsSignature::<PEER>::try_from(input.as_slice()).unwrap();
    sig.write_to(out);
}
