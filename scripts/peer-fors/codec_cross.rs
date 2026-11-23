#[unsafe(no_mangle)]
pub fn PEER_peer_to_ours(input: &[u8; SIZE], output: &mut [u8; SIZE]) {
    let signature = peer::Signature::<peer::PEER>::try_from(input.as_slice()).unwrap();
    let bytes = signature.to_vec();
    let signature = ours::Signature::<ours::PEER>::try_from(bytes.as_slice()).unwrap();
    *output = signature.to_bytes().0;
}

#[unsafe(no_mangle)]
pub fn PEER_ours_to_peer(input: &[u8; SIZE], output: &mut [u8; SIZE]) {
    let signature = ours::Signature::<ours::PEER>::try_from(input.as_slice()).unwrap();
    let bytes = signature.to_vec();
    let signature = peer::Signature::<peer::PEER>::try_from(bytes.as_slice()).unwrap();
    *output = signature.to_bytes().0;
}

#[unsafe(no_mangle)]
pub fn PEER_both_invalid(input: &[u8]) -> u8 {
    if input.len() == SIZE {
        return 2;
    }
    u8::from(
        peer::Signature::<peer::PEER>::try_from(input).is_ok()
            || ours::Signature::<ours::PEER>::try_from(input).is_ok(),
    )
}
