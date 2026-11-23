/// Instantiate the exact iterator adapter chain used by both message hashes.
#[allow(unsafe_code)]
#[unsafe(no_mangle)]
pub fn proof_peer_parts(msg: &[&[&[u8]]], consume: extern "C" fn(*const u8, usize)) {
    msg.iter().copied().flatten().for_each(|part| {
        let bytes: &[u8] = part.as_ref();
        consume(bytes.as_ptr(), bytes.len());
    });
}
