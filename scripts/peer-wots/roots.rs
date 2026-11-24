#[allow(missing_docs, private_interfaces)]
#[unsafe(no_mangle)]
pub fn whole_pk_SUFFIX(
    h: &crate::TYPE,
    sk: &crate::SkSeed<typenum::U<NBYTES>>,
    a: &crate::address::WotsHash,
    out: &mut [u8; NBYTES],
) {
    out.copy_from_slice(h.wots_pk_gen(sk, a).as_slice());
}
#[allow(missing_docs, private_interfaces)]
#[unsafe(no_mangle)]
pub fn whole_sign_SUFFIX(
    h: &crate::TYPE,
    m: &Array<u8, typenum::U<NBYTES>>,
    sk: &crate::SkSeed<typenum::U<NBYTES>>,
    a: &crate::address::WotsHash,
    out: &mut [u8; SIZE],
) {
    h.wots_sign(m, sk, a).write_to(out);
}
#[allow(missing_docs, private_interfaces)]
#[unsafe(no_mangle)]
pub fn whole_recover_SUFFIX(
    h: &crate::TYPE,
    sig: &WotsSig<crate::TYPE>,
    m: &Array<u8, typenum::U<NBYTES>>,
    a: &crate::address::WotsHash,
    out: &mut [u8; NBYTES],
) {
    out.copy_from_slice(h.wots_pk_from_sig(sig, m, a).as_slice());
}
#[allow(missing_docs, private_interfaces)]
#[unsafe(no_mangle)]
pub fn whole_chain_SUFFIX(
    h: &crate::TYPE,
    x: &Array<u8, typenum::U<NBYTES>>,
    start: u32,
    count: u32,
    a: &crate::address::WotsHash,
    out: &mut [u8; NBYTES],
) {
    out.copy_from_slice(h.wots_chain(x, start, count, a).as_slice());
}
