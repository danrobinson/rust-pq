#[allow(dead_code)]
pub(crate) fn ROOT(
    pk: &crate::PkSeed<typenum::U<PARAM_N>>, sk: &crate::SkSeed<typenum::U<PARAM_N>>,
    prf: &crate::SkPrf<typenum::U<PARAM_N>>, rand: &hybrid_array::Array<u8,typenum::U<PARAM_N>>,
    data: &hybrid_array::Array<u8,typenum::U<PARAM_N>>, wots: &crate::address::WotsHash,
    tree: &crate::address::HashTree, fors: &crate::address::ForsTree, roots: &crate::address::ForsRoots,
    ends: &hybrid_array::Array<hybrid_array::Array<u8,typenum::U<PARAM_N>>,typenum::U<PARAM_LEN>>,
    nodes: &hybrid_array::Array<hybrid_array::Array<u8,typenum::U<PARAM_N>>,typenum::U<PARAM_K>>,
    parts: &[&[&[u8]]],
) {
    use crate::hashes::HashSuite;
    type P = crate::PEER_TYPE;
    let h = P::new_from_pk_seed(pk);
    let _ = h.prf_sk(sk, &wots.prf_adrs());
    let _ = h.prf_sk(sk, &fors.prf_adrs());
    let _ = h.f(wots, data);
    let _ = h.f(fors, data);
    let _ = h.h(tree, rand, data);
    let _ = h.h(fors, rand, data);
    let _ = h.t(&wots.pk_adrs(), ends);
    let _ = h.t(roots, nodes);
    let _ = P::prf_msg(prf, rand, parts);
    let _ = P::h_msg(rand, pk, data, parts);
}
