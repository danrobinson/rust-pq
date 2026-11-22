### `slh::slh_sign_internal`: unconditioned profile over random honest keys (M and PK.seed fixed)

crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and M fixed); failed runs: 0; every run returned a signature equal to the native one: yes
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 24 (min 6513217366, max 6513220818, spread 3452)
- distinct basic-block counts: 18
- distinct call-out (malloc/realloc/free/memcpy/memset) counts: [12456]
- executed SHA-256 instructions, distinct values: SHA256H [0], SHA256H2 [0], SHA256SU0 [0], SHA256SU1 [0]
- calls of the crate's out-of-line functions, same number in every run: `fors::fors_batch` 532, `fors::fors_node` 896, `fors::fors_pk_from_sig` 1, `fors::fors_sign` 1, `hash::chain_blocks_portable` 11584, `hash::h_msg` 1, `hash::prf_msg` 1, `hash::thash` 1, `hash::thash_short` 3955, `hash::thash_values` 3584, `ht::ht_sign` 1, `sha256::schedule` 39808, `sha256::sha256_from` 5, `slh::slh_sign_internal` 1, `util::base_2b` 30, `wots::sk_blocks` 3584, `wots::wots_digits` 14, `wots::wots_pk_from_sig` 7, `wots::wots_pk_gen` 3570, `wots::wots_sign` 7, `xmss::xmss_node` 7084, `xmss::xmss_pk_from_sig` 7, `xmss::xmss_sign` 7
- calls of the crate's out-of-line functions, number varies between runs: none
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

