### `slh::slh_sign_internal_checked`: unconditioned profile over random honest keys (M and PK.seed fixed)

crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

- runs: 24 (run 0 = base key, others = fresh honest (SK.seed, SK.prf, addrnd), PK.seed and M fixed); failed runs: 0; every run returned a signature equal to the native one: yes
- distinct full control-flow traces: 24 (expected: all distinct, the public transcript differs)
- distinct executed-instruction counts: 24 (min 583221666, max 583225503, spread 3837)
- distinct basic-block counts: 23
- distinct call-out (malloc/realloc/free/memcpy/memset) counts: [23010]
- executed SHA-256 instructions, distinct values: SHA256H [62265032], SHA256H2 [58194448], SHA256SU0 [49735392], SHA256SU1 [49735392]
- calls of the crate's out-of-line functions, same number in every run: `fors::fors_batch` 980, `fors::fors_node` 1778, `fors::fors_pk_from_sig` 1, `fors::fors_pk_gen` 1, `fors::fors_sign` 1, `hash::chain_blocks` 21760, `hash::h_msg` 1, `hash::prf_msg` 1, `hash::thash` 2, `hash::thash_short` 7455, `hash::thash_values` 6656, `ht::ht_sign_checked` 1, `sha256::sha256_from` 6, `slh::slh_sign_internal_checked` 1, `util::base_2b` 30, `wots::sk_blocks` 6656, `wots::wots_digits` 14, `wots::wots_pk_from_sig` 7, `wots::wots_pk_gen` 6642, `wots::wots_sign` 7, `xmss::xmss_node` 13222, `xmss::xmss_pk_from_sig` 7, `xmss::xmss_sign` 7
- calls of the crate's out-of-line functions, number varies between runs: none
- distinct block-execution histograms (multiset of executed blocks, order ignored): 24

