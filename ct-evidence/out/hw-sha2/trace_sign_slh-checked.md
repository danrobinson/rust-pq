### `slh::slh_sign_checked`: declassification-pinned trace comparison (control flow + memory addresses)

crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

hook points (results of calls of these out-of-line functions of the crate): `slhdsa::hash::prf_msg`, `slhdsa::fors::fors_pk_from_sig`, `slhdsa::fors::fors_pk_gen`, `slhdsa::xmss::xmss_pk_from_sig`, `slhdsa::xmss::xmss_node` (calls with z = 9)

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 16 | 3 | 3 | 0 | 2/2 | 583225713 | 234664875 | PASS |
| 1 | 0 | 16 | 3 | 3 | 0 | 2/2 | 583224234 | 234662818 | PASS |
| 2 | 100 | 16 | 3 | 3 | 0 | 2/2 | 583226448 | 234665593 | PASS |
| 3 | 1 | 16 | 3 | 3 | 0 | 2/2 | 583225553 | 234665170 | PASS |

overall: ALL CONFIGURATIONS PASS

