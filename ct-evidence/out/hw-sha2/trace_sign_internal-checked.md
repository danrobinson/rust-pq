### `slh::slh_sign_internal_checked`: declassification-pinned trace comparison (control flow + memory addresses)

crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

hook points (results of calls of these out-of-line functions of the crate): `slhdsa::hash::prf_msg`, `slhdsa::fors::fors_pk_from_sig`, `slhdsa::fors::fors_pk_gen`, `slhdsa::xmss::xmss_pk_from_sig`, `slhdsa::xmss::xmss_node` (calls with z = 9)

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583225622 | 234665948 | PASS |
| 1 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583223632 | 234663169 | PASS |
| 2 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583222907 | 234660813 | PASS |
| 3 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583225499 | 234665396 | PASS |
| 4 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583222247 | 234660513 | PASS |
| 5 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583223146 | 234662228 | PASS |
| 6 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583225944 | 234665311 | PASS |
| 7 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583223625 | 234663024 | PASS |
| 8 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583222958 | 234662120 | PASS |
| 9 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583225606 | 234666160 | PASS |
| 10 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583225928 | 234665315 | PASS |
| 11 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583223422 | 234662707 | PASS |
| 12 | 32 | 16 | 6 | 6 | 0 | 2/2 | 583223110 | 234662467 | PASS |
| 13 | 0 | 16 | 6 | 6 | 0 | 2/2 | 583222712 | 234661626 | PASS |
| 14 | 100 | 16 | 6 | 6 | 0 | 2/2 | 583224160 | 234662871 | PASS |
| 15 | 1 | 16 | 6 | 6 | 0 | 2/2 | 583223953 | 234663576 | PASS |

overall: ALL CONFIGURATIONS PASS

