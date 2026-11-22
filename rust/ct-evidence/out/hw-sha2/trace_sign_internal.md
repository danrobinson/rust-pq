### `slh::slh_sign_internal`: declassification-pinned trace comparison (control flow + memory addresses)

crate under test: `slhdsa` built with `--features hw-sha2` (`sha256::hw_active()` = true), cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

hook points (results of calls of these out-of-line functions of the crate): `slhdsa::hash::prf_msg`, `slhdsa::fors::fors_pk_from_sig`, `slhdsa::fors::fors_pk_gen`, `slhdsa::xmss::xmss_pk_from_sig`, `slhdsa::xmss::xmss_node` (calls with z = 9)

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311240556 | 124711643 | PASS |
| 1 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311238566 | 124708864 | PASS |
| 2 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311237841 | 124706508 | PASS |
| 3 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311240433 | 124711091 | PASS |
| 4 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311237181 | 124706208 | PASS |
| 5 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311238080 | 124707923 | PASS |
| 6 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311240878 | 124711006 | PASS |
| 7 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311238559 | 124708719 | PASS |
| 8 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311237892 | 124707815 | PASS |
| 9 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311240540 | 124711855 | PASS |
| 10 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311240862 | 124711010 | PASS |
| 11 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311238356 | 124708402 | PASS |
| 12 | 32 | 9 | 6 | 6 | 0 | 2/2 | 311238044 | 124708162 | PASS |
| 13 | 0 | 9 | 6 | 6 | 0 | 2/2 | 311237646 | 124707321 | PASS |
| 14 | 100 | 9 | 6 | 6 | 0 | 2/2 | 311239094 | 124708566 | PASS |
| 15 | 1 | 9 | 6 | 6 | 0 | 2/2 | 311238887 | 124709271 | PASS |

overall: ALL CONFIGURATIONS PASS

