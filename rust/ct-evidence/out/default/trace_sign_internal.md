### `slh::slh_sign_internal`: declassification-pinned trace comparison (control flow + memory addresses)

crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

hook points (results of calls of these out-of-line functions of the crate): `slhdsa::hash::prf_msg`, `slhdsa::fors::fors_pk_from_sig`, `slhdsa::fors::fors_pk_gen`, `slhdsa::xmss::xmss_pk_from_sig`, `slhdsa::xmss::xmss_node` (calls with z = 9)

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 9 | 4 | 4 | 0 | 2/2 | 6513219407 | 1203415794 | PASS |
| 1 | 0 | 9 | 4 | 4 | 0 | 2/2 | 6513216244 | 1203415211 | PASS |
| 2 | 100 | 9 | 4 | 4 | 0 | 2/2 | 6513224909 | 1203416738 | PASS |
| 3 | 1 | 9 | 4 | 4 | 0 | 2/2 | 6513217857 | 1203415991 | PASS |
| 4 | 32 | 9 | 4 | 4 | 0 | 2/2 | 6513218689 | 1203415454 | PASS |
| 5 | 0 | 9 | 4 | 4 | 0 | 2/2 | 6513216145 | 1203415175 | PASS |
| 6 | 100 | 9 | 4 | 4 | 0 | 2/2 | 6513225763 | 1203417151 | PASS |
| 7 | 1 | 9 | 4 | 4 | 0 | 2/2 | 6513216012 | 1203415091 | PASS |

overall: ALL CONFIGURATIONS PASS

