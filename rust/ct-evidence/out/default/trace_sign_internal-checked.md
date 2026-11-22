### `slh::slh_sign_internal_checked`: declassification-pinned trace comparison (control flow + memory addresses)

crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

hook points (results of calls of these out-of-line functions of the crate): `slhdsa::hash::prf_msg`, `slhdsa::fors::fors_pk_from_sig`, `slhdsa::fors::fors_pk_gen`, `slhdsa::xmss::xmss_pk_from_sig`, `slhdsa::xmss::xmss_node` (calls with z = 9)

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 16 | 4 | 4 | 0 | 2/2 | 12171176950 | 2250023606 | PASS |
| 1 | 0 | 16 | 4 | 4 | 0 | 2/2 | 12171173787 | 2250023023 | PASS |
| 2 | 100 | 16 | 4 | 4 | 0 | 2/2 | 12171182452 | 2250024550 | PASS |
| 3 | 1 | 16 | 4 | 4 | 0 | 2/2 | 12171175400 | 2250023803 | PASS |
| 4 | 32 | 16 | 4 | 4 | 0 | 2/2 | 12171176232 | 2250023266 | PASS |
| 5 | 0 | 16 | 4 | 4 | 0 | 2/2 | 12171173688 | 2250022987 | PASS |
| 6 | 100 | 16 | 4 | 4 | 0 | 2/2 | 12171183306 | 2250024963 | PASS |
| 7 | 1 | 16 | 4 | 4 | 0 | 2/2 | 12171173555 | 2250022903 | PASS |

overall: ALL CONFIGURATIONS PASS

