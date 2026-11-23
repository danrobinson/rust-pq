### `api::sign`: declassification-pinned trace comparison (control flow only)

crate under test: `slhdsa` built with default features, cargo release profile; emulator: Unicorn, CPU model `max`; seed 349104788289

hook points (results of calls of these out-of-line functions of the crate): `slhdsa::hash::prf_msg`, `slhdsa::fors::fors_pk_from_sig`, `slhdsa::xmss::xmss_pk_from_sig`

| public config (M, PK.seed, key A) | message bytes | values recorded and pinned | secret sets B | pinned: identical | pinned: differing | unpinned control differing | insns/run | events/run | verdict |
|---|---|---|---|---|---|---|---|---|---|
| 0 | 32 | 9 | 3 | 3 | 0 | 2/2 | 6513224097 | 257704655 | PASS |
| 1 | 0 | 9 | 3 | 3 | 0 | 2/2 | 6513220954 | 257704437 | PASS |
| 2 | 100 | 9 | 3 | 3 | 0 | 2/2 | 6513229958 | 257705078 | PASS |
| 3 | 1 | 9 | 3 | 3 | 0 | 2/2 | 6513220269 | 257704425 | PASS |

overall: ALL CONFIGURATIONS PASS

