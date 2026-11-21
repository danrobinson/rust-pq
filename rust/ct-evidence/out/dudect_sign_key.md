clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh_sign_internal (m, PK.seed fixed; honest keys) | SK.seed, SK.prf, addrnd (PK.root changes with SK.seed) | 1 | 283 | 317 | 819893125.0 | 825129250.0 | -2594151.988 | -0.3179% | -1.29 | 1.83 (crop 7) | 2.30 | 1.28 | no leak detected | 2524687.697 |
