21:32  up 2 days, 11:51, 4 users, load averages: 1.97 1.62 1.65
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal (m, whole key fixed) | addrnd only | 1 | 297 | 303 | 30750833.3 | 30757000.0 | -1622.790 | -0.0053% | -0.23 | 1.82 (crop 10) | 2.22 | 1.09 | no leak detected | 8541.185 |
21:32  up 2 days, 11:51, 4 users, load averages: 2.05 1.66 1.66
