20:59  up 2 days, 11:18, 4 users, load averages: 3.14 2.16 1.80
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal_checked (m, whole key fixed) | addrnd only | 1 | 297 | 303 | 572233708.3 | 572405958.3 | -261608.982 | -0.0458% | -1.51 | 2.64 (crop 2) | 2.08 | 2.08 | no leak detected | 572542.718 |
21:05  up 2 days, 11:24, 4 users, load averages: 1.87 1.87 1.78
