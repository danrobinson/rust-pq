20:50  up 2 days, 11:09, 4 users, load averages: 1.64 1.60 1.57
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal (m, whole key fixed) | addrnd only | 1 | 297 | 303 | 305866875.0 | 305811458.3 | +8766.288 | +0.0029% | +0.05 | 1.41 (crop 16) | 2.19 | 1.93 | no leak detected | 239082.976 |
20:53  up 2 days, 11:12, 4 users, load averages: 1.78 1.72 1.63
