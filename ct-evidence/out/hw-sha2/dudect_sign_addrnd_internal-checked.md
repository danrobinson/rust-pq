21:33  up 2 days, 11:52, 4 users, load averages: 2.39 1.77 1.70
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal_checked (m, whole key fixed) | addrnd only | 1 | 297 | 303 | 57543416.7 | 57527833.3 | -773.376 | -0.0013% | -0.14 | 2.82 (crop 10) | 1.32 | 1.46 | no leak detected | 10060.276 |
21:33  up 2 days, 11:52, 4 users, load averages: 2.41 1.85 1.73
