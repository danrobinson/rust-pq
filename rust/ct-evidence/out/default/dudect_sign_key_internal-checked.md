20:53  up 2 days, 11:12, 4 users, load averages: 1.78 1.72 1.63
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys) | SK.seed, SK.prf, addrnd (PK.root changes with SK.seed) | 1 | 283 | 317 | 573686583.3 | 573163541.7 | +737015.701 | +0.1287% | +0.91 | 2.23 (crop 32) | 2.35 | 1.73 | no leak detected | 814661.539 |
20:59  up 2 days, 11:18, 4 users, load averages: 3.14 2.16 1.80
