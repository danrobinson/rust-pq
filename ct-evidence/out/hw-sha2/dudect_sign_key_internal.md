21:31  up 2 days, 11:51, 4 users, load averages: 1.74 1.56 1.63
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal (m, PK.seed fixed; honest keys) | SK.seed, SK.prf, addrnd (PK.root changes with SK.seed) | 1 | 283 | 317 | 30761375.0 | 30754833.3 | +28206.181 | +0.0919% | +1.29 | 2.14 (crop 48) | 0.74 | 1.07 | no leak detected | 14555.785 |
21:32  up 2 days, 11:51, 4 users, load averages: 1.97 1.62 1.65
