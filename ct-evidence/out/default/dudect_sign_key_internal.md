20:46  up 2 days, 11:06, 4 users, load averages: 1.78 1.65 1.59
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal (m, PK.seed fixed; honest keys) | SK.seed, SK.prf, addrnd (PK.root changes with SK.seed) | 1 | 283 | 317 | 307267791.7 | 306297583.3 | +239144.603 | +0.0781% | +1.00 | 2.10 (crop 17) | 2.18 | 2.46 | no leak detected | 252374.614 |
20:50  up 2 days, 11:09, 4 users, load averages: 1.64 1.60 1.57
