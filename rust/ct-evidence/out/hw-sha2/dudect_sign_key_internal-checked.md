21:32  up 2 days, 11:51, 4 users, load averages: 2.05 1.66 1.66
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| slh::slh_sign_internal_checked (m, PK.seed fixed; honest keys) | SK.seed, SK.prf, addrnd (PK.root changes with SK.seed) | 1 | 283 | 317 | 57533958.3 | 57531166.7 | +1947.301 | +0.0034% | -0.78 | 2.18 (crop 2) | 1.47 | 1.83 | no leak detected | 9643.644 |
21:33  up 2 days, 11:52, 4 users, load averages: 2.39 1.77 1.70
