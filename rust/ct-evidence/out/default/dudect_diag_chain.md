## RR/DIT: random vs random (null), DIT = 1, seed 2001
20:37  up 2 days, 10:56, 4 users, load averages: 1.58 1.54 1.56
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = random-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 199757 | 200243 | 10083.3 | 10083.3 | +0.463 | +0.0046% | +0.38 | 2.39 (crop 16) | 1.23 | 1.80 | no leak detected | 2.249 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 87875.0 | 87833.3 | +4.795 | +0.0055% | +0.32 | 1.69 (crop 64) | 1.63 | 2.08 | no leak detected | 17.818 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 48625.0 | 48625.0 | +0.671 | +0.0014% | -0.91 | 1.92 (crop 3) | 2.99 | 1.79 | no leak detected | 12.093 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 2250.0 | 2250.0 | +0.007 | +0.0003% | -0.28 | 1.43 (crop 16) | 1.88 | 3.00 | no leak detected | 0.398 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 39919 | 40081 | 20416.7 | 20416.7 | -0.703 | -0.0034% | -0.51 | 2.10 (crop 1) | 1.83 | 1.56 | no leak detected | 10.278 |

## FF/DIT: fixed A vs fixed B, DIT = 1, seed 2001
20:38  up 2 days, 10:57, 4 users, load averages: 1.83 1.61 1.59
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 199757 | 200243 | 10083.3 | 10083.3 | +0.168 | +0.0017% | +1.41 | 1.62 (crop 9) | 2.33 | 1.67 | no leak detected | 2.196 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 87916.7 | 87916.7 | -4.247 | -0.0048% | -1.04 | 3.23 (crop 38) | 3.09 | 1.39 | no leak detected | 17.508 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 48666.7 | 48708.3 | -3.944 | -0.0081% | -1.07 | 2.63 (crop 7) | 1.72 | 1.82 | no leak detected | 12.413 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 2250.0 | 2250.0 | +0.018 | +0.0008% | -1.57 | 2.17 (crop 86) | 1.99 | 2.26 | no leak detected | 0.407 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 39919 | 40081 | 20500.0 | 20500.0 | -0.738 | -0.0036% | -0.80 | 1.72 (crop 18) | 1.76 | 1.70 | no leak detected | 10.397 |

## FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 2001
20:39  up 2 days, 10:58, 4 users, load averages: 1.45 1.55 1.56
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 199757 | 200243 | 10083.3 | 10083.3 | +0.004 | +0.0000% | +1.44 | 1.44 | 2.08 | 1.45 | no leak detected | 2.262 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 87875.0 | 87875.0 | +26.808 | +0.0305% | -0.11 | 8.88 (crop 31) | 1.76 | 2.27 | **t > 4.5** | 17.922 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 48625.0 | 48625.0 | +12.696 | +0.0261% | +1.27 | 9.84 (crop 37) | 1.16 | 2.00 | **t > 4.5** | 12.302 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 2250.0 | 2250.0 | -0.002 | -0.0001% | -2.49 | 3.55 (crop 61) | 1.34 | 2.03 | no leak detected | 0.385 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 39919 | 40081 | 20416.7 | 20375.0 | +14.333 | +0.0702% | +1.93 | 20.43 (crop 36) | 1.48 | 1.88 | **t > 4.5** | 9.411 |

## FR/same/DIT: fixed (pseudo-random) vs random, same preparation path, DIT = 1, seed 2001
20:39  up 2 days, 10:58, 4 users, load averages: 1.30 1.49 1.54
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 199757 | 200243 | 10062.5 | 10062.5 | -0.019 | -0.0002% | +0.90 | 1.37 (crop 0) | 2.34 | 1.51 | no leak detected | 1.596 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 87875.0 | 87875.0 | +10.656 | +0.0121% | +1.27 | 3.07 (crop 22) | 2.68 | 2.45 | no leak detected | 16.595 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 48625.0 | 48625.0 | -0.802 | -0.0017% | +0.12 | 2.47 (crop 47) | 3.24 | 1.56 | no leak detected | 11.481 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 2250.0 | 2250.0 | -0.026 | -0.0012% | +0.98 | 2.29 (crop 19) | 0.86 | 1.52 | no leak detected | 0.359 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 39919 | 40081 | 20416.7 | 20416.7 | +4.284 | +0.0209% | +0.64 | 2.48 (crop 61) | 2.01 | 2.17 | no leak detected | 9.398 |

## RR/DIT: random vs random (null), DIT = 1, seed 2002
20:40  up 2 days, 10:59, 4 users, load averages: 1.55 1.52 1.54
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = random-random; fixed class = one fixed pseudo-random secret; seed 2002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 200640 | 199360 | 10083.3 | 10083.3 | -0.401 | -0.0040% | +0.45 | 2.48 (crop 20) | 1.26 | 1.07 | no leak detected | 1.953 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79924 | 80076 | 87875.0 | 87875.0 | +1.848 | +0.0021% | +0.44 | 3.29 (crop 11) | 2.19 | 2.01 | no leak detected | 16.694 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80105 | 79895 | 39250.0 | 39250.0 | -1.507 | -0.0038% | +0.67 | 2.20 (crop 0) | 2.58 | 1.21 | no leak detected | 9.454 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199804 | 200196 | 2250.0 | 2250.0 | +0.011 | +0.0005% | -1.85 | 1.85 | 2.06 | 1.09 | no leak detected | 0.356 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 40014 | 39986 | 20375.0 | 20375.0 | -0.084 | -0.0004% | +1.09 | 1.54 (crop 53) | 1.55 | 1.67 | no leak detected | 9.747 |

## FF/DIT: fixed A vs fixed B, DIT = 1, seed 2002
20:41  up 2 days, 11 hrs, 4 users, load averages: 1.82 1.58 1.56
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 2002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 200640 | 199360 | 10083.3 | 10083.3 | +0.665 | +0.0066% | +1.81 | 3.34 (crop 39) | 2.18 | 1.24 | no leak detected | 1.936 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79924 | 80076 | 87958.3 | 87916.7 | +1.960 | +0.0022% | +0.94 | 1.87 (crop 68) | 1.81 | 2.31 | no leak detected | 16.206 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80105 | 79895 | 39333.3 | 39333.3 | -1.189 | -0.0030% | -1.92 | 2.99 (crop 42) | 1.95 | 1.79 | no leak detected | 9.614 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 199804 | 200196 | 2250.0 | 2250.0 | -0.096 | -0.0043% | +0.32 | 2.87 (crop 31) | 2.10 | 2.00 | no leak detected | 0.486 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 40014 | 39986 | 20541.7 | 20541.7 | +2.808 | +0.0137% | -0.68 | 2.84 (crop 24) | 1.93 | 2.94 | no leak detected | 9.901 |

## FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 2002
20:42  up 2 days, 11:01, 4 users, load averages: 1.47 1.52 1.54
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 200640 | 199360 | 10083.3 | 10083.3 | +0.314 | +0.0031% | -0.04 | 2.14 (crop 47) | 1.61 | 2.24 | no leak detected | 2.164 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79924 | 80076 | 87916.7 | 87875.0 | +27.684 | +0.0315% | +1.82 | 9.05 (crop 31) | 1.80 | 2.00 | **t > 4.5** | 18.559 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80105 | 79895 | 39291.7 | 39250.0 | +13.414 | +0.0342% | +3.83 | 12.64 (crop 37) | 2.59 | 1.33 | **t > 4.5** | 10.663 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199804 | 200196 | 2250.0 | 2250.0 | -0.030 | -0.0014% | -2.23 | 2.74 (crop 92) | 2.19 | 1.52 | no leak detected | 0.402 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 40014 | 39986 | 20416.7 | 20416.7 | +11.586 | +0.0567% | +1.99 | 13.75 (crop 35) | 1.72 | 1.64 | **t > 4.5** | 8.480 |

## FR/same/DIT: fixed (pseudo-random) vs random, same preparation path, DIT = 1, seed 2002
20:42  up 2 days, 11:02, 4 users, load averages: 1.53 1.53 1.54
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2002; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 200640 | 199360 | 10083.3 | 10083.3 | -0.312 | -0.0031% | -1.06 | 3.52 (crop 2) | 1.50 | 2.41 | no leak detected | 2.037 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79924 | 80076 | 87916.7 | 87916.7 | +3.158 | +0.0036% | +0.91 | 1.35 (crop 40) | 2.71 | 1.93 | no leak detected | 16.499 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80105 | 79895 | 39291.7 | 39291.7 | -0.530 | -0.0013% | +0.15 | 2.29 (crop 56) | 1.78 | 1.32 | no leak detected | 9.825 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199804 | 200196 | 2250.0 | 2250.0 | -0.018 | -0.0008% | +0.07 | 1.58 (crop 62) | 2.03 | 1.82 | no leak detected | 0.361 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 40014 | 39986 | 20375.0 | 20375.0 | -0.127 | -0.0006% | +0.16 | 2.41 (crop 86) | 2.04 | 1.98 | no leak detected | 8.488 |

## RR: random vs random (null), seed 2001
20:43  up 2 days, 11:02, 4 users, load averages: 1.43 1.50 1.53
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 199757 | 200243 | 8083.3 | 8083.3 | +0.094 | +0.0012% | -1.00 | 1.35 (crop 30) | 1.48 | 0.95 | no leak detected | 1.840 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 70666.7 | 70666.7 | -1.770 | -0.0025% | -0.96 | 2.39 (crop 13) | 1.59 | 2.19 | no leak detected | 22.513 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 39083.3 | 39083.3 | +3.046 | +0.0078% | +0.89 | 2.01 (crop 32) | 1.28 | 1.32 | no leak detected | 14.768 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 1893.2 | 1893.2 | -0.331 | -0.0167% | +0.10 | 2.39 (crop 0) | 2.17 | 0.98 | no leak detected | 0.591 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 39919 | 40081 | 17250.0 | 17250.0 | -8.515 | -0.0473% | -0.08 | 2.09 (crop 3) | 1.83 | 1.32 | no leak detected | 12.701 |

## FF: fixed A vs fixed B, seed 2001
20:44  up 2 days, 11:03, 4 users, load averages: 1.55 1.54 1.54
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 199757 | 200243 | 8083.3 | 8083.3 | -0.191 | -0.0024% | +0.69 | 2.02 (crop 0) | 1.62 | 1.95 | no leak detected | 1.939 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 70708.3 | 70708.3 | -0.957 | -0.0014% | -0.98 | 2.22 (crop 28) | 1.16 | 1.29 | no leak detected | 22.285 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 39125.0 | 39125.0 | +0.142 | +0.0004% | -1.04 | 1.96 (crop 66) | 2.89 | 1.75 | no leak detected | 15.660 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 1895.8 | 1895.8 | -0.022 | -0.0011% | +0.46 | 1.33 (crop 14) | 1.57 | 2.33 | no leak detected | 0.616 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 39919 | 40081 | 17354.2 | 17375.0 | -12.758 | -0.0696% | -0.70 | 1.87 (crop 14) | 0.99 | 1.87 | no leak detected | 12.917 |

## FR: fixed (pseudo-random) vs random, seed 2001
20:45  up 2 days, 11:04, 4 users, load averages: 1.84 1.61 1.57
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 199757 | 200243 | 8083.3 | 8083.3 | +0.708 | +0.0087% | +0.26 | 1.75 (crop 32) | 1.98 | 1.14 | no leak detected | 2.307 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 70666.7 | 70625.0 | +27.294 | +0.0385% | +1.48 | 26.17 (crop 26) | 1.47 | 1.23 | **t > 4.5** | 24.605 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 39083.3 | 39083.3 | +23.659 | +0.0604% | +0.19 | 22.17 (crop 27) | 1.95 | 2.35 | **t > 4.5** | 15.687 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 1893.2 | 1893.2 | -0.127 | -0.0064% | -0.65 | 2.36 (crop 1) | 1.43 | 2.72 | no leak detected | 0.583 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 39919 | 40081 | 17187.5 | 17187.5 | -3.868 | -0.0216% | +1.88 | 13.10 (crop 14) | 2.82 | 1.49 | **t > 4.5** | 11.842 |

## FR/same: fixed (pseudo-random) vs random, same preparation path, seed 2001
20:46  up 2 days, 11:05, 4 users, load averages: 1.87 1.65 1.58
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 199757 | 200243 | 8083.3 | 8083.3 | +0.060 | +0.0007% | -0.02 | 1.32 (crop 50) | 2.25 | 2.33 | no leak detected | 1.937 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 70625.0 | 70625.0 | +6.584 | +0.0093% | +1.04 | 2.18 (crop 33) | 2.70 | 2.85 | no leak detected | 22.668 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 39083.3 | 39083.3 | -3.596 | -0.0092% | -2.05 | 2.21 (crop 99) | 1.43 | 2.68 | no leak detected | 14.835 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 1893.2 | 1893.2 | +0.656 | +0.0330% | +0.72 | 2.75 (crop 10) | 3.14 | 1.86 | no leak detected | 0.593 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 39919 | 40081 | 17187.5 | 17187.5 | +3.885 | +0.0217% | -0.07 | 1.49 (crop 7) | 2.52 | 1.33 | no leak detected | 12.052 |

20:46  up 2 days, 11:06, 4 users, load averages: 1.78 1.65 1.59
## ZF: fixed all-zero vs fixed pseudo-random B, seed 2001
21:31  up 2 days, 11:51, 4 users, load averages: 1.76 1.56 1.63
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = all-zero secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 199757 | 200243 | 8239.6 | 8260.4 | -15.749 | -0.1902% | -7.98 | 190.28 (crop 14) | 1.78 | 1.58 | **t > 4.5** | 2.225 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 72125.0 | 72333.3 | -154.527 | -0.2131% | -5.80 | 114.12 (crop 20) | 1.24 | 1.78 | **t > 4.5** | 25.752 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 39916.7 | 40000.0 | -76.976 | -0.1918% | -4.91 | 77.50 (crop 6) | 2.44 | 1.48 | **t > 4.5** | 15.543 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 1929.7 | 1932.3 | +8.260 | +0.4089% | -9.85 | 115.12 (crop 9) | 1.93 | 1.59 | **t > 4.5** | 0.570 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 39919 | 40081 | 17770.8 | 17812.5 | +171.943 | +0.9194% | -10.63 | 31.85 (crop 24) | 1.64 | 1.79 | **t > 4.5** | 12.278 |

## ZF/DIT: fixed all-zero vs fixed pseudo-random B, DIT = 1, seed 2001
21:32  up 2 days, 11:51, 4 users, load averages: 2.04 1.67 1.66
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = all-zero secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 199757 | 200243 | 10291.7 | 10291.7 | -0.041 | -0.0004% | +0.62 | 1.08 (crop 2) | 1.44 | 1.55 | no leak detected | 1.659 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 79690 | 80310 | 89875.0 | 89875.0 | +0.267 | +0.0003% | -0.90 | 1.40 (crop 36) | 2.15 | 2.04 | no leak detected | 14.076 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 80185 | 79815 | 49750.0 | 49750.0 | -4.386 | -0.0088% | -1.15 | 2.40 (crop 31) | 1.90 | 1.36 | no leak detected | 9.782 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 199687 | 200313 | 2299.5 | 2299.5 | -0.063 | -0.0027% | -0.31 | 2.89 (crop 24) | 1.65 | 1.70 | no leak detected | 0.312 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 39919 | 40081 | 21125.0 | 21125.0 | -1.014 | -0.0048% | -0.05 | 1.44 (crop 66) | 2.22 | 1.90 | no leak detected | 7.017 |

21:33  up 2 days, 11:52, 4 users, load averages: 2.44 1.84 1.73
