## RR/DIT: random vs random (null), DIT = 1, seed 2001
21:55  up 2 days, 12:14, 4 users, load averages: 2.81 2.62 2.42
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = random-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 816.4 | 816.4 | -0.008 | -0.0010% | -0.83 | 2.22 (crop 12) | 2.34 | 1.33 | no leak detected | 0.128 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6947.9 | 6947.9 | +0.588 | +0.0085% | +0.87 | 3.43 (crop 48) | 1.58 | 2.05 | no leak detected | 1.695 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3880.2 | 3880.2 | -0.187 | -0.0048% | +1.11 | 2.14 (crop 92) | 2.52 | 1.88 | no leak detected | 1.038 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 221.4 | 221.4 | -0.000 | -0.0001% | -0.54 | 1.39 (crop 64) | 1.73 | 1.91 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1789.1 | 1789.1 | -0.170 | -0.0095% | -1.48 | 1.77 (crop 96) | 1.29 | 1.58 | no leak detected | 0.692 |

## FF/DIT: fixed A vs fixed B, DIT = 1, seed 2001
21:56  up 2 days, 12:15, 4 users, load averages: 2.30 2.51 2.39
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | +0.007 | +0.0009% | -0.67 | 1.12 (crop 61) | 2.06 | 1.83 | no leak detected | 0.144 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6812.5 | 6812.5 | +0.353 | +0.0052% | +0.65 | 2.58 (crop 5) | 2.07 | 1.56 | no leak detected | 1.740 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3880.2 | 3880.2 | +0.034 | +0.0009% | +0.63 | 1.89 (crop 79) | 1.99 | 1.63 | no leak detected | 1.048 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 221.4 | 221.4 | +0.005 | +0.0021% | +1.10 | 2.34 (crop 97) | 1.44 | 1.77 | no leak detected | 0.038 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1791.7 | 1791.7 | -0.081 | -0.0045% | -0.11 | 1.65 (crop 1) | 1.22 | 1.06 | no leak detected | 0.619 |

## FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 2001
21:56  up 2 days, 12:15, 4 users, load averages: 1.92 2.39 2.35
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | +0.002 | +0.0002% | -1.21 | 2.02 (crop 70) | 1.18 | 1.40 | no leak detected | 0.143 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6812.5 | 6802.1 | +1.947 | +0.0286% | +0.48 | 7.20 (crop 41) | 2.15 | 1.97 | **t > 4.5** | 1.781 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3875.0 | 3875.0 | +1.232 | +0.0318% | +2.30 | 10.19 (crop 36) | 1.00 | 1.79 | **t > 4.5** | 1.089 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 221.0 | 221.0 | -0.007 | -0.0033% | -1.53 | 2.66 (crop 78) | 2.21 | 1.23 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1789.1 | 1789.1 | +0.521 | +0.0292% | +2.22 | 6.75 (crop 45) | 1.31 | 1.21 | **t > 4.5** | 0.709 |

## FR/same/DIT: fixed (pseudo-random) vs random, same preparation path, DIT = 1, seed 2001
21:57  up 2 days, 12:16, 4 users, load averages: 1.57 2.25 2.30
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | -0.014 | -0.0018% | -0.87 | 2.60 (crop 5) | 1.85 | 1.17 | no leak detected | 0.146 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6802.1 | 6802.1 | +0.020 | +0.0003% | +0.53 | 2.42 (crop 2) | 1.49 | 1.53 | no leak detected | 1.965 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3875.0 | 3875.0 | +0.031 | +0.0008% | -0.39 | 2.11 (crop 46) | 1.85 | 1.85 | no leak detected | 1.053 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 220.7 | 220.7 | -0.004 | -0.0018% | +1.00 | 1.88 (crop 2) | 1.86 | 1.42 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1786.5 | 1786.5 | -0.182 | -0.0102% | +1.08 | 2.34 (crop 71) | 1.89 | 1.50 | no leak detected | 0.675 |

## RR/DIT: random vs random (null), DIT = 1, seed 2002
21:57  up 2 days, 12:17, 4 users, load averages: 1.71 2.21 2.28
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = random-random; fixed class = one fixed pseudo-random secret; seed 2002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 200640 | 199360 | 799.5 | 799.5 | +0.023 | +0.0029% | -0.22 | 2.38 (crop 11) | 1.63 | 2.39 | no leak detected | 0.148 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79924 | 80076 | 6802.1 | 6802.1 | +0.649 | +0.0095% | +1.06 | 2.80 (crop 29) | 1.67 | 1.92 | no leak detected | 1.825 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80105 | 79895 | 3166.7 | 3166.7 | -0.019 | -0.0006% | -1.20 | 1.27 (crop 61) | 1.57 | 1.75 | no leak detected | 0.948 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199804 | 200196 | 221.4 | 221.4 | -0.007 | -0.0033% | -1.43 | 2.58 (crop 47) | 1.47 | 1.80 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 40014 | 39986 | 1786.5 | 1786.5 | +0.083 | +0.0046% | +1.27 | 1.94 (crop 92) | 1.38 | 1.86 | no leak detected | 0.667 |

## FF/DIT: fixed A vs fixed B, DIT = 1, seed 2002
21:58  up 2 days, 12:17, 4 users, load averages: 1.78 2.17 2.26
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 2002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 200640 | 199360 | 799.5 | 799.5 | -0.017 | -0.0021% | +0.31 | 1.27 (crop 78) | 1.93 | 1.52 | no leak detected | 0.145 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79924 | 80076 | 6812.5 | 6812.5 | +0.294 | +0.0043% | +0.14 | 1.47 (crop 52) | 1.25 | 1.80 | no leak detected | 1.791 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80105 | 79895 | 3171.9 | 3171.9 | +0.039 | +0.0012% | +0.47 | 1.11 (crop 16) | 1.24 | 1.73 | no leak detected | 0.932 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199804 | 200196 | 221.4 | 221.4 | +0.001 | +0.0003% | +2.14 | 2.46 (crop 93) | 0.94 | 1.25 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 40014 | 39986 | 1789.1 | 1791.7 | -0.151 | -0.0084% | +0.53 | 2.25 (crop 50) | 1.90 | 1.47 | no leak detected | 0.734 |

## FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 2002
21:59  up 2 days, 12:18, 4 users, load averages: 1.69 2.10 2.23
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 200640 | 199360 | 800.8 | 800.8 | +0.047 | +0.0059% | -0.65 | 2.33 (crop 21) | 1.83 | 2.81 | no leak detected | 0.144 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79924 | 80076 | 6812.5 | 6802.1 | +2.091 | +0.0307% | +2.94 | 10.39 (crop 41) | 1.96 | 1.23 | **t > 4.5** | 1.934 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80105 | 79895 | 3161.5 | 3161.5 | +0.754 | +0.0239% | +0.94 | 7.40 (crop 42) | 2.21 | 1.28 | **t > 4.5** | 0.929 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199804 | 200196 | 221.4 | 221.4 | +0.005 | +0.0024% | -0.12 | 2.54 (crop 3) | 1.38 | 1.33 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 40014 | 39986 | 1786.5 | 1786.5 | +0.749 | +0.0420% | -0.32 | 7.69 (crop 43) | 2.49 | 2.07 | **t > 4.5** | 0.714 |

## FR/same/DIT: fixed (pseudo-random) vs random, same preparation path, DIT = 1, seed 2002
21:59  up 2 days, 12:18, 4 users, load averages: 1.71 2.06 2.21
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2002; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 200640 | 199360 | 799.5 | 799.5 | -0.023 | -0.0029% | -0.12 | 1.79 (crop 45) | 1.79 | 1.06 | no leak detected | 0.144 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79924 | 80076 | 6802.1 | 6802.1 | -0.291 | -0.0043% | +0.55 | 2.23 (crop 4) | 1.22 | 2.76 | no leak detected | 1.915 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80105 | 79895 | 3166.7 | 3166.7 | +0.182 | +0.0058% | -1.82 | 2.05 (crop 19) | 2.29 | 1.22 | no leak detected | 0.904 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199804 | 200196 | 220.7 | 220.7 | +0.002 | +0.0008% | +0.28 | 1.64 (crop 3) | 1.70 | 1.63 | no leak detected | 0.038 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 40014 | 39986 | 1786.5 | 1786.5 | -0.017 | -0.0010% | -0.84 | 2.33 (crop 55) | 3.01 | 1.12 | no leak detected | 0.676 |

## RR: random vs random (null), seed 2001
22:00  up 2 days, 12:19, 4 users, load averages: 1.63 2.00 2.19
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 798.2 | 798.2 | +0.030 | +0.0038% | +0.06 | 1.87 (crop 53) | 1.28 | 1.53 | no leak detected | 0.142 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6802.1 | 6802.1 | -0.170 | -0.0025% | +0.89 | 2.18 (crop 26) | 1.81 | 1.50 | no leak detected | 1.922 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3843.8 | 3843.8 | +0.025 | +0.0007% | +0.11 | 1.22 (crop 73) | 2.31 | 1.18 | no leak detected | 0.995 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 219.4 | 219.1 | +0.009 | +0.0040% | -0.50 | 2.02 (crop 51) | 1.64 | 1.75 | no leak detected | 0.037 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1773.4 | 1773.4 | -0.055 | -0.0031% | -0.63 | 2.51 (crop 12) | 1.63 | 1.49 | no leak detected | 0.686 |

## FF: fixed A vs fixed B, seed 2001
22:00  up 2 days, 12:19, 4 users, load averages: 1.89 2.03 2.19
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | -0.053 | -0.0067% | +0.05 | 3.05 (crop 41) | 1.94 | 2.08 | no leak detected | 0.141 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6812.5 | 6812.5 | +0.117 | +0.0017% | -0.13 | 1.93 (crop 64) | 2.54 | 1.59 | no leak detected | 1.925 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3849.0 | 3849.0 | +0.064 | +0.0017% | +0.89 | 1.68 (crop 12) | 1.37 | 1.87 | no leak detected | 1.001 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 220.4 | 220.4 | +0.002 | +0.0011% | -0.72 | 2.60 (crop 49) | 1.85 | 1.40 | no leak detected | 0.038 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1781.2 | 1781.2 | +0.152 | +0.0086% | -0.52 | 2.13 (crop 2) | 1.54 | 1.60 | no leak detected | 0.666 |

## FR: fixed (pseudo-random) vs random, seed 2001
22:01  up 2 days, 12:20, 4 users, load averages: 1.59 1.94 2.15
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 798.2 | 798.2 | -0.029 | -0.0036% | +0.37 | 2.83 (crop 17) | 2.68 | 1.85 | no leak detected | 0.141 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6802.1 | 6802.1 | +1.301 | +0.0192% | +1.73 | 6.87 (crop 42) | 1.16 | 1.48 | **t > 4.5** | 1.970 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3843.8 | 3843.8 | +0.815 | +0.0212% | +1.69 | 8.67 (crop 41) | 1.53 | 2.29 | **t > 4.5** | 0.974 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 219.4 | 219.4 | -0.013 | -0.0060% | -1.09 | 2.60 (crop 45) | 1.08 | 1.86 | no leak detected | 0.038 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1773.4 | 1770.8 | +1.183 | +0.0668% | +1.27 | 6.80 (crop 43) | 1.37 | 1.88 | **t > 4.5** | 0.692 |

## FR/same: fixed (pseudo-random) vs random, same preparation path, seed 2001
22:01  up 2 days, 12:21, 4 users, load averages: 1.59 1.90 2.12
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 2001; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | +0.042 | +0.0052% | -2.10 | 2.92 (crop 6) | 2.23 | 2.31 | no leak detected | 0.143 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6802.1 | 6802.1 | +0.048 | +0.0007% | +1.59 | 2.04 (crop 92) | 1.66 | 1.62 | no leak detected | 1.964 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3843.8 | 3843.8 | +0.204 | +0.0053% | +1.00 | 2.69 (crop 44) | 1.76 | 1.01 | no leak detected | 0.972 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 219.1 | 219.1 | -0.004 | -0.0017% | +1.90 | 3.23 (crop 87) | 2.05 | 2.29 | no leak detected | 0.038 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1770.8 | 1770.8 | -0.110 | -0.0062% | -0.34 | 2.55 (crop 52) | 1.31 | 1.03 | no leak detected | 0.697 |

## ZF: fixed all-zero vs fixed pseudo-random B, seed 2001
22:02  up 2 days, 12:21, 4 users, load averages: 1.82 1.91 2.12
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = all-zero secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | +0.027 | +0.0033% | -0.54 | 1.60 (crop 3) | 1.41 | 1.54 | no leak detected | 0.142 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6812.5 | 6812.5 | +0.655 | +0.0096% | +2.21 | 2.50 (crop 28) | 1.62 | 1.38 | no leak detected | 1.944 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3854.2 | 3854.2 | +0.259 | +0.0067% | +0.07 | 2.42 (crop 42) | 1.74 | 1.64 | no leak detected | 0.986 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 220.4 | 220.4 | +0.009 | +0.0039% | +0.66 | 2.05 (crop 64) | 1.56 | 1.22 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1783.9 | 1783.9 | +0.459 | +0.0258% | +1.79 | 2.39 (crop 31) | 2.00 | 1.17 | no leak detected | 0.685 |

## ZF/DIT: fixed all-zero vs fixed pseudo-random B, DIT = 1, seed 2001
22:03  up 2 days, 12:22, 4 users, load averages: 1.60 1.84 2.08
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = all-zero secret; seed 2001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 199757 | 200243 | 799.5 | 799.5 | +0.013 | +0.0016% | +0.43 | 1.15 (crop 2) | 1.45 | 1.57 | no leak detected | 0.143 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 79690 | 80310 | 6812.5 | 6812.5 | +0.100 | +0.0015% | +0.89 | 1.74 (crop 84) | 1.88 | 1.94 | no leak detected | 1.973 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 80185 | 79815 | 3880.2 | 3880.2 | -0.148 | -0.0038% | -1.76 | 3.26 (crop 11) | 1.17 | 1.47 | no leak detected | 0.958 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 199687 | 200313 | 221.4 | 221.4 | -0.006 | -0.0029% | -0.45 | 1.80 (crop 41) | 1.21 | 1.46 | no leak detected | 0.039 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 39919 | 40081 | 1802.1 | 1802.1 | -0.070 | -0.0039% | +0.43 | 1.39 (crop 6) | 1.45 | 1.94 | no leak detected | 0.698 |

22:03  up 2 days, 12:22, 4 users, load averages: 1.43 1.78 2.05
