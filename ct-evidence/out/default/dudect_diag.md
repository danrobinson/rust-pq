## RR: random vs random (null), seed 1001
19:36  up 2 days,  9:55, 4 users, load averages: 1.79 1.66 2.13
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 32 | 199892 | 200108 | 205.7 | 205.7 | +0.008 | +0.0041% | +0.53 | 1.73 (crop 19) | 1.77 | 1.22 | no leak detected | 0.079 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 192.4 | 192.4 | +0.020 | +0.0104% | +0.75 | 1.62 (crop 6) | 1.52 | 1.10 | no leak detected | 0.048 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 301.4 | 301.4 | +0.074 | +0.0238% | +1.51 | 2.73 (crop 83) | 1.06 | 1.22 | no leak detected | 0.087 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 475.9 | 475.9 | +0.022 | +0.0045% | -0.52 | 1.64 (crop 27) | 1.50 | 1.67 | no leak detected | 0.121 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200459 | 199541 | 136.2 | 136.2 | +0.001 | +0.0009% | +0.85 | 2.13 (crop 18) | 1.80 | 2.50 | no leak detected | 0.037 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 199841 | 200159 | 141.8 | 141.8 | +0.012 | +0.0086% | +1.37 | 1.78 (crop 5) | 1.55 | 1.38 | no leak detected | 0.037 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199796 | 200204 | 142.3 | 142.3 | -0.039 | -0.0269% | +0.63 | 1.94 (crop 34) | 1.72 | 1.17 | no leak detected | 0.035 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2028.6 | 2028.6 | -0.066 | -0.0032% | -0.15 | 1.83 (crop 42) | 1.53 | 1.53 | no leak detected | 0.652 |
| fors_sk_gen | SK.seed | 256 | 200085 | 199915 | 146.2 | 146.2 | +0.011 | +0.0074% | +0.56 | 1.49 (crop 63) | 1.79 | 1.76 | no leak detected | 0.034 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 367.8 | 367.8 | -0.023 | -0.0062% | +0.48 | 2.15 (crop 1) | 1.51 | 1.66 | no leak detected | 0.136 |

## FF: fixed A vs fixed B, seed 1001
19:38  up 2 days,  9:57, 4 users, load averages: 1.68 1.65 2.07
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 204.8 | 204.8 | -0.007 | -0.0036% | +0.07 | 2.37 (crop 9) | 2.18 | 1.47 | no leak detected | 0.041 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 189.5 | 189.5 | +0.012 | +0.0064% | -0.01 | 2.43 (crop 28) | 1.14 | 1.05 | no leak detected | 0.040 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 301.4 | 301.4 | +0.005 | +0.0015% | +1.10 | 1.27 (crop 55) | 2.81 | 1.22 | no leak detected | 0.079 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 474.6 | 474.6 | +0.079 | +0.0162% | +0.34 | 2.25 (crop 8) | 2.32 | 2.23 | no leak detected | 0.123 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200459 | 199541 | 135.9 | 135.9 | -0.001 | -0.0007% | +0.53 | 1.65 (crop 23) | 1.45 | 2.13 | no leak detected | 0.036 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 199841 | 200159 | 141.9 | 141.9 | -0.008 | -0.0054% | -0.58 | 1.66 (crop 1) | 3.04 | 2.45 | no leak detected | 0.043 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199796 | 200204 | 142.4 | 142.4 | -0.003 | -0.0018% | -1.31 | 1.48 (crop 99) | 1.29 | 1.38 | no leak detected | 0.036 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2026.0 | 2026.0 | -0.020 | -0.0010% | +1.06 | 2.40 (crop 44) | 1.87 | 1.37 | no leak detected | 0.655 |
| fors_sk_gen | SK.seed | 256 | 200085 | 199915 | 146.2 | 146.2 | +0.022 | +0.0147% | +2.17 | 3.25 (crop 57) | 1.35 | 2.21 | no leak detected | 0.034 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 368.5 | 368.5 | +0.044 | +0.0119% | +2.34 | 2.76 (crop 50) | 1.35 | 1.42 | no leak detected | 0.137 |

## FF: fixed A vs fixed B, seed 1002
19:40  up 2 days,  9:59, 4 users, load averages: 1.51 1.62 2.00
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 205.1 | 205.1 | -0.011 | -0.0056% | -1.54 | 2.95 (crop 4) | 1.56 | 0.92 | no leak detected | 0.041 |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 189.8 | 189.8 | -0.003 | -0.0016% | -0.12 | 2.26 (crop 1) | 1.28 | 1.10 | no leak detected | 0.040 |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 301.4 | 301.4 | -0.086 | -0.0278% | -0.86 | 2.13 (crop 15) | 0.97 | 1.16 | no leak detected | 0.087 |
| sha256/len=120 | all message bytes | 8 | 200138 | 199862 | 474.0 | 474.0 | -0.154 | -0.0314% | +0.10 | 2.68 (crop 16) | 1.50 | 0.91 | no leak detected | 0.210 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200149 | 199851 | 135.7 | 135.7 | -0.012 | -0.0088% | -1.14 | 1.72 (crop 74) | 2.21 | 1.08 | no leak detected | 0.032 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 199922 | 200078 | 141.8 | 141.8 | +0.018 | +0.0128% | +0.76 | 3.46 (crop 21) | 1.69 | 1.71 | no leak detected | 0.032 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199649 | 200351 | 142.4 | 142.4 | +0.033 | +0.0227% | -0.65 | 2.11 (crop 29) | 2.19 | 1.31 | no leak detected | 0.035 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99512 | 100488 | 2026.0 | 2026.0 | -0.040 | -0.0020% | -0.91 | 1.66 (crop 50) | 2.11 | 1.21 | no leak detected | 0.623 |
| fors_sk_gen | SK.seed | 256 | 199797 | 200203 | 146.8 | 146.8 | +0.012 | +0.0082% | -0.18 | 1.41 (crop 2) | 1.44 | 1.42 | no leak detected | 0.034 |
| fors_node/z=0 | SK.seed | 64 | 99927 | 100073 | 369.1 | 369.1 | -0.045 | -0.0121% | +0.17 | 2.03 (crop 26) | 2.02 | 1.30 | no leak detected | 0.136 |

## FR: fixed (pseudo-random) vs random, seed 1001
19:41  up 2 days, 10:01, 4 users, load averages: 1.68 1.63 1.96
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 204.8 | 204.8 | -0.092 | -0.0451% | -1.57 | 17.88 (crop 27) | 3.03 | 1.92 | **t > 4.5** | 0.041 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 188.8 | 188.8 | -0.005 | -0.0025% | -0.62 | 2.85 (crop 26) | 1.38 | 2.05 | no leak detected | 0.038 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 300.8 | 300.8 | -0.115 | -0.0373% | +0.04 | 5.89 (crop 23) | 2.17 | 1.90 | **t > 4.5** | 0.085 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 474.6 | 474.6 | +0.022 | +0.0045% | +0.74 | 2.85 (crop 16) | 2.17 | 2.37 | no leak detected | 0.120 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200459 | 199541 | 135.9 | 136.1 | +0.352 | +0.2548% | -7.50 | 187.01 (crop 6) | 2.29 | 2.27 | **t > 4.5** | 0.033 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 199841 | 200159 | 141.9 | 141.9 | +0.015 | +0.0105% | +1.21 | 1.41 (crop 3) | 1.57 | 1.41 | no leak detected | 0.040 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199796 | 200204 | 142.4 | 142.3 | -0.202 | -0.1396% | +2.46 | 30.59 (crop 20) | 1.53 | 1.35 | **t > 4.5** | 0.035 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2026.0 | 2028.6 | -1.828 | -0.0901% | -2.06 | 78.73 (crop 14) | 1.33 | 1.45 | **t > 4.5** | 0.627 |
| fors_sk_gen | SK.seed | 256 | 200085 | 199915 | 146.3 | 146.5 | -0.057 | -0.0386% | -1.88 | 2.94 (crop 11) | 1.71 | 1.54 | no leak detected | 0.035 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 367.2 | 366.5 | -0.001 | -0.0003% | +1.73 | 12.36 (crop 5) | 1.93 | 2.45 | **t > 4.5** | 0.153 |

## FR/same: fixed (pseudo-random) vs random, same preparation path, seed 1001
19:43  up 2 days, 10:02, 4 users, load averages: 1.44 1.56 1.89
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 204.8 | 204.8 | -0.071 | -0.0348% | -2.71 | 22.43 (crop 21) | 1.26 | 2.57 | **t > 4.5** | 0.042 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 189.5 | 189.5 | -0.019 | -0.0098% | -1.92 | 3.42 (crop 9) | 1.46 | 1.10 | no leak detected | 0.041 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 301.4 | 301.4 | +0.065 | +0.0211% | +0.74 | 6.76 (crop 11) | 1.41 | 1.16 | **t > 4.5** | 0.086 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 475.9 | 475.9 | -0.023 | -0.0047% | -1.61 | 12.56 (crop 13) | 2.72 | 1.69 | **t > 4.5** | 0.128 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200459 | 199541 | 136.7 | 136.9 | +0.383 | +0.2745% | -5.88 | 94.86 (crop 9) | 1.20 | 1.50 | **t > 4.5** | 0.035 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 199841 | 200159 | 141.8 | 141.8 | +0.016 | +0.0112% | +0.33 | 1.84 (crop 23) | 2.32 | 1.49 | no leak detected | 0.036 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199796 | 200204 | 142.4 | 142.4 | -0.210 | -0.1447% | +2.14 | 35.62 (crop 19) | 1.55 | 1.64 | **t > 4.5** | 0.036 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2028.6 | 2028.6 | -1.864 | -0.0917% | -3.44 | 83.40 (crop 12) | 1.58 | 1.57 | **t > 4.5** | 0.749 |
| fors_sk_gen | SK.seed | 256 | 200085 | 199915 | 146.2 | 146.2 | -0.032 | -0.0214% | +0.37 | 5.95 (crop 16) | 1.88 | 1.31 | **t > 4.5** | 0.036 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 365.2 | 365.2 | +0.070 | +0.0187% | +0.54 | 6.02 (crop 7) | 1.55 | 1.44 | **t > 4.5** | 0.155 |

## FR/x8: fixed (pseudo-random) vs random, 8 x calls per measurement, seed 1001
19:45  up 2 days, 10:04, 4 users, load averages: 1.83 1.62 1.87
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001; calls per measurement = 8 x calibrated

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1024 | 49974 | 50026 | 203.2 | 203.2 | +0.086 | +0.0421% | -1.16 | 4.03 (crop 35) | 2.13 | 1.10 | no leak detected | 0.049 |
| sha256/len=16 | all message bytes | 1024 | 50202 | 49798 | 187.9 | 188.0 | +0.020 | +0.0107% | -1.91 | 5.10 (crop 11) | 1.35 | 1.54 | **t > 4.5** | 0.051 |
| sha256/len=119 | all message bytes | 512 | 49963 | 50037 | 300.4 | 300.5 | -0.053 | -0.0173% | -1.13 | 14.36 (crop 3) | 2.65 | 1.90 | **t > 4.5** | 0.130 |
| sha256/len=120 | all message bytes | 512 | 50039 | 49961 | 474.2 | 474.2 | -0.150 | -0.0309% | +1.96 | 3.14 (crop 13) | 1.51 | 2.03 | no leak detected | 0.191 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 50123 | 49877 | 135.9 | 136.0 | +0.114 | +0.0826% | -1.58 | 35.57 (crop 4) | 1.68 | 2.35 | **t > 4.5** | 0.049 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 2048 | 50009 | 49991 | 141.6 | 141.6 | -0.051 | -0.0358% | -1.39 | 39.72 (crop 15) | 2.04 | 2.02 | **t > 4.5** | 0.037 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 2048 | 49840 | 50160 | 142.5 | 142.5 | +0.004 | +0.0030% | -1.16 | 6.08 (crop 6) | 1.60 | 1.70 | **t > 4.5** | 0.039 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 24775 | 25225 | 2025.7 | 2026.0 | +0.027 | +0.0013% | -0.06 | 22.85 (crop 18) | 1.24 | 1.58 | **t > 4.5** | 0.820 |
| fors_sk_gen | SK.seed | 1024 | 50019 | 49981 | 146.5 | 146.5 | -0.006 | -0.0039% | +0.37 | 5.16 (crop 3) | 1.48 | 1.86 | **t > 4.5** | 0.050 |
| fors_node/z=0 | SK.seed | 512 | 24873 | 25127 | 372.2 | 372.2 | +0.065 | +0.0172% | -0.48 | 2.71 (crop 19) | 1.58 | 2.64 | no leak detected | 0.187 |

## FZ: fixed (all-zero) vs random, seed 1001
19:49  up 2 days, 10:08, 4 users, load averages: 1.51 1.63 1.81
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 204.8 | 205.1 | -0.113 | -0.0548% | -2.84 | 25.01 (crop 23) | 1.38 | 1.68 | **t > 4.5** | 0.040 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 188.8 | 188.8 | -0.075 | -0.0399% | -2.45 | 20.75 (crop 18) | 2.65 | 1.86 | **t > 4.5** | 0.039 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 300.1 | 300.8 | +0.116 | +0.0377% | -3.20 | 72.03 (crop 11) | 1.34 | 2.86 | **t > 4.5** | 0.089 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 474.6 | 475.3 | -0.220 | -0.0450% | -1.59 | 45.48 (crop 12) | 0.85 | 1.56 | **t > 4.5** | 0.126 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200459 | 199541 | 134.8 | 136.1 | -2.042 | -1.4939% | -173.23 | 426.07 (crop 19) | 1.82 | 1.93 | **t > 4.5** | 0.031 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 199841 | 200159 | 141.8 | 141.8 | -0.002 | -0.0012% | +0.41 | 2.33 (crop 24) | 1.41 | 2.76 | no leak detected | 0.036 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199796 | 200204 | 142.3 | 142.3 | +0.149 | +0.1033% | +0.58 | 8.63 (crop 28) | 1.46 | 1.55 | **t > 4.5** | 0.035 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2026.0 | 2028.6 | -1.837 | -0.0906% | -3.41 | 80.69 (crop 14) | 2.26 | 2.14 | **t > 4.5** | 0.627 |
| fors_sk_gen | SK.seed | 256 | 200085 | 199915 | 146.3 | 146.3 | -0.039 | -0.0262% | +0.35 | 2.01 (crop 9) | 1.95 | 1.84 | no leak detected | 0.035 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 365.2 | 365.2 | +0.074 | +0.0198% | -0.06 | 6.89 (crop 7) | 1.12 | 1.12 | **t > 4.5** | 0.153 |

## FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 1001
19:51  up 2 days, 10:10, 4 users, load averages: 1.63 1.61 1.77
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 234.7 | 234.7 | -0.002 | -0.0006% | +0.22 | 0.91 (crop 7) | 1.93 | 1.46 | no leak detected | 0.039 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 219.4 | 219.4 | +0.003 | +0.0013% | -0.44 | 1.97 (crop 44) | 1.21 | 2.10 | no leak detected | 0.038 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 354.2 | 354.2 | -0.006 | -0.0016% | -0.11 | 2.02 (crop 36) | 2.26 | 1.44 | no leak detected | 0.066 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 556.0 | 556.0 | -0.007 | -0.0013% | +1.20 | 2.16 (crop 1) | 2.38 | 1.82 | no leak detected | 0.087 |
| compress (copy inlined into the wrapper) | state and block | 128 | 200459 | 199541 | 160.8 | 160.8 | -0.002 | -0.0013% | -1.08 | 1.52 (crop 37) | 1.81 | 1.56 | no leak detected | 0.032 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 199841 | 200159 | 164.7 | 164.7 | -0.002 | -0.0014% | -2.30 | 2.36 (crop 10) | 1.78 | 1.99 | no leak detected | 0.032 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 128 | 199796 | 200204 | 165.4 | 165.4 | -0.003 | -0.0015% | -1.15 | 2.76 (crop 2) | 1.91 | 1.05 | no leak detected | 0.031 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 99638 | 100362 | 2541.7 | 2541.7 | +0.211 | +0.0083% | +1.95 | 2.86 (crop 61) | 2.27 | 1.85 | no leak detected | 0.703 |
| fors_sk_gen | SK.seed | 128 | 200085 | 199915 | 168.6 | 168.6 | +0.003 | +0.0017% | -0.36 | 1.36 (crop 27) | 2.03 | 2.07 | no leak detected | 0.032 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 427.1 | 427.1 | +0.003 | +0.0006% | -2.47 | 2.47 | 1.74 | 1.00 | no leak detected | 0.120 |

## FZ/DIT: fixed (all-zero) vs random, DIT = 1, seed 1001
19:52  up 2 days, 10:11, 4 users, load averages: 1.44 1.55 1.73
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 234.4 | 234.4 | -0.006 | -0.0024% | +0.11 | 2.07 (crop 40) | 2.38 | 1.78 | no leak detected | 0.045 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 219.1 | 219.1 | -0.004 | -0.0019% | +0.42 | 2.34 (crop 24) | 1.43 | 1.19 | no leak detected | 0.043 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 353.5 | 353.5 | +0.000 | +0.0001% | +1.79 | 2.22 (crop 93) | 2.39 | 1.78 | no leak detected | 0.067 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 556.0 | 556.0 | +0.011 | +0.0019% | +0.57 | 2.37 (crop 38) | 1.93 | 2.04 | no leak detected | 0.090 |
| compress (copy inlined into the wrapper) | state and block | 128 | 200459 | 199541 | 160.8 | 160.8 | -0.004 | -0.0024% | -0.91 | 2.05 (crop 32) | 1.85 | 1.89 | no leak detected | 0.032 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 199841 | 200159 | 164.7 | 164.7 | -0.001 | -0.0007% | -0.14 | 1.69 (crop 57) | 1.12 | 2.14 | no leak detected | 0.032 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 128 | 199796 | 200204 | 165.4 | 165.4 | +0.002 | +0.0009% | -0.87 | 1.63 (crop 0) | 1.87 | 1.24 | no leak detected | 0.031 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 99638 | 100362 | 2531.2 | 2531.2 | +0.078 | +0.0031% | +0.43 | 1.54 (crop 62) | 2.07 | 2.83 | no leak detected | 0.753 |
| fors_sk_gen | SK.seed | 128 | 200085 | 199915 | 168.9 | 168.9 | +0.004 | +0.0023% | +0.18 | 1.38 (crop 32) | 1.60 | 2.43 | no leak detected | 0.032 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 430.3 | 430.3 | +0.014 | +0.0032% | +1.29 | 2.39 (crop 3) | 1.50 | 1.97 | no leak detected | 0.111 |

## FF/DIT: fixed A vs fixed B, DIT = 1, seed 1001
19:54  up 2 days, 10:13, 4 users, load averages: 2.31 1.77 1.79
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 64 | 199892 | 200108 | 234.4 | 234.4 | +0.003 | +0.0012% | -0.52 | 1.95 (crop 3) | 2.34 | 1.66 | no leak detected | 0.051 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 219.4 | 219.4 | +0.001 | +0.0006% | -1.10 | 1.41 (crop 45) | 1.74 | 1.90 | no leak detected | 0.039 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 354.2 | 353.5 | +0.007 | +0.0021% | +0.19 | 1.96 (crop 36) | 1.91 | 1.83 | no leak detected | 0.078 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 556.0 | 556.0 | +0.010 | +0.0018% | -0.48 | 2.29 (crop 57) | 1.65 | 1.78 | no leak detected | 0.101 |
| compress (copy inlined into the wrapper) | state and block | 128 | 200459 | 199541 | 160.8 | 160.8 | -0.000 | -0.0001% | -0.82 | 1.20 (crop 0) | 2.17 | 1.85 | no leak detected | 0.036 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 199841 | 200159 | 165.0 | 165.0 | +0.002 | +0.0013% | -0.27 | 1.51 (crop 35) | 2.01 | 2.49 | no leak detected | 0.035 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 128 | 199796 | 200204 | 165.4 | 165.4 | -0.003 | -0.0018% | +0.74 | 2.18 (crop 42) | 1.43 | 1.39 | no leak detected | 0.032 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 99638 | 100362 | 2536.5 | 2536.5 | +0.005 | +0.0002% | -0.93 | 1.53 (crop 58) | 2.27 | 1.69 | no leak detected | 0.650 |
| fors_sk_gen | SK.seed | 128 | 200085 | 199915 | 168.6 | 168.6 | -0.002 | -0.0011% | +0.91 | 1.66 (crop 92) | 1.82 | 2.33 | no leak detected | 0.033 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 435.5 | 435.5 | -0.007 | -0.0017% | -0.23 | 2.22 (crop 54) | 1.41 | 2.67 | no leak detected | 0.109 |

## RR: random vs random (null), seed 1002
19:55  up 2 days, 10:14, 4 users, load averages: 2.20 1.92 1.85
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 205.1 | 205.1 | -0.006 | -0.0030% | +0.77 | 1.75 (crop 8) | 1.63 | 1.52 | no leak detected | 0.040 |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 191.4 | 191.4 | -0.002 | -0.0009% | -1.12 | 1.24 (crop 7) | 1.11 | 1.28 | no leak detected | 0.039 |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 301.4 | 301.4 | -0.080 | -0.0259% | -0.63 | 2.02 (crop 28) | 1.34 | 1.46 | no leak detected | 0.086 |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 474.6 | 474.6 | +0.099 | +0.0204% | -0.25 | 1.60 (crop 14) | 1.70 | 1.80 | no leak detected | 0.119 |
| compress (copy inlined into the wrapper) | state and block | 256 | 200149 | 199851 | 136.1 | 136.1 | +0.007 | +0.0054% | -0.46 | 2.01 (crop 13) | 1.15 | 1.86 | no leak detected | 0.035 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 199922 | 200078 | 141.8 | 141.8 | +0.039 | +0.0269% | +2.57 | 2.69 (crop 74) | 1.64 | 1.33 | no leak detected | 0.037 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199649 | 200351 | 142.3 | 142.3 | +0.025 | +0.0175% | +2.24 | 2.70 (crop 85) | 1.55 | 2.12 | no leak detected | 0.035 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99512 | 100488 | 2028.6 | 2028.6 | +0.031 | +0.0015% | +0.35 | 2.24 (crop 0) | 2.79 | 1.36 | no leak detected | 0.669 |
| fors_sk_gen | SK.seed | 256 | 199797 | 200203 | 146.2 | 146.2 | -0.001 | -0.0009% | -0.57 | 1.25 (crop 3) | 1.51 | 1.26 | no leak detected | 0.035 |
| fors_node/z=0 | SK.seed | 64 | 99927 | 100073 | 368.5 | 368.5 | +0.041 | +0.0110% | +0.70 | 2.51 (crop 0) | 1.29 | 1.39 | no leak detected | 0.126 |

19:57  up 2 days, 10:16, 4 users, load averages: 1.71 1.80 1.81
## ZF: fixed all-zero vs fixed pseudo-random B, seed 1001
19:58  up 2 days, 10:17, 4 users, load averages: 1.48 1.73 1.78
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 64 | 199892 | 200108 | 205.1 | 205.1 | -0.014 | -0.0069% | +1.14 | 2.98 (crop 26) | 2.61 | 1.61 | no leak detected | 0.054 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 189.8 | 190.1 | -0.049 | -0.0260% | -1.95 | 13.50 (crop 23) | 1.48 | 1.05 | **t > 4.5** | 0.039 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 301.4 | 301.4 | +0.182 | +0.0592% | -2.74 | 59.51 (crop 13) | 1.85 | 1.57 | **t > 4.5** | 0.083 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 474.6 | 474.6 | +0.072 | +0.0150% | -2.58 | 34.55 (crop 18) | 2.08 | 1.60 | **t > 4.5** | 0.119 |
| compress (copy inlined into the wrapper) | state and block | 128 | 200459 | 199541 | 135.4 | 136.4 | -1.535 | -1.1188% | -103.61 | 300.43 (crop 16) | 1.81 | 1.20 | **t > 4.5** | 0.037 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 199841 | 200159 | 141.8 | 141.8 | -0.039 | -0.0271% | -2.46 | 3.12 (crop 19) | 1.34 | 2.63 | no leak detected | 0.034 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 199796 | 200204 | 142.3 | 142.4 | +0.476 | +0.3294% | -1.44 | 49.10 (crop 20) | 1.86 | 2.31 | **t > 4.5** | 0.035 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2028.6 | 2028.6 | -0.093 | -0.0046% | -0.47 | 3.68 (crop 14) | 1.57 | 1.60 | no leak detected | 0.624 |
| fors_sk_gen | SK.seed | 256 | 200085 | 199915 | 146.3 | 146.3 | -0.039 | -0.0263% | -0.38 | 5.34 (crop 6) | 2.11 | 1.34 | **t > 4.5** | 0.035 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 371.1 | 371.1 | +0.054 | +0.0144% | -1.43 | 1.72 (crop 17) | 1.24 | 1.66 | no leak detected | 0.127 |

## ZF/DIT: fixed all-zero vs fixed pseudo-random B, DIT = 1, seed 1001
20:00  up 2 days, 10:19, 4 users, load averages: 1.75 1.81 1.81
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 234.4 | 234.4 | +0.002 | +0.0009% | +0.80 | 3.31 (crop 15) | 2.03 | 1.72 | no leak detected | 0.041 |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 219.1 | 219.1 | +0.001 | +0.0004% | +0.74 | 1.29 (crop 45) | 1.74 | 1.38 | no leak detected | 0.038 |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 353.5 | 353.5 | -0.007 | -0.0020% | +0.27 | 1.84 (crop 32) | 2.80 | 1.66 | no leak detected | 0.067 |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 555.3 | 555.3 | -0.012 | -0.0022% | -0.08 | 2.45 (crop 13) | 2.58 | 1.11 | no leak detected | 0.091 |
| compress (copy inlined into the wrapper) | state and block | 128 | 200459 | 199541 | 160.8 | 160.8 | -0.000 | -0.0001% | +0.27 | 2.69 (crop 57) | 1.87 | 1.80 | no leak detected | 0.031 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 199841 | 200159 | 164.7 | 164.7 | +0.001 | +0.0006% | -0.85 | 1.75 (crop 87) | 1.62 | 2.36 | no leak detected | 0.032 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 128 | 199796 | 200204 | 165.4 | 165.4 | -0.003 | -0.0017% | -0.71 | 2.76 (crop 48) | 1.18 | 1.34 | no leak detected | 0.032 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 99638 | 100362 | 2536.5 | 2536.5 | +0.148 | +0.0058% | +1.15 | 2.34 (crop 28) | 1.27 | 1.57 | no leak detected | 0.538 |
| fors_sk_gen | SK.seed | 128 | 200085 | 199915 | 168.9 | 168.9 | -0.003 | -0.0017% | -0.34 | 2.93 (crop 56) | 1.61 | 1.60 | no leak detected | 0.033 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 434.9 | 434.9 | +0.008 | +0.0018% | -0.47 | 1.41 (crop 2) | 1.57 | 1.75 | no leak detected | 0.113 |

20:01  up 2 days, 10:21, 4 users, load averages: 1.74 1.78 1.79
