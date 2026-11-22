## RR: random vs random (null), seed 1001
21:33  up 2 days, 11:52, 4 users, load averages: 2.41 1.85 1.73
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 90.5 | 90.5 | -0.006 | -0.0064% | +0.18 | 1.21 (crop 35) | 1.01 | 0.89 | no leak detected | 0.019 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 74.9 | 74.9 | -0.003 | -0.0046% | -0.61 | 2.23 (crop 21) | 1.22 | 1.25 | no leak detected | 0.016 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 62.7 | 62.7 | +0.021 | +0.0332% | +1.38 | 2.27 (crop 33) | 1.30 | 1.04 | no leak detected | 0.020 |
| sha256/len=120 | all message bytes | 256 | 200379 | 199621 | 116.7 | 116.7 | -0.011 | -0.0091% | -0.48 | 1.84 (crop 11) | 1.07 | 0.86 | no leak detected | 0.026 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 15.7 | 15.7 | -0.000 | -0.0008% | +0.32 | 1.72 (crop 49) | 2.54 | 2.59 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199841 | 200159 | 25.6 | 25.6 | -0.001 | -0.0046% | -0.54 | 1.73 (crop 58) | 1.33 | 2.09 | no leak detected | 0.009 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 24.7 | 24.7 | -0.005 | -0.0181% | -0.60 | 1.62 (crop 43) | 1.15 | 1.22 | no leak detected | 0.010 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | +0.003 | +0.0009% | -1.20 | 1.36 (crop 71) | 1.45 | 1.40 | no leak detected | 0.074 |
| fors_sk_gen | SK.seed | 1024 | 200085 | 199915 | 25.2 | 25.2 | -0.001 | -0.0021% | +0.56 | 2.19 (crop 56) | 1.63 | 1.78 | no leak detected | 0.010 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 155.9 | 156.2 | -0.085 | -0.0524% | +0.60 | 2.57 (crop 17) | 1.03 | 0.79 | no leak detected | 0.240 |

## FF: fixed A vs fixed B, seed 1001
21:35  up 2 days, 11:54, 4 users, load averages: 2.59 2.09 1.83
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 89.7 | 89.7 | -0.006 | -0.0069% | -0.72 | 1.89 (crop 7) | 1.03 | 1.01 | no leak detected | 0.019 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 74.5 | 74.5 | -0.001 | -0.0010% | -0.25 | 2.47 (crop 41) | 2.18 | 0.92 | no leak detected | 0.017 |
| sha256/len=119 | all message bytes | 16 | 200276 | 199724 | 62.5 | 62.5 | -0.007 | -0.0110% | -0.91 | 1.62 (crop 1) | 1.72 | 1.61 | no leak detected | 0.036 |
| sha256/len=120 | all message bytes | 256 | 200379 | 199621 | 116.5 | 116.5 | -0.018 | -0.0150% | -0.52 | 2.32 (crop 44) | 1.04 | 1.71 | no leak detected | 0.026 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 15.7 | 15.7 | +0.001 | +0.0077% | +0.69 | 2.90 (crop 7) | 1.57 | 1.41 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199841 | 200159 | 25.3 | 25.3 | +0.002 | +0.0071% | +0.13 | 2.05 (crop 26) | 1.43 | 1.16 | no leak detected | 0.010 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 24.8 | 24.8 | -0.006 | -0.0239% | -1.54 | 1.98 (crop 97) | 1.46 | 1.48 | no leak detected | 0.013 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | -0.009 | -0.0027% | -0.88 | 1.71 (crop 21) | 1.57 | 1.93 | no leak detected | 0.079 |
| fors_sk_gen | SK.seed | 1024 | 200085 | 199915 | 25.2 | 25.2 | +0.000 | +0.0008% | +0.86 | 1.95 (crop 11) | 2.03 | 1.87 | no leak detected | 0.011 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 162.1 | 162.4 | -0.038 | -0.0234% | -1.04 | 2.17 (crop 15) | 0.47 | 0.67 | no leak detected | 0.101 |

## FF: fixed A vs fixed B, seed 1002
21:36  up 2 days, 11:55, 4 users, load averages: 2.89 2.26 1.92
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199563 | 200437 | 91.6 | 91.6 | +0.002 | +0.0019% | +0.28 | 1.81 (crop 1) | 1.51 | 0.93 | no leak detected | 0.018 |
| sha256/len=16 | all message bytes | 256 | 200053 | 199947 | 75.2 | 75.2 | +0.004 | +0.0056% | +0.50 | 2.14 (crop 59) | 1.05 | 1.39 | no leak detected | 0.016 |
| sha256/len=119 | all message bytes | 256 | 200279 | 199721 | 62.7 | 62.7 | +0.005 | +0.0086% | +0.69 | 2.11 (crop 24) | 0.88 | 2.26 | no leak detected | 0.019 |
| sha256/len=120 | all message bytes | 256 | 200138 | 199862 | 116.7 | 116.7 | +0.019 | +0.0162% | +0.91 | 2.03 (crop 5) | 1.51 | 0.82 | no leak detected | 0.025 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200149 | 199851 | 15.7 | 15.7 | -0.001 | -0.0035% | -0.65 | 2.78 (crop 50) | 1.77 | 1.02 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199922 | 200078 | 25.3 | 25.3 | -0.000 | -0.0007% | +1.82 | 2.39 (crop 67) | 1.50 | 1.95 | no leak detected | 0.009 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199649 | 200351 | 24.7 | 24.7 | +0.001 | +0.0027% | +0.68 | 1.49 (crop 11) | 2.86 | 1.10 | no leak detected | 0.010 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99512 | 100488 | 315.1 | 315.1 | -0.005 | -0.0015% | -0.01 | 2.42 (crop 43) | 1.63 | 1.02 | no leak detected | 0.076 |
| fors_sk_gen | SK.seed | 1024 | 199797 | 200203 | 25.1 | 25.1 | -0.001 | -0.0043% | +1.50 | 2.27 (crop 36) | 2.57 | 1.18 | no leak detected | 0.010 |
| fors_node/z=0 | SK.seed | 128 | 99927 | 100073 | 157.9 | 157.9 | +0.025 | +0.0155% | -1.92 | 2.18 (crop 99) | 0.82 | 0.74 | no leak detected | 0.110 |

## FR: fixed (pseudo-random) vs random, seed 1001
21:38  up 2 days, 11:57, 4 users, load averages: 2.45 2.31 1.97
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 91.6 | 91.8 | -0.031 | -0.0339% | -3.22 | 8.94 (crop 14) | 0.92 | 0.90 | **t > 4.5** | 0.020 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 75.5 | 75.5 | -0.006 | -0.0077% | -0.68 | 1.60 (crop 0) | 0.86 | 1.52 | no leak detected | 0.017 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 62.8 | 62.8 | -0.007 | -0.0105% | +0.26 | 2.67 (crop 9) | 1.37 | 1.69 | no leak detected | 0.020 |
| sha256/len=120 | all message bytes | 256 | 200379 | 199621 | 116.9 | 116.9 | -0.017 | -0.0140% | -0.53 | 1.80 (crop 35) | 1.66 | 1.02 | no leak detected | 0.025 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 15.8 | 15.8 | -0.000 | -0.0002% | -1.49 | 2.43 (crop 26) | 1.57 | 1.93 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199841 | 200159 | 25.3 | 25.3 | +0.000 | +0.0012% | +1.49 | 2.08 (crop 10) | 1.81 | 1.75 | no leak detected | 0.011 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 24.7 | 24.7 | -0.001 | -0.0049% | -0.14 | 1.26 (crop 20) | 1.53 | 1.29 | no leak detected | 0.011 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 314.5 | 314.5 | +0.009 | +0.0030% | -0.40 | 1.66 (crop 29) | 1.61 | 1.68 | no leak detected | 0.075 |
| fors_sk_gen | SK.seed | 1024 | 200085 | 199915 | 25.1 | 25.1 | +0.000 | +0.0017% | +1.06 | 1.46 (crop 88) | 2.11 | 1.56 | no leak detected | 0.008 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 156.6 | 156.6 | +0.043 | +0.0270% | -0.12 | 2.64 (crop 29) | 0.80 | 1.15 | no leak detected | 0.091 |

## FR/same: fixed (pseudo-random) vs random, same preparation path, seed 1001
21:39  up 2 days, 11:58, 4 users, load averages: 2.50 2.38 2.03
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 90.8 | 90.8 | -0.056 | -0.0616% | -1.25 | 13.09 (crop 21) | 0.95 | 1.30 | **t > 4.5** | 0.020 |
| sha256/len=16 | all message bytes | 512 | 199899 | 200101 | 74.6 | 74.6 | -0.000 | -0.0006% | +0.26 | 2.51 (crop 6) | 1.07 | 0.98 | no leak detected | 0.015 |
| sha256/len=119 | all message bytes | 512 | 200276 | 199724 | 63.2 | 63.2 | -0.005 | -0.0070% | +0.13 | 1.45 (crop 21) | 1.04 | 1.64 | no leak detected | 0.017 |
| sha256/len=120 | all message bytes | 256 | 200379 | 199621 | 116.9 | 116.9 | -0.008 | -0.0067% | -0.28 | 2.02 (crop 0) | 1.20 | 0.97 | no leak detected | 0.026 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 15.7 | 15.7 | +0.001 | +0.0051% | -0.47 | 1.10 (crop 9) | 1.25 | 2.46 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199841 | 200159 | 25.3 | 25.3 | -0.003 | -0.0108% | -1.09 | 1.70 (crop 34) | 1.40 | 1.33 | no leak detected | 0.012 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 24.7 | 24.7 | +0.002 | +0.0085% | -0.39 | 1.64 (crop 41) | 1.54 | 1.31 | no leak detected | 0.011 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 313.8 | 313.8 | +0.005 | +0.0015% | +0.12 | 1.80 (crop 4) | 2.06 | 1.39 | no leak detected | 0.076 |
| fors_sk_gen | SK.seed | 1024 | 200085 | 199915 | 25.2 | 25.2 | -0.000 | -0.0011% | +0.09 | 2.76 (crop 10) | 1.52 | 1.11 | no leak detected | 0.010 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 156.6 | 156.9 | -0.001 | -0.0007% | -1.28 | 1.57 (crop 0) | 1.09 | 1.27 | no leak detected | 0.071 |

## FR/x8: fixed (pseudo-random) vs random, 8 x calls per measurement, seed 1001
21:41  up 2 days, 12 hrs, 4 users, load averages: 2.78 2.46 2.10
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001; calls per measurement = 8 x calibrated

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 2048 | 49975 | 50025 | 89.1 | 89.1 | -0.000 | -0.0003% | -0.59 | 2.51 (crop 8) | 1.39 | 1.12 | no leak detected | 0.027 |
| sha256/len=16 | all message bytes | 4096 | 50197 | 49803 | 74.0 | 74.0 | -0.002 | -0.0028% | -0.13 | 1.50 (crop 50) | 1.75 | 2.08 | no leak detected | 0.025 |
| sha256/len=119 | all message bytes | 2048 | 49965 | 50035 | 62.6 | 62.6 | -0.003 | -0.0044% | -1.33 | 1.37 (crop 67) | 2.76 | 1.35 | no leak detected | 0.033 |
| sha256/len=120 | all message bytes | 2048 | 50036 | 49964 | 116.7 | 116.7 | -0.016 | -0.0135% | -0.34 | 1.38 (crop 22) | 2.01 | 1.43 | no leak detected | 0.040 |
| compress (copy inlined into the wrapper) | state and block | 16384 | 50123 | 49877 | 15.8 | 15.8 | -0.002 | -0.0100% | -1.12 | 2.04 (crop 36) | 1.78 | 2.27 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 8192 | 50007 | 49993 | 25.1 | 25.1 | -0.000 | -0.0000% | +0.88 | 2.25 (crop 6) | 1.41 | 1.21 | no leak detected | 0.018 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 8192 | 49841 | 50159 | 25.2 | 25.1 | +0.008 | +0.0326% | -0.61 | 1.53 (crop 33) | 2.05 | 1.46 | no leak detected | 0.020 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 512 | 24776 | 25224 | 314.5 | 314.5 | -0.009 | -0.0027% | -1.53 | 2.48 (crop 40) | 1.84 | 1.59 | no leak detected | 0.071 |
| fors_sk_gen | SK.seed | 8192 | 50013 | 49987 | 25.1 | 25.1 | +0.002 | +0.0085% | -0.00 | 2.22 (crop 25) | 1.34 | 2.55 | no leak detected | 0.019 |
| fors_node/z=0 | SK.seed | 1024 | 24875 | 25125 | 153.0 | 152.7 | +0.048 | +0.0309% | +1.09 | 1.77 (crop 44) | 0.73 | 1.24 | no leak detected | 0.274 |

## FZ: fixed (all-zero) vs random, seed 1001
21:44  up 2 days, 12:04, 4 users, load averages: 2.95 2.76 2.29
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 90.5 | 90.5 | -0.046 | -0.0508% | -4.07 | 9.27 (crop 27) | 0.67 | 0.99 | **t > 4.5** | 0.019 |
| sha256/len=16 | all message bytes | 512 | 199899 | 200101 | 74.4 | 74.4 | +0.020 | +0.0276% | +1.31 | 5.47 (crop 1) | 1.88 | 1.09 | **t > 4.5** | 0.016 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 63.0 | 63.0 | -0.031 | -0.0488% | -2.53 | 21.26 (crop 19) | 1.23 | 1.38 | **t > 4.5** | 0.020 |
| sha256/len=120 | all message bytes | 256 | 200379 | 199621 | 116.9 | 116.9 | -0.021 | -0.0173% | -0.87 | 3.26 (crop 7) | 1.01 | 1.56 | no leak detected | 0.027 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 15.7 | 15.7 | -0.000 | -0.0024% | +0.23 | 2.19 (crop 31) | 1.75 | 1.54 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199841 | 200159 | 25.2 | 25.2 | +0.016 | +0.0629% | +0.76 | 13.07 (crop 19) | 1.29 | 1.67 | **t > 4.5** | 0.010 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 24.7 | 24.7 | -0.001 | -0.0050% | -0.19 | 2.98 (crop 1) | 1.54 | 1.88 | no leak detected | 0.010 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 314.5 | 314.5 | +0.003 | +0.0009% | +1.88 | 2.42 (crop 98) | 2.14 | 1.29 | no leak detected | 0.073 |
| fors_sk_gen | SK.seed | 1024 | 200085 | 199915 | 25.2 | 25.2 | +0.019 | +0.0759% | +2.10 | 28.29 (crop 28) | 1.29 | 1.51 | **t > 4.5** | 0.009 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 159.5 | 159.5 | +0.010 | +0.0062% | +0.60 | 1.98 (crop 12) | 0.73 | 0.78 | no leak detected | 0.091 |

## FR/DIT: fixed (pseudo-random) vs random, DIT = 1, seed 1001
21:46  up 2 days, 12:05, 4 users, load averages: 2.46 2.66 2.30
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 110.2 | 110.2 | -0.004 | -0.0038% | -0.29 | 2.18 (crop 53) | 1.39 | 0.70 | no leak detected | 0.017 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 89.8 | 89.7 | +0.003 | +0.0032% | +1.80 | 3.72 (crop 54) | 1.32 | 1.77 | no leak detected | 0.015 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 77.1 | 77.1 | +0.001 | +0.0018% | -0.36 | 1.45 (crop 37) | 1.69 | 1.38 | no leak detected | 0.015 |
| sha256/len=120 | all message bytes | 128 | 200379 | 199621 | 141.9 | 142.3 | -0.008 | -0.0056% | -0.44 | 1.81 (crop 28) | 1.32 | 1.35 | no leak detected | 0.027 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 17.5 | 17.5 | -0.000 | -0.0011% | +0.05 | 1.09 (crop 22) | 2.59 | 2.34 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 512 | 199841 | 200159 | 38.2 | 38.2 | -0.000 | -0.0012% | +0.69 | 2.71 (crop 20) | 1.24 | 2.05 | no leak detected | 0.007 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 512 | 199796 | 200204 | 37.4 | 37.4 | +0.007 | +0.0173% | +1.06 | 2.82 (crop 11) | 1.26 | 1.40 | no leak detected | 0.008 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | -0.004 | -0.0013% | +0.56 | 2.08 (crop 15) | 2.87 | 1.90 | no leak detected | 0.074 |
| fors_sk_gen | SK.seed | 512 | 200085 | 199915 | 37.4 | 37.4 | +0.001 | +0.0022% | +1.90 | 3.13 (crop 11) | 1.77 | 1.74 | no leak detected | 0.007 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 158.9 | 158.9 | +0.053 | +0.0323% | +0.14 | 1.52 (crop 43) | 0.75 | 0.77 | no leak detected | 0.234 |

## FZ/DIT: fixed (all-zero) vs random, DIT = 1, seed 1001
21:48  up 2 days, 12:07, 4 users, load averages: 2.39 2.58 2.31
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 114.9 | 114.9 | +0.004 | +0.0036% | +0.45 | 1.92 (crop 50) | 1.37 | 2.21 | no leak detected | 0.018 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 92.6 | 92.6 | -0.001 | -0.0010% | +0.39 | 1.66 (crop 69) | 2.38 | 1.32 | no leak detected | 0.016 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 76.8 | 76.8 | +0.001 | +0.0009% | +1.09 | 1.74 (crop 64) | 1.70 | 1.31 | no leak detected | 0.013 |
| sha256/len=120 | all message bytes | 128 | 200379 | 199621 | 142.9 | 142.9 | -0.001 | -0.0010% | -1.52 | 2.67 (crop 38) | 1.39 | 1.64 | no leak detected | 0.024 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 17.5 | 17.5 | -0.000 | -0.0023% | -0.79 | 2.30 (crop 30) | 1.87 | 2.27 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 512 | 199841 | 200159 | 39.3 | 39.3 | -0.000 | -0.0011% | +1.16 | 2.08 (crop 91) | 1.59 | 1.68 | no leak detected | 0.007 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 512 | 199796 | 200204 | 37.5 | 37.5 | -0.000 | -0.0008% | -1.06 | 2.05 (crop 7) | 0.93 | 1.12 | no leak detected | 0.008 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | -0.001 | -0.0002% | -1.34 | 1.68 (crop 5) | 1.53 | 0.98 | no leak detected | 0.074 |
| fors_sk_gen | SK.seed | 512 | 200085 | 199915 | 37.4 | 37.4 | +0.000 | +0.0011% | -2.95 | 2.95 | 1.15 | 1.41 | no leak detected | 0.007 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 156.2 | 156.2 | -0.002 | -0.0012% | -1.69 | 2.83 (crop 65) | 1.42 | 1.29 | no leak detected | 0.094 |

## FF/DIT: fixed A vs fixed B, DIT = 1, seed 1001
21:49  up 2 days, 12:08, 4 users, load averages: 2.37 2.52 2.31
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 109.9 | 109.9 | -0.007 | -0.0060% | +0.02 | 1.50 (crop 55) | 0.84 | 0.95 | no leak detected | 0.018 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 90.0 | 90.0 | -0.001 | -0.0011% | +2.41 | 2.66 (crop 95) | 2.22 | 1.68 | no leak detected | 0.015 |
| sha256/len=119 | all message bytes | 16 | 200276 | 199724 | 78.1 | 78.1 | +0.003 | +0.0035% | +1.42 | 1.42 | 1.83 | 1.60 | no leak detected | 0.037 |
| sha256/len=120 | all message bytes | 256 | 200379 | 199621 | 140.8 | 140.8 | +0.003 | +0.0023% | -0.44 | 2.00 (crop 15) | 1.31 | 1.08 | no leak detected | 0.019 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 17.5 | 17.5 | +0.000 | +0.0002% | -0.46 | 2.32 (crop 74) | 2.01 | 1.08 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 512 | 199841 | 200159 | 38.2 | 38.2 | +0.002 | +0.0059% | +1.37 | 1.57 (crop 95) | 1.28 | 2.10 | no leak detected | 0.006 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 512 | 199796 | 200204 | 37.3 | 37.3 | -0.000 | -0.0012% | -0.08 | 1.67 (crop 8) | 1.52 | 1.72 | no leak detected | 0.008 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | +0.006 | +0.0018% | -1.05 | 1.80 (crop 23) | 2.26 | 1.69 | no leak detected | 0.073 |
| fors_sk_gen | SK.seed | 512 | 200085 | 199915 | 37.4 | 37.4 | +0.000 | +0.0007% | +1.16 | 1.56 (crop 38) | 1.40 | 0.85 | no leak detected | 0.006 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 158.2 | 158.2 | -0.019 | -0.0120% | -0.89 | 2.16 (crop 22) | 1.53 | 1.04 | no leak detected | 0.111 |

## RR: random vs random (null), seed 1002
21:50  up 2 days, 12:10, 4 users, load averages: 2.52 2.55 2.34
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199563 | 200437 | 89.5 | 89.5 | +0.004 | +0.0050% | +1.54 | 1.79 (crop 2) | 1.79 | 0.84 | no leak detected | 0.018 |
| sha256/len=16 | all message bytes | 512 | 200053 | 199947 | 73.7 | 73.8 | -0.010 | -0.0139% | -1.18 | 2.47 (crop 34) | 1.36 | 1.21 | no leak detected | 0.015 |
| sha256/len=119 | all message bytes | 256 | 200279 | 199721 | 62.8 | 62.8 | -0.011 | -0.0179% | +0.03 | 2.11 (crop 17) | 2.10 | 2.02 | no leak detected | 0.019 |
| sha256/len=120 | all message bytes | 256 | 200138 | 199862 | 115.9 | 115.9 | -0.027 | -0.0230% | -1.51 | 2.92 (crop 40) | 1.09 | 0.98 | no leak detected | 0.026 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200149 | 199851 | 15.7 | 15.7 | -0.000 | -0.0018% | +0.44 | 1.38 (crop 4) | 1.79 | 1.75 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199922 | 200078 | 25.6 | 25.6 | +0.000 | +0.0012% | +2.00 | 2.80 (crop 50) | 1.58 | 2.10 | no leak detected | 0.010 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199649 | 200351 | 24.7 | 24.7 | -0.001 | -0.0051% | -1.10 | 1.69 (crop 49) | 2.18 | 1.71 | no leak detected | 0.010 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99512 | 100488 | 315.1 | 315.1 | +0.005 | +0.0016% | +0.07 | 1.92 (crop 40) | 2.32 | 1.13 | no leak detected | 0.079 |
| fors_sk_gen | SK.seed | 1024 | 199797 | 200203 | 25.1 | 25.1 | -0.000 | -0.0012% | +0.45 | 1.89 (crop 0) | 2.25 | 1.15 | no leak detected | 0.010 |
| fors_node/z=0 | SK.seed | 128 | 99927 | 100073 | 158.2 | 158.2 | -0.050 | -0.0313% | -0.82 | 2.27 (crop 43) | 0.55 | 0.84 | no leak detected | 0.096 |

## ZF: fixed all-zero vs fixed pseudo-random B, seed 1001
21:52  up 2 days, 12:11, 4 users, load averages: 2.66 2.62 2.39
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 89.7 | 89.7 | +0.000 | +0.0001% | +1.08 | 1.08 | 1.12 | 1.11 | no leak detected | 0.020 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 74.4 | 74.5 | -0.028 | -0.0379% | -1.45 | 9.38 (crop 13) | 1.29 | 1.08 | **t > 4.5** | 0.016 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 62.5 | 62.5 | -0.029 | -0.0453% | -4.75 | 37.15 (crop 20) | 1.90 | 1.64 | **t > 4.5** | 0.019 |
| sha256/len=120 | all message bytes | 128 | 200379 | 199621 | 116.5 | 116.5 | -0.056 | -0.0471% | -3.33 | 18.64 (crop 18) | 1.82 | 1.10 | **t > 4.5** | 0.028 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 15.7 | 15.7 | -0.000 | -0.0031% | +0.55 | 2.36 (crop 5) | 1.19 | 1.36 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 199841 | 200159 | 25.3 | 25.2 | +0.021 | +0.0815% | +2.75 | 11.51 (crop 34) | 2.51 | 1.70 | **t > 4.5** | 0.011 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 24.7 | 24.7 | -0.004 | -0.0164% | +0.14 | 2.64 (crop 5) | 1.16 | 1.21 | no leak detected | 0.011 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | -0.001 | -0.0004% | +0.38 | 2.15 (crop 40) | 2.01 | 1.84 | no leak detected | 0.074 |
| fors_sk_gen | SK.seed | 1024 | 200085 | 199915 | 25.2 | 25.1 | +0.022 | +0.0877% | +3.89 | 29.30 (crop 29) | 0.83 | 1.61 | **t > 4.5** | 0.009 |
| fors_node/z=0 | SK.seed | 64 | 99730 | 100270 | 158.2 | 158.2 | +0.002 | +0.0010% | -0.30 | 2.22 (crop 11) | 0.58 | 0.76 | no leak detected | 0.143 |

## ZF/DIT: fixed all-zero vs fixed pseudo-random B, DIT = 1, seed 1001
21:53  up 2 days, 12:13, 4 users, load averages: 2.42 2.56 2.39
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-fixed; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 199892 | 200108 | 110.4 | 110.4 | +0.004 | +0.0035% | -0.74 | 1.67 (crop 2) | 1.26 | 1.42 | no leak detected | 0.016 |
| sha256/len=16 | all message bytes | 256 | 199899 | 200101 | 90.0 | 90.0 | +0.001 | +0.0014% | -0.29 | 1.90 (crop 44) | 1.27 | 1.02 | no leak detected | 0.014 |
| sha256/len=119 | all message bytes | 256 | 200276 | 199724 | 76.8 | 76.8 | -0.003 | -0.0043% | +0.32 | 2.65 (crop 39) | 2.13 | 1.07 | no leak detected | 0.013 |
| sha256/len=120 | all message bytes | 128 | 200379 | 199621 | 140.6 | 140.6 | -0.005 | -0.0037% | -0.42 | 2.56 (crop 40) | 1.78 | 1.29 | no leak detected | 0.023 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 200459 | 199541 | 17.5 | 17.5 | +0.000 | +0.0013% | -0.30 | 2.06 (crop 37) | 2.32 | 1.94 | no leak detected | 0.002 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 512 | 199841 | 200159 | 38.2 | 38.2 | -0.000 | -0.0004% | +0.27 | 1.79 (crop 11) | 1.61 | 1.36 | no leak detected | 0.006 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 199796 | 200204 | 37.2 | 37.2 | +0.003 | +0.0071% | +0.42 | 1.19 (crop 47) | 1.34 | 1.23 | no leak detected | 0.007 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 99638 | 100362 | 315.1 | 315.1 | -0.019 | -0.0061% | +0.28 | 2.69 (crop 55) | 2.13 | 1.99 | no leak detected | 0.081 |
| fors_sk_gen | SK.seed | 512 | 200085 | 199915 | 37.4 | 37.4 | +0.001 | +0.0023% | +0.27 | 1.77 (crop 28) | 2.50 | 1.92 | no leak detected | 0.007 |
| fors_node/z=0 | SK.seed | 128 | 99730 | 100270 | 153.0 | 153.0 | -0.043 | -0.0276% | -0.47 | 2.38 (crop 1) | 2.20 | 1.34 | no leak detected | 0.088 |

21:55  up 2 days, 12:14, 4 users, load averages: 2.81 2.62 2.42
