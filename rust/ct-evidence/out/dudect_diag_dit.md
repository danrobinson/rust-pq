## sha256, DIT=1: fixed-random, fixed = pseudo-random, seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 263.7 | 263.7 | -0.013 | -0.0050% | +0.42 | 2.41 (crop 0) | 1.01 | 1.29 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 245.4 | 245.4 | -0.001 | -0.0003% | +1.90 | 1.90 | 1.40 | 0.98 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199800 | 200200 | 217.8 | 217.8 | -0.037 | -0.0170% | -1.12 | 1.95 (crop 33) | 1.25 | 1.15 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199786 | 200214 | 413.4 | 413.4 | +0.036 | +0.0086% | +0.30 | 1.52 (crop 0) | 0.78 | 0.57 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200374 | 199626 | 383.5 | 383.5 | -0.012 | -0.0031% | +0.28 | 1.92 (crop 0) | 1.47 | 1.19 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 375.7 | 375.7 | +0.011 | +0.0030% | +0.11 | 1.82 (crop 1) | 1.64 | 1.27 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 572.3 | 572.3 | -0.038 | -0.0066% | -0.40 | 2.51 (crop 4) | 1.57 | 1.10 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199874 | 200126 | 890.6 | 890.6 | +0.163 | +0.0182% | +0.00 | 2.10 (crop 44) | 0.89 | 1.23 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 200527 | 199473 | 1645.8 | 1645.8 | -0.050 | -0.0031% | +0.08 | 0.84 (crop 82) | 0.79 | 0.97 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100001 | 99999 | 1013.0 | 1013.0 | +0.215 | +0.0218% | -0.36 | 1.85 (crop 1) | 0.90 | 1.41 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 100101 | 99899 | 1380.2 | 1380.2 | +0.092 | +0.0067% | +0.04 | 2.01 (crop 2) | 2.09 | 1.35 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100528 | 99472 | 1145.8 | 1145.8 | -0.075 | -0.0065% | -0.50 | 2.44 (crop 42) | 1.23 | 1.22 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99698 | 100302 | 970.1 | 970.1 | +0.009 | +0.0010% | -0.36 | 1.54 (crop 36) | 1.41 | 1.45 | no leak detected |
## sha256, DIT=1: fixed-random, fixed = all-zero, seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 238.0 | 238.0 | +0.023 | +0.0099% | +0.03 | 1.84 (crop 42) | 1.35 | 1.32 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 224.6 | 224.6 | -0.007 | -0.0029% | -0.95 | 1.78 (crop 0) | 1.71 | 0.91 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199800 | 200200 | 204.8 | 204.8 | -0.024 | -0.0119% | -0.73 | 2.22 (crop 7) | 0.87 | 1.02 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199786 | 200214 | 412.1 | 412.1 | +0.022 | +0.0053% | -0.22 | 1.88 (crop 7) | 1.00 | 1.04 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200374 | 199626 | 376.3 | 376.3 | +0.000 | +0.0000% | +0.25 | 1.36 (crop 48) | 1.96 | 2.41 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 367.2 | 367.2 | +0.041 | +0.0112% | +0.44 | 1.46 (crop 32) | 1.12 | 1.17 | no leak detected |
| sha256/len=120 | all message bytes | 32 | 200379 | 199621 | 552.1 | 552.1 | -0.002 | -0.0004% | -0.30 | 0.89 (crop 48) | 1.01 | 1.32 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199874 | 200126 | 898.4 | 898.4 | +0.114 | +0.0126% | +0.38 | 1.84 (crop 13) | 1.46 | 1.81 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 200527 | 199473 | 1549.5 | 1549.5 | -0.022 | -0.0014% | +0.04 | 2.78 (crop 4) | 1.09 | 1.73 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100001 | 99999 | 957.0 | 957.0 | +0.057 | +0.0059% | +0.90 | 2.57 (crop 18) | 1.08 | 1.32 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 100101 | 99899 | 1304.7 | 1304.7 | +0.051 | +0.0039% | +0.02 | 1.54 (crop 39) | 1.61 | 1.70 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100528 | 99472 | 1127.6 | 1127.6 | -0.016 | -0.0015% | +0.17 | 1.97 (crop 44) | 2.13 | 2.27 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99698 | 100302 | 974.0 | 974.0 | -0.127 | -0.0130% | +0.76 | 2.54 (crop 27) | 1.57 | 1.76 | no leak detected |
## sha256, DIT=1: fixed-random, fixed = pseudo-random, seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 241.2 | 241.2 | -0.001 | -0.0003% | -0.12 | 0.81 (crop 6) | 1.14 | 1.24 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 225.9 | 225.9 | -0.001 | -0.0005% | +1.60 | 1.60 | 1.43 | 1.46 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199920 | 200080 | 203.1 | 203.1 | -0.004 | -0.0020% | -1.43 | 1.55 (crop 3) | 1.07 | 1.17 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199907 | 200093 | 404.3 | 404.3 | -0.023 | -0.0058% | -0.20 | 1.72 (crop 42) | 0.97 | 1.12 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200452 | 199548 | 376.3 | 376.3 | -0.003 | -0.0008% | -0.09 | 2.27 (crop 44) | 1.95 | 1.65 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 369.8 | 369.8 | -0.003 | -0.0008% | -0.79 | 1.30 (crop 9) | 1.21 | 2.28 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 584.6 | 584.6 | -0.069 | -0.0121% | -0.42 | 2.76 (crop 4) | 0.89 | 1.55 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199639 | 200361 | 895.8 | 895.8 | +0.013 | +0.0015% | -0.20 | 1.35 (crop 26) | 1.72 | 1.57 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 199522 | 200478 | 1544.3 | 1544.3 | +0.038 | +0.0025% | +0.41 | 1.61 (crop 18) | 1.99 | 1.23 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100042 | 99958 | 971.4 | 971.4 | -0.126 | -0.0129% | -1.51 | 2.29 (crop 32) | 2.06 | 0.75 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 99690 | 100310 | 1309.9 | 1309.9 | +0.223 | +0.0170% | +0.71 | 2.82 (crop 29) | 1.12 | 1.59 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100073 | 99927 | 1134.1 | 1134.1 | -0.095 | -0.0083% | -0.94 | 2.50 (crop 61) | 1.17 | 2.07 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 100008 | 99992 | 967.4 | 967.4 | +0.313 | +0.0321% | +1.71 | 2.93 (crop 25) | 1.91 | 1.61 | no leak detected |
## sha256, DIT=1: fixed-random, fixed = all-zero, seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = all-zero secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 241.2 | 241.2 | -0.007 | -0.0031% | +0.12 | 1.48 (crop 11) | 1.12 | 1.05 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 227.5 | 227.5 | +0.012 | +0.0054% | +0.05 | 1.34 (crop 13) | 1.31 | 0.95 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199920 | 200080 | 202.8 | 202.8 | -0.008 | -0.0038% | -1.72 | 2.53 (crop 78) | 1.66 | 1.04 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199907 | 200093 | 407.6 | 407.6 | +0.000 | +0.0001% | -1.20 | 2.32 (crop 2) | 1.08 | 1.23 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200452 | 199548 | 382.2 | 382.2 | +0.015 | +0.0040% | +0.59 | 1.43 (crop 64) | 1.38 | 1.18 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 367.8 | 367.8 | -0.044 | -0.0121% | -1.43 | 2.07 (crop 56) | 1.14 | 0.77 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 559.2 | 559.2 | -0.057 | -0.0102% | -0.45 | 1.80 (crop 46) | 1.60 | 1.00 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199639 | 200361 | 893.2 | 893.2 | -0.080 | -0.0090% | -0.35 | 2.64 (crop 18) | 2.23 | 1.53 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 199522 | 200478 | 1567.7 | 1565.1 | +0.163 | +0.0104% | +0.20 | 1.78 (crop 18) | 1.43 | 0.75 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100042 | 99958 | 954.4 | 954.4 | -0.052 | -0.0055% | +0.94 | 2.07 (crop 54) | 2.14 | 1.37 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 99690 | 100310 | 1328.1 | 1328.1 | +0.026 | +0.0020% | +1.41 | 2.11 (crop 51) | 1.25 | 1.28 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100073 | 99927 | 1126.3 | 1126.3 | +0.025 | +0.0022% | +0.97 | 2.40 (crop 1) | 1.77 | 2.12 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 100008 | 99992 | 960.9 | 960.9 | -0.031 | -0.0032% | -0.96 | 2.33 (crop 49) | 2.41 | 2.20 | no leak detected |
