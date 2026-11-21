## sha256: random-random (true null), seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 199892 | 200108 | 208.3 | 208.3 | +0.015 | +0.0064% | -0.81 | 2.20 (crop 0) | 0.95 | 1.01 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 187.8 | 187.8 | +0.004 | +0.0024% | -0.41 | 1.38 (crop 9) | 1.43 | 1.97 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199800 | 200200 | 163.7 | 163.7 | +0.039 | +0.0232% | +0.24 | 2.52 (crop 42) | 1.90 | 1.06 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199786 | 200214 | 335.9 | 335.9 | +0.077 | +0.0227% | +2.03 | 3.60 (crop 47) | 1.03 | 1.14 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200374 | 199626 | 315.8 | 315.8 | -0.047 | -0.0147% | +0.63 | 2.06 (crop 2) | 1.27 | 1.14 | no leak detected |
| sha256/len=119 | all message bytes | 128 | 200276 | 199724 | 304.4 | 304.4 | -0.030 | -0.0097% | -0.47 | 1.79 (crop 8) | 0.90 | 0.81 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 449.9 | 449.9 | +0.012 | +0.0027% | +1.34 | 2.02 (crop 4) | 1.22 | 1.42 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199874 | 200126 | 725.3 | 725.3 | -0.014 | -0.0019% | +2.17 | 2.77 (crop 1) | 1.42 | 2.65 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 200527 | 199473 | 1250.0 | 1250.0 | -0.055 | -0.0044% | -0.77 | 1.51 (crop 0) | 2.30 | 1.54 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100001 | 99999 | 799.5 | 799.5 | -0.010 | -0.0013% | -0.42 | 2.80 (crop 1) | 1.41 | 1.18 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 100101 | 99899 | 1108.1 | 1108.1 | -0.141 | -0.0126% | +0.27 | 1.37 (crop 18) | 1.45 | 1.13 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100528 | 99472 | 936.2 | 936.2 | -0.136 | -0.0144% | +2.64 | 2.64 | 1.37 | 1.45 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99698 | 100302 | 802.1 | 802.1 | +0.263 | +0.0325% | +0.67 | 2.71 (crop 17) | 1.14 | 1.35 | no leak detected |
## sha256: fixed-fixed (two different fixed pseudo-random secrets), seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 210.9 | 211.3 | -0.001 | -0.0003% | -0.86 | 1.43 (crop 84) | 1.30 | 0.89 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 198.9 | 198.9 | -0.048 | -0.0243% | -1.03 | 1.72 (crop 28) | 0.79 | 0.90 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199800 | 200200 | 175.8 | 175.8 | -0.021 | -0.0117% | -0.94 | 2.37 (crop 28) | 1.57 | 0.72 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199786 | 200214 | 359.4 | 359.4 | -0.036 | -0.0097% | -0.14 | 1.24 (crop 26) | 0.93 | 0.39 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200374 | 199626 | 335.9 | 335.9 | +0.027 | +0.0076% | +0.97 | 2.08 (crop 15) | 2.29 | 0.81 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200276 | 199724 | 322.3 | 322.3 | -0.028 | -0.0085% | +0.36 | 2.02 (crop 0) | 1.27 | 0.95 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 483.1 | 483.1 | +0.306 | +0.0596% | +1.49 | 1.94 (crop 31) | 1.04 | 1.53 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199874 | 200126 | 726.6 | 726.6 | -0.038 | -0.0052% | +0.49 | 1.46 (crop 26) | 1.03 | 1.66 | no leak detected |
| sha256/len=560 | all message bytes | 4 | 200527 | 199473 | 1260.4 | 1260.4 | +0.157 | +0.0124% | +0.17 | 2.28 (crop 39) | 1.89 | 0.92 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100001 | 99999 | 790.4 | 790.4 | -0.053 | -0.0067% | +0.60 | 1.93 (crop 0) | 1.63 | 1.09 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 100101 | 99899 | 1083.3 | 1083.3 | -0.240 | -0.0221% | -1.62 | 2.41 (crop 70) | 1.31 | 1.68 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100528 | 99472 | 936.2 | 936.2 | -0.056 | -0.0060% | +2.08 | 2.08 | 1.30 | 1.22 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99698 | 100302 | 803.4 | 803.4 | -0.027 | -0.0034% | -0.58 | 1.08 (crop 1) | 1.27 | 1.44 | no leak detected |
## sha256: fixed-random, fixed = pseudo-random, seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 200.8 | 201.2 | -0.118 | -0.0587% | -2.71 | 27.62 (crop 24) | 1.03 | 1.17 | **t > 4.5** |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 188.8 | 188.8 | -0.062 | -0.0329% | -4.09 | 16.94 (crop 21) | 2.03 | 1.54 | **t > 4.5** |
| sha256/len=55 | all message bytes | 128 | 199800 | 200200 | 166.7 | 166.7 | -0.023 | -0.0139% | -2.60 | 5.97 (crop 15) | 1.25 | 1.05 | **t > 4.5** |
| sha256/len=56 | all message bytes | 64 | 199786 | 200214 | 330.1 | 330.1 | +0.028 | +0.0085% | +0.10 | 11.90 (crop 13) | 1.23 | 1.13 | **t > 4.5** |
| sha256/len=64 | all message bytes | 64 | 200374 | 199626 | 309.9 | 309.9 | -0.009 | -0.0028% | +0.95 | 3.62 (crop 23) | 1.01 | 1.66 | no leak detected |
| sha256/len=119 | all message bytes | 128 | 200276 | 199724 | 298.5 | 298.5 | +0.033 | +0.0111% | +0.67 | 6.25 (crop 0) | 1.32 | 1.06 | **t > 4.5** |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 456.4 | 456.4 | -0.049 | -0.0107% | -0.57 | 3.18 (crop 3) | 2.49 | 1.55 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199874 | 200126 | 726.6 | 726.6 | -0.118 | -0.0161% | +0.19 | 2.64 (crop 3) | 1.21 | 1.65 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 200527 | 199473 | 1273.4 | 1273.4 | +0.259 | +0.0200% | +1.68 | 1.68 | 1.07 | 0.98 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100001 | 99999 | 789.1 | 789.1 | +0.090 | +0.0114% | +1.92 | 3.56 (crop 7) | 1.34 | 1.28 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 100101 | 99899 | 1102.9 | 1102.9 | -0.103 | -0.0093% | +0.08 | 1.29 (crop 42) | 0.87 | 1.35 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100528 | 99472 | 938.8 | 938.8 | -0.172 | -0.0182% | -1.40 | 5.92 (crop 4) | 1.46 | 1.44 | **t > 4.5** |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99698 | 100302 | 816.4 | 816.4 | -0.079 | -0.0096% | -1.16 | 3.12 (crop 0) | 1.28 | 1.29 | no leak detected |
## sha256: fixed-random, fixed = all-zero, seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199892 | 200108 | 202.8 | 202.8 | -0.128 | -0.0627% | -3.37 | 13.85 (crop 3) | 1.42 | 1.17 | **t > 4.5** |
| sha256/len=16 | all message bytes | 128 | 199899 | 200101 | 187.2 | 187.2 | -0.089 | -0.0475% | -2.85 | 19.68 (crop 10) | 1.39 | 1.08 | **t > 4.5** |
| sha256/len=55 | all message bytes | 128 | 199800 | 200200 | 162.8 | 163.1 | -0.192 | -0.1173% | -3.89 | 75.91 (crop 16) | 1.76 | 1.35 | **t > 4.5** |
| sha256/len=56 | all message bytes | 64 | 199786 | 200214 | 331.4 | 331.4 | -0.155 | -0.0465% | -3.36 | 36.56 (crop 19) | 1.51 | 2.14 | **t > 4.5** |
| sha256/len=64 | all message bytes | 64 | 200374 | 199626 | 309.9 | 309.9 | -0.123 | -0.0396% | -2.75 | 21.41 (crop 22) | 1.49 | 1.17 | **t > 4.5** |
| sha256/len=119 | all message bytes | 128 | 200276 | 199724 | 297.5 | 297.9 | -0.323 | -0.1078% | -5.50 | 46.63 (crop 1) | 1.58 | 1.33 | **t > 4.5** |
| sha256/len=120 | all message bytes | 64 | 200379 | 199621 | 458.3 | 459.0 | +0.618 | +0.1315% | -5.06 | 53.17 (crop 11) | 1.28 | 1.15 | **t > 4.5** |
| sha256/len=256 | all message bytes | 32 | 199874 | 200126 | 739.6 | 739.6 | +0.532 | +0.0703% | -2.25 | 40.99 (crop 8) | 1.74 | 0.88 | **t > 4.5** |
| sha256/len=560 | all message bytes | 16 | 200527 | 199473 | 1296.9 | 1296.9 | -0.760 | -0.0578% | -3.85 | 22.76 (crop 5) | 1.03 | 1.10 | **t > 4.5** |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100001 | 99999 | 852.9 | 852.9 | +0.222 | +0.0256% | +0.68 | 2.17 (crop 24) | 0.72 | 1.24 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 100101 | 99899 | 1114.6 | 1114.6 | +0.022 | +0.0020% | +2.69 | 16.90 (crop 10) | 1.31 | 1.44 | **t > 4.5** |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100528 | 99472 | 967.4 | 966.1 | +0.145 | +0.0144% | +1.87 | 10.93 (crop 13) | 1.28 | 1.98 | **t > 4.5** |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99698 | 100302 | 829.4 | 829.4 | +0.458 | +0.0536% | +0.53 | 2.59 (crop 18) | 1.04 | 2.29 | no leak detected |
## sha256: random-random (true null), seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 205.4 | 205.4 | -0.027 | -0.0128% | -1.52 | 2.32 (crop 13) | 1.55 | 1.10 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 191.7 | 191.4 | +0.019 | +0.0098% | +0.40 | 2.12 (crop 17) | 0.85 | 1.22 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199920 | 200080 | 168.6 | 168.6 | -0.004 | -0.0022% | +0.16 | 1.76 (crop 4) | 1.38 | 1.27 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199907 | 200093 | 354.2 | 354.2 | -0.096 | -0.0274% | -1.21 | 2.67 (crop 43) | 1.40 | 1.19 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200452 | 199548 | 317.1 | 317.1 | -0.067 | -0.0205% | -1.28 | 2.25 (crop 27) | 1.71 | 1.57 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 312.5 | 311.8 | +0.048 | +0.0150% | -0.36 | 2.87 (crop 24) | 0.71 | 1.22 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 481.8 | 481.8 | +0.194 | +0.0405% | +1.15 | 2.57 (crop 30) | 1.18 | 0.66 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199639 | 200361 | 769.5 | 769.5 | +0.146 | +0.0193% | +0.54 | 1.76 (crop 18) | 1.43 | 1.37 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 199522 | 200478 | 1362.0 | 1362.0 | +0.286 | +0.0208% | +0.68 | 1.74 (crop 11) | 1.06 | 1.00 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100042 | 99958 | 851.6 | 851.6 | -0.050 | -0.0058% | +1.02 | 2.03 (crop 24) | 0.97 | 0.82 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 99690 | 100310 | 1166.7 | 1165.4 | +0.492 | +0.0421% | +0.69 | 2.19 (crop 19) | 0.65 | 0.89 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100073 | 99927 | 1000.0 | 1000.0 | +0.060 | +0.0060% | +1.08 | 1.48 (crop 25) | 1.22 | 0.79 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 100008 | 99992 | 825.5 | 825.5 | +0.063 | +0.0074% | +0.95 | 1.78 (crop 11) | 1.34 | 1.48 | no leak detected |
## sha256: fixed-fixed (two different fixed pseudo-random secrets), seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 214.5 | 214.5 | +0.014 | +0.0066% | -0.44 | 1.32 (crop 6) | 0.75 | 1.30 | no leak detected |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 200.5 | 200.5 | -0.010 | -0.0051% | -0.35 | 1.60 (crop 25) | 0.98 | 0.80 | no leak detected |
| sha256/len=55 | all message bytes | 128 | 199920 | 200080 | 176.4 | 176.4 | -0.007 | -0.0043% | +0.43 | 1.90 (crop 34) | 1.12 | 0.92 | no leak detected |
| sha256/len=56 | all message bytes | 64 | 199907 | 200093 | 354.2 | 354.2 | -0.005 | -0.0014% | -1.89 | 2.02 (crop 78) | 2.62 | 1.85 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200452 | 199548 | 317.1 | 317.1 | +0.001 | +0.0002% | +0.97 | 2.38 (crop 2) | 1.48 | 1.85 | no leak detected |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 320.3 | 320.3 | -0.016 | -0.0051% | +0.21 | 2.65 (crop 2) | 1.09 | 1.27 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 481.1 | 481.1 | +0.052 | +0.0109% | +0.71 | 2.49 (crop 8) | 2.49 | 1.57 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199639 | 200361 | 729.2 | 729.2 | -0.196 | -0.0266% | -1.15 | 2.64 (crop 33) | 1.17 | 1.24 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 199522 | 200478 | 1270.8 | 1270.8 | +0.171 | +0.0132% | +0.31 | 1.57 (crop 14) | 1.01 | 1.26 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100042 | 99958 | 786.5 | 786.5 | -0.035 | -0.0044% | +0.40 | 1.39 (crop 40) | 1.75 | 1.04 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 99690 | 100310 | 1097.7 | 1097.7 | +0.089 | +0.0079% | -1.23 | 1.93 (crop 7) | 1.38 | 1.27 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100073 | 99927 | 951.8 | 951.8 | +0.226 | +0.0235% | +0.07 | 2.17 (crop 29) | 1.18 | 1.43 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 100008 | 99992 | 819.0 | 819.0 | +0.084 | +0.0102% | -0.19 | 1.63 (crop 7) | 1.12 | 1.65 | no leak detected |
## sha256: fixed-random, fixed = pseudo-random, seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 205.1 | 205.1 | -0.105 | -0.0506% | -3.69 | 23.33 (crop 5) | 0.84 | 1.33 | **t > 4.5** |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 191.7 | 191.7 | -0.064 | -0.0330% | +0.06 | 6.57 (crop 3) | 1.52 | 0.72 | **t > 4.5** |
| sha256/len=55 | all message bytes | 32 | 199920 | 200080 | 164.1 | 164.1 | -0.069 | -0.0418% | +0.07 | 10.18 (crop 33) | 2.57 | 0.91 | **t > 4.5** |
| sha256/len=56 | all message bytes | 64 | 199907 | 200093 | 352.2 | 352.2 | -0.096 | -0.0279% | +0.04 | 3.50 (crop 1) | 0.68 | 1.04 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200452 | 199548 | 317.1 | 317.1 | -0.117 | -0.0366% | -0.66 | 5.83 (crop 13) | 1.22 | 1.03 | **t > 4.5** |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 303.4 | 302.7 | -0.018 | -0.0058% | +0.73 | 2.74 (crop 0) | 1.45 | 1.65 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 451.2 | 451.2 | -0.023 | -0.0051% | -0.08 | 3.22 (crop 22) | 0.80 | 1.35 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199639 | 200361 | 730.5 | 730.5 | +0.027 | +0.0037% | +2.25 | 2.48 (crop 23) | 1.12 | 1.55 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 199522 | 200478 | 1273.4 | 1273.4 | +0.052 | +0.0040% | +1.20 | 1.55 (crop 23) | 1.03 | 1.26 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100042 | 99958 | 800.8 | 800.8 | +0.130 | +0.0163% | +0.82 | 6.70 (crop 5) | 0.82 | 1.34 | **t > 4.5** |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 99690 | 100310 | 1115.9 | 1115.9 | +0.053 | +0.0047% | +0.10 | 2.00 (crop 2) | 0.86 | 1.48 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100073 | 99927 | 1014.3 | 1013.0 | +0.316 | +0.0309% | +2.04 | 4.69 (crop 21) | 0.85 | 0.90 | **t > 4.5** |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 100008 | 99992 | 824.2 | 824.2 | +0.080 | +0.0094% | +0.59 | 3.13 (crop 13) | 1.23 | 1.12 | no leak detected |
## sha256: fixed-random, fixed = all-zero, seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199563 | 200437 | 216.1 | 216.1 | -0.155 | -0.0728% | -2.77 | 20.27 (crop 4) | 1.43 | 1.25 | **t > 4.5** |
| sha256/len=16 | all message bytes | 128 | 200053 | 199947 | 192.7 | 192.7 | -0.065 | -0.0334% | -1.09 | 10.81 (crop 10) | 1.22 | 1.95 | **t > 4.5** |
| sha256/len=55 | all message bytes | 128 | 199920 | 200080 | 175.8 | 176.1 | -0.197 | -0.1122% | -5.58 | 18.07 (crop 5) | 0.76 | 0.78 | **t > 4.5** |
| sha256/len=56 | all message bytes | 64 | 199907 | 200093 | 335.9 | 336.6 | -0.172 | -0.0505% | -1.80 | 27.88 (crop 4) | 1.31 | 1.84 | **t > 4.5** |
| sha256/len=64 | all message bytes | 64 | 200452 | 199548 | 310.5 | 311.2 | +0.006 | +0.0018% | -3.10 | 22.25 (crop 9) | 1.36 | 1.44 | **t > 4.5** |
| sha256/len=119 | all message bytes | 64 | 200279 | 199721 | 319.7 | 319.7 | -0.070 | -0.0221% | -0.30 | 16.42 (crop 5) | 0.84 | 1.85 | **t > 4.5** |
| sha256/len=120 | all message bytes | 64 | 200138 | 199862 | 481.1 | 481.8 | +0.628 | +0.1297% | -7.51 | 36.24 (crop 2) | 1.12 | 1.65 | **t > 4.5** |
| sha256/len=256 | all message bytes | 32 | 199639 | 200361 | 734.4 | 734.4 | +0.182 | +0.0243% | -2.56 | 31.68 (crop 4) | 1.05 | 1.62 | **t > 4.5** |
| sha256/len=560 | all message bytes | 8 | 199522 | 200478 | 1354.2 | 1359.4 | +0.749 | +0.0548% | -3.58 | 5.46 (crop 1) | 1.08 | 0.88 | **t > 4.5** |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100042 | 99958 | 798.2 | 798.2 | +0.043 | +0.0054% | +1.29 | 2.52 (crop 13) | 1.37 | 1.33 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 99690 | 100310 | 1123.7 | 1123.7 | +0.123 | +0.0108% | +0.67 | 9.67 (crop 1) | 0.78 | 0.91 | **t > 4.5** |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100073 | 99927 | 958.3 | 957.0 | +0.281 | +0.0291% | +2.92 | 7.58 (crop 5) | 1.06 | 1.59 | **t > 4.5** |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 100008 | 99992 | 878.9 | 878.9 | -0.126 | -0.0143% | -1.49 | 2.43 (crop 24) | 1.12 | 0.88 | no leak detected |
## thash: random-random (true null), seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200135 | 199865 | 352.9 | 352.9 | -0.073 | -0.0203% | -2.16 | 2.60 (crop 7) | 1.35 | 1.01 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200024 | 199976 | 368.5 | 368.5 | -0.024 | -0.0065% | +0.20 | 1.13 (crop 0) | 2.16 | 0.92 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199989 | 200011 | 1648.4 | 1648.4 | +0.016 | +0.0010% | +0.92 | 2.05 (crop 1) | 1.89 | 1.58 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 8 | 200346 | 199654 | 796.9 | 796.9 | +0.006 | +0.0008% | -0.08 | 2.01 (crop 22) | 1.42 | 1.06 | no leak detected |
## thash: fixed-fixed (two different fixed pseudo-random secrets), seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200135 | 199865 | 355.5 | 355.5 | -0.046 | -0.0126% | -1.14 | 2.10 (crop 26) | 1.12 | 1.55 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200024 | 199976 | 350.3 | 350.3 | -0.012 | -0.0034% | -0.06 | 2.23 (crop 5) | 1.36 | 1.18 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199989 | 200011 | 1648.4 | 1648.4 | +0.240 | +0.0145% | -0.40 | 1.55 (crop 0) | 1.24 | 1.02 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 8 | 200346 | 199654 | 807.3 | 807.3 | +0.241 | +0.0291% | +2.75 | 2.78 (crop 96) | 1.94 | 1.85 | no leak detected |
## thash: fixed-random, fixed = pseudo-random, seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200135 | 199865 | 374.3 | 374.3 | -0.035 | -0.0094% | -0.45 | 1.40 (crop 42) | 1.27 | 1.49 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200024 | 199976 | 369.1 | 369.1 | -0.010 | -0.0027% | +0.70 | 1.55 (crop 1) | 1.10 | 1.87 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199989 | 200011 | 1729.2 | 1729.2 | +0.404 | +0.0236% | +0.22 | 2.95 (crop 16) | 1.23 | 1.09 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 200346 | 199654 | 811.2 | 811.2 | -0.089 | -0.0108% | -0.44 | 2.14 (crop 15) | 1.20 | 1.81 | no leak detected |
## thash: fixed-random, fixed = all-zero, seed 1001
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 1001

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200135 | 199865 | 373.0 | 373.0 | -0.010 | -0.0026% | +0.20 | 2.44 (crop 0) | 1.33 | 1.01 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200024 | 199976 | 352.9 | 352.9 | -0.080 | -0.0221% | -1.07 | 4.09 (crop 12) | 1.79 | 1.32 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199989 | 200011 | 1653.6 | 1653.6 | +0.382 | +0.0227% | -0.43 | 1.67 (crop 2) | 1.36 | 1.71 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 200346 | 199654 | 798.2 | 798.2 | -0.037 | -0.0045% | -1.30 | 7.55 (crop 5) | 2.03 | 1.36 | **t > 4.5** |
## thash: random-random (true null), seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200335 | 199665 | 349.0 | 349.0 | -0.024 | -0.0066% | +0.74 | 2.80 (crop 10) | 2.08 | 2.04 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200046 | 199954 | 351.6 | 351.6 | -0.055 | -0.0155% | -1.47 | 2.44 (crop 18) | 1.19 | 1.71 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199997 | 200003 | 1648.4 | 1648.4 | +0.341 | +0.0204% | +2.91 | 3.15 (crop 63) | 0.73 | 1.34 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 199923 | 200077 | 813.8 | 813.8 | +0.060 | +0.0072% | -1.77 | 2.48 (crop 83) | 1.64 | 1.08 | no leak detected |
## thash: fixed-fixed (two different fixed pseudo-random secrets), seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200335 | 199665 | 351.6 | 351.6 | +0.050 | +0.0139% | +1.60 | 2.18 (crop 25) | 1.53 | 1.68 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200046 | 199954 | 350.9 | 350.9 | -0.115 | -0.0323% | +0.84 | 2.51 (crop 10) | 1.37 | 0.86 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199997 | 200003 | 1638.0 | 1638.0 | -0.180 | -0.0109% | -0.40 | 1.82 (crop 25) | 1.11 | 1.30 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 8 | 199923 | 200077 | 796.9 | 796.9 | +0.153 | +0.0186% | +1.67 | 1.74 (crop 86) | 1.36 | 1.55 | no leak detected |
## thash: fixed-random, fixed = pseudo-random, seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200335 | 199665 | 355.5 | 355.5 | +0.041 | +0.0114% | +0.00 | 1.35 (crop 26) | 1.27 | 1.25 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200046 | 199954 | 354.8 | 354.8 | +0.064 | +0.0178% | +0.59 | 1.54 (crop 70) | 1.16 | 1.04 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199997 | 200003 | 1734.4 | 1734.4 | +0.100 | +0.0058% | +0.30 | 2.07 (crop 12) | 1.06 | 0.78 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 199923 | 200077 | 856.8 | 856.8 | +0.114 | +0.0130% | +0.17 | 1.67 (crop 5) | 0.77 | 0.85 | no leak detected |
## thash: fixed-random, fixed = all-zero, seed 1002
clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 1002

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 200335 | 199665 | 373.0 | 373.0 | -0.019 | -0.0051% | +0.59 | 2.56 (crop 6) | 1.35 | 0.98 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200046 | 199954 | 377.0 | 377.0 | +0.038 | +0.0096% | +1.28 | 2.91 (crop 0) | 0.70 | 1.24 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 199997 | 200003 | 1755.2 | 1755.2 | -0.163 | -0.0091% | -1.51 | 2.56 (crop 7) | 1.08 | 0.81 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 199923 | 200077 | 869.8 | 871.1 | -0.047 | -0.0052% | -1.20 | 4.43 (crop 16) | 1.21 | 0.86 | no leak detected |
