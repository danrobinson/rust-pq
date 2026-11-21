clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 64 | 199749 | 200251 | 242.8 | 242.8 | +0.006 | +0.0025% | +0.16 | 2.10 (crop 0) | 0.86 | 1.06 | no leak detected | 0.043 |
| sha256/len=16 | all message bytes | 128 | 199758 | 200242 | 228.5 | 228.5 | +0.019 | +0.0085% | -0.17 | 2.09 (crop 1) | 1.67 | 0.99 | no leak detected | 0.031 |
| sha256/len=55 | all message bytes | 128 | 200278 | 199722 | 196.0 | 196.0 | -0.013 | -0.0065% | -0.87 | 2.67 (crop 10) | 1.46 | 2.46 | no leak detected | 0.040 |
| sha256/len=56 | all message bytes | 64 | 199812 | 200188 | 404.3 | 404.3 | -0.027 | -0.0068% | +0.12 | 1.39 (crop 17) | 1.39 | 2.47 | no leak detected | 0.077 |
| sha256/len=64 | all message bytes | 64 | 200507 | 199493 | 380.9 | 380.9 | -0.001 | -0.0002% | -0.95 | 3.14 (crop 11) | 1.39 | 1.37 | no leak detected | 0.089 |
| sha256/len=119 | all message bytes | 64 | 200222 | 199778 | 371.7 | 371.7 | +0.037 | +0.0100% | -0.13 | 1.89 (crop 2) | 0.93 | 1.18 | no leak detected | 0.063 |
| sha256/len=120 | all message bytes | 64 | 200086 | 199914 | 554.7 | 554.7 | +0.034 | +0.0061% | -0.38 | 2.20 (crop 19) | 1.14 | 1.76 | no leak detected | 0.088 |
| sha256/len=256 | all message bytes | 32 | 199720 | 200280 | 910.2 | 908.9 | +0.102 | +0.0112% | +2.53 | 2.53 | 2.21 | 1.78 | no leak detected | 0.140 |
| sha256/len=560 | all message bytes | 16 | 199738 | 200262 | 1567.7 | 1567.7 | -0.178 | -0.0114% | -0.79 | 2.18 (crop 0) | 0.78 | 1.05 | no leak detected | 0.282 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100037 | 99963 | 967.4 | 967.4 | +0.060 | +0.0062% | +0.04 | 1.88 (crop 3) | 1.25 | 1.60 | no leak detected | 0.236 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 100246 | 99754 | 1398.4 | 1398.4 | +0.312 | +0.0225% | +1.93 | 2.47 (crop 18) | 1.77 | 1.00 | no leak detected | 0.203 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100037 | 99963 | 1156.2 | 1156.2 | -0.016 | -0.0014% | +0.55 | 0.95 (crop 56) | 1.55 | 1.40 | no leak detected | 0.226 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99718 | 100282 | 964.8 | 964.8 | +0.029 | +0.0030% | -0.51 | 2.10 (crop 40) | 1.43 | 1.53 | no leak detected | 0.221 |
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 199754 | 200246 | 416.0 | 416.0 | -0.008 | -0.0020% | -0.75 | 2.59 (crop 2) | 1.37 | 1.71 | no leak detected | 0.073 |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200044 | 199956 | 446.6 | 446.6 | +0.087 | +0.0198% | +1.38 | 1.95 (crop 87) | 0.50 | 0.97 | no leak detected | 0.063 |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 8 | 200036 | 199964 | 1979.2 | 1979.2 | -0.076 | -0.0038% | -0.58 | 2.24 (crop 0) | 1.37 | 1.41 | no leak detected | 0.364 |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 200273 | 199727 | 946.6 | 946.6 | -0.060 | -0.0063% | -0.38 | 1.86 (crop 41) | 1.02 | 1.75 | no leak detected | 0.167 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 100034 | 99966 | 985.7 | 985.7 | +0.044 | +0.0045% | +1.06 | 1.08 (crop 56) | 1.91 | 1.82 | no leak detected | 0.214 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 99542 | 100458 | 987.0 | 987.0 | +0.106 | +0.0108% | +0.41 | 2.17 (crop 7) | 1.49 | 1.00 | no leak detected | 0.219 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 100080 | 99920 | 1242.2 | 1242.2 | +0.224 | +0.0182% | +0.98 | 1.93 (crop 63) | 0.65 | 0.96 | no leak detected | 0.172 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 99874 | 100126 | 3890.6 | 3890.6 | +0.296 | +0.0078% | +0.05 | 1.77 (crop 15) | 1.39 | 1.31 | no leak detected | 0.908 |
| chain/i=0,s=15 | start value x | 4 | 100153 | 99847 | 6333.3 | 6322.9 | +0.739 | +0.0117% | +0.37 | 2.36 (crop 0) | 1.73 | 2.14 | no leak detected | 1.472 |
| chain/i=0,s=1 | start value x | 64 | 100553 | 99447 | 419.3 | 419.3 | +0.008 | +0.0020% | +0.08 | 1.10 (crop 84) | 1.30 | 1.34 | no leak detected | 0.103 |
| chain/i=3,s=7 | start value x | 8 | 100033 | 99967 | 2906.2 | 2906.2 | -0.073 | -0.0025% | -0.44 | 1.63 (crop 49) | 1.44 | 0.78 | no leak detected | 0.786 |
| chain/i=15,s=0 | start value x | 8192 | 100283 | 99717 | 4.0 | 4.0 | -0.000 | -0.0115% | -1.59 | 2.02 (crop 98) | 1.16 | 0.90 | no leak detected | 0.001 |
| chain/i=0,s=0 | start value x | 8192 | 99782 | 100218 | 3.7 | 3.7 | -0.000 | -0.0016% | -0.40 | 1.48 (crop 37) | 1.90 | 2.75 | no leak detected | 0.001 |
| wots_pk_gen | SK.seed | 1 | 49946 | 50054 | 238375.0 | 238375.0 | -55.845 | -0.0233% | +0.26 | 1.55 (crop 35) | 0.92 | 1.01 | no leak detected | 52.696 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 50111 | 49889 | 121750.0 | 121750.0 | -0.510 | -0.0004% | +1.64 | 1.95 (crop 53) | 1.53 | 1.49 | no leak detected | 28.036 |
| xmss_node/z=0 | SK.seed | 1 | 10002 | 9998 | 235333.3 | 235375.0 | -19.227 | -0.0082% | -1.26 | 1.45 (crop 39) | 1.11 | 1.23 | no leak detected | 86.825 |
| xmss_node/z=1 | SK.seed | 1 | 10034 | 9966 | 480583.3 | 480541.7 | +5.068 | +0.0011% | +0.15 | 1.29 (crop 16) | 1.58 | 1.93 | no leak detected | 206.913 |
| xmss_node/z=2 | SK.seed | 1 | 3039 | 2961 | 949583.3 | 950041.7 | -728.555 | -0.0770% | -1.55 | 1.84 (crop 72) | 0.91 | 0.70 | no leak detected | 544.595 |
| xmss_node/z=3 | SK.seed | 1 | 2949 | 3051 | 1941375.0 | 1940958.3 | +385.012 | +0.0198% | -0.18 | 1.34 (crop 13) | 0.86 | 0.79 | no leak detected | 1437.300 |
| xmss_node/z=4 | SK.seed | 1 | 2988 | 3012 | 3831375.0 | 3829041.7 | +18.942 | +0.0005% | +0.79 | 1.76 (crop 12) | 1.50 | 1.59 | no leak detected | 2493.143 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 492 | 508 | 123352375.0 | 123388583.3 | +10981.903 | +0.0089% | +0.35 | 1.75 (crop 15) | 1.98 | 1.68 | no leak detected | 219508.403 |
| fors_sk_gen | SK.seed | 64 | 200547 | 199453 | 418.0 | 418.0 | +0.004 | +0.0010% | -1.61 | 1.61 | 1.63 | 1.48 | no leak detected | 0.071 |
| fors_node/z=0 | SK.seed | 32 | 100088 | 99912 | 845.1 | 845.1 | +0.059 | +0.0070% | -1.01 | 1.75 (crop 53) | 1.59 | 1.16 | no leak detected | 0.193 |
| fors_node/z=1 | SK.seed | 16 | 99737 | 100263 | 2127.6 | 2127.6 | -0.058 | -0.0027% | -1.06 | 1.29 (crop 7) | 1.08 | 1.29 | no leak detected | 0.484 |
| fors_node/z=3 | SK.seed | 2 | 30094 | 29906 | 10104.2 | 10104.2 | +0.887 | +0.0088% | +1.25 | 1.59 (crop 11) | 2.19 | 1.34 | no leak detected | 4.358 |
| fors_node/z=6 | SK.seed | 1 | 5083 | 4917 | 83875.0 | 83833.3 | -2.921 | -0.0035% | +2.48 | 3.31 (crop 85) | 2.08 | 1.50 | no leak detected | 45.570 |
| fors_node/z=12 | SK.seed | 1 | 1985 | 2015 | 5353125.0 | 5353750.0 | -729.160 | -0.0136% | -0.80 | 1.66 (crop 2) | 1.30 | 2.08 | no leak detected | 3900.157 |
| fors_sign | SK.seed (md public, fixed) | 1 | 299 | 301 | 74628291.7 | 74565000.0 | +224350.205 | +0.2999% | +0.70 | 3.28 (crop 31) | 1.24 | 1.16 | no leak detected | 147330.525 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 1027 | 973 | 129771000.0 | 129800041.7 | -220856.496 | -0.1721% | -1.33 | 1.95 (crop 24) | 0.65 | 1.44 | no leak detected | 134349.601 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 32 | 100383 | 99617 | 623.7 | 307.3 | +452.297 | +111.8098% | +223.72 | 839.87 (crop 6) | 1.81 | 2.85 | leak detected (expected: control) | 1.419 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 99785 | 100215 | 636.7 | 847.7 | -109.103 | -15.5798% | -220.19 | 220.19 | 1.93 | 1.04 | leak detected (expected: control) | 0.969 |
