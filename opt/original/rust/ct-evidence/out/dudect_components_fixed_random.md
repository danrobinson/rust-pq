clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199749 | 200251 | 201.5 | 201.5 | -0.107 | -0.0526% | -2.88 | 20.14 (crop 14) | 1.93 | 1.45 | **t > 4.5** |
| sha256/len=16 | all message bytes | 128 | 199758 | 200242 | 190.1 | 190.1 | -0.048 | -0.0251% | -0.74 | 6.28 (crop 4) | 1.04 | 1.36 | **t > 4.5** |
| sha256/len=55 | all message bytes | 128 | 200278 | 199722 | 166.3 | 166.3 | -0.066 | -0.0400% | -3.16 | 9.25 (crop 26) | 1.12 | 1.55 | **t > 4.5** |
| sha256/len=56 | all message bytes | 64 | 199812 | 200188 | 334.6 | 334.6 | +0.032 | +0.0094% | +1.07 | 2.57 (crop 7) | 0.95 | 1.71 | no leak detected |
| sha256/len=64 | all message bytes | 64 | 200507 | 199493 | 308.6 | 308.6 | +0.003 | +0.0009% | -0.34 | 7.12 (crop 10) | 1.86 | 2.20 | **t > 4.5** |
| sha256/len=119 | all message bytes | 64 | 200222 | 199778 | 304.0 | 304.0 | -0.037 | -0.0119% | -1.84 | 2.73 (crop 58) | 0.91 | 0.67 | no leak detected |
| sha256/len=120 | all message bytes | 64 | 200086 | 199914 | 454.4 | 454.4 | -0.040 | -0.0087% | +0.87 | 4.22 (crop 9) | 1.22 | 1.61 | no leak detected |
| sha256/len=256 | all message bytes | 32 | 199720 | 200280 | 785.2 | 785.2 | -0.321 | -0.0397% | -1.57 | 1.97 (crop 23) | 1.67 | 2.08 | no leak detected |
| sha256/len=560 | all message bytes | 16 | 199738 | 200262 | 1263.0 | 1263.0 | -0.129 | -0.0099% | -0.07 | 1.84 (crop 8) | 1.07 | 1.34 | no leak detected |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100037 | 99963 | 804.7 | 804.7 | +0.054 | +0.0066% | +1.25 | 5.75 (crop 11) | 1.29 | 1.47 | **t > 4.5** |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 8 | 100246 | 99754 | 1119.8 | 1119.8 | -0.103 | -0.0091% | -0.21 | 2.24 (crop 0) | 1.56 | 0.90 | no leak detected |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100037 | 99963 | 950.5 | 950.5 | +0.146 | +0.0152% | +1.73 | 3.83 (crop 26) | 1.60 | 1.41 | no leak detected |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99718 | 100282 | 826.8 | 826.8 | +0.488 | +0.0584% | +0.60 | 3.30 (crop 22) | 0.94 | 2.61 | no leak detected |
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 199754 | 200246 | 378.9 | 378.9 | +0.020 | +0.0051% | +1.09 | 1.90 (crop 5) | 0.90 | 1.64 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200044 | 199956 | 371.7 | 371.7 | -0.061 | -0.0168% | -1.61 | 2.65 (crop 0) | 1.83 | 1.23 | no leak detected |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 200036 | 199964 | 1640.6 | 1640.6 | +0.164 | +0.0099% | +0.70 | 1.68 (crop 67) | 2.34 | 1.93 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 200273 | 199727 | 799.5 | 800.8 | -0.071 | -0.0088% | -0.04 | 2.23 (crop 6) | 1.60 | 2.15 | no leak detected |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 100034 | 99966 | 890.6 | 890.6 | -0.203 | -0.0228% | -0.93 | 1.23 (crop 12) | 1.11 | 1.41 | no leak detected |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 99542 | 100458 | 833.3 | 833.3 | +0.163 | +0.0189% | +0.98 | 1.68 (crop 3) | 1.33 | 1.57 | no leak detected |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 100080 | 99920 | 979.2 | 979.2 | +0.037 | +0.0037% | +0.41 | 1.45 (crop 1) | 1.57 | 2.16 | no leak detected |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 99874 | 100126 | 3072.9 | 3072.9 | -0.272 | -0.0087% | -0.79 | 1.41 (crop 2) | 1.24 | 1.84 | no leak detected |
| chain/i=0,s=15 | start value x | 4 | 100153 | 99847 | 5364.6 | 5364.6 | +0.996 | +0.0182% | +0.27 | 1.27 (crop 0) | 0.96 | 2.28 | no leak detected |
| chain/i=0,s=1 | start value x | 64 | 100553 | 99447 | 382.2 | 382.2 | -0.050 | -0.0128% | +0.06 | 2.68 (crop 3) | 1.76 | 0.85 | no leak detected |
| chain/i=3,s=7 | start value x | 8 | 100033 | 99967 | 2437.5 | 2437.5 | -0.048 | -0.0020% | +2.05 | 2.52 (crop 99) | 1.45 | 2.20 | no leak detected |
| chain/i=15,s=0 | start value x | 8192 | 100283 | 99717 | 3.2 | 3.2 | -0.000 | -0.0104% | +0.81 | 2.15 (crop 36) | 1.44 | 1.65 | no leak detected |
| chain/i=0,s=0 | start value x | 8192 | 99782 | 100218 | 3.2 | 3.2 | +0.000 | +0.0093% | -0.76 | 1.73 (crop 37) | 1.60 | 1.50 | no leak detected |
| wots_pk_gen | SK.seed | 1 | 49955 | 50045 | 197958.3 | 197875.0 | +51.151 | +0.0257% | -1.86 | 2.63 (crop 16) | 1.49 | 1.48 | no leak detected |
| wots_sign | SK.seed (message m public, fixed) | 1 | 50105 | 49895 | 101000.0 | 101041.7 | -21.772 | -0.0214% | -1.42 | 2.21 (crop 44) | 1.88 | 2.19 | no leak detected |
| xmss_node/z=0 | SK.seed | 1 | 10006 | 9994 | 199000.0 | 199041.7 | -149.269 | -0.0745% | -0.79 | 2.15 (crop 5) | 1.12 | 1.13 | no leak detected |
| xmss_node/z=1 | SK.seed | 1 | 10033 | 9967 | 395250.0 | 394833.3 | +222.135 | +0.0561% | +1.36 | 3.04 (crop 29) | 1.42 | 1.52 | no leak detected |
| xmss_node/z=2 | SK.seed | 1 | 3040 | 2960 | 787791.7 | 787875.0 | -19.981 | -0.0025% | -0.28 | 1.90 (crop 23) | 1.13 | 1.95 | no leak detected |
| xmss_node/z=3 | SK.seed | 1 | 2947 | 3053 | 1579333.3 | 1579000.0 | +636.814 | +0.0403% | +0.28 | 1.65 (crop 32) | 1.17 | 1.41 | no leak detected |
| xmss_node/z=4 | SK.seed | 1 | 2988 | 3012 | 3169291.7 | 3170041.7 | -1089.811 | -0.0344% | +0.52 | 1.86 (crop 1) | 2.73 | 2.74 | no leak detected |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 492 | 508 | 102509875.0 | 102555500.0 | -4916.587 | -0.0048% | +0.38 | 1.51 (crop 1) | 3.03 | 2.16 | no leak detected |
| fors_sk_gen | SK.seed | 64 | 200547 | 199453 | 376.3 | 376.3 | +0.015 | +0.0039% | -0.64 | 1.28 (crop 7) | 1.43 | 1.44 | no leak detected |
| fors_node/z=0 | SK.seed | 32 | 100088 | 99912 | 707.0 | 707.0 | +0.221 | +0.0306% | +1.07 | 1.81 (crop 3) | 2.03 | 1.16 | no leak detected |
| fors_node/z=1 | SK.seed | 16 | 99737 | 100263 | 1815.1 | 1815.1 | -0.112 | -0.0061% | -0.29 | 1.75 (crop 25) | 1.28 | 1.04 | no leak detected |
| fors_node/z=3 | SK.seed | 4 | 30094 | 29906 | 8395.8 | 8395.8 | -5.221 | -0.0616% | -2.11 | 2.34 (crop 29) | 2.08 | 1.67 | no leak detected |
| fors_node/z=6 | SK.seed | 1 | 5083 | 4917 | 69000.0 | 68958.3 | -4.499 | -0.0065% | -0.86 | 1.72 (crop 5) | 1.82 | 1.40 | no leak detected |
| fors_node/z=12 | SK.seed | 1 | 1985 | 2015 | 4473541.7 | 4474791.7 | -627.675 | -0.0140% | -0.93 | 2.36 (crop 16) | 1.65 | 2.93 | no leak detected |
| fors_sign | SK.seed (md public, fixed) | 1 | 299 | 301 | 62627416.7 | 63075916.7 | -120790.290 | -0.1920% | -1.90 | 2.39 (crop 53) | 1.92 | 1.67 | no leak detected |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 1027 | 973 | 102588500.0 | 102573458.3 | -25677.032 | -0.0251% | -0.16 | 1.34 (crop 1) | 2.20 | 1.74 | no leak detected |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 32 | 100383 | 99617 | 412.8 | 209.6 | +295.008 | +111.0316% | +216.33 | 875.00 (crop 6) | 0.89 | 1.19 | leak detected (expected: control) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 99785 | 100215 | 502.6 | 668.0 | -85.356 | -15.3730% | -215.06 | 215.34 (crop 99) | 1.99 | 1.06 | leak detected (expected: control) |
