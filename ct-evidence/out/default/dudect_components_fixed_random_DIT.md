20:25  up 2 days, 10:44, 4 users, load averages: 1.58 1.65 1.62
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 234.0 | 234.0 | -0.004 | -0.0016% | +0.48 | 2.19 (crop 19) | 1.95 | 2.11 | no leak detected | 0.061 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 219.1 | 219.1 | +0.006 | +0.0027% | -0.80 | 1.88 (crop 37) | 2.30 | 1.48 | no leak detected | 0.054 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 194.7 | 194.7 | -0.001 | -0.0006% | +1.21 | 2.09 (crop 99) | 1.72 | 1.72 | no leak detected | 0.053 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 395.8 | 395.8 | +0.015 | +0.0037% | -0.24 | 1.47 (crop 34) | 1.80 | 1.92 | no leak detected | 0.100 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 391.3 | 391.3 | -0.013 | -0.0032% | +1.59 | 2.15 (crop 40) | 1.95 | 1.59 | no leak detected | 0.104 |
| sha256/len=119 | all message bytes | 64 | 99937 | 100063 | 353.5 | 353.5 | -0.005 | -0.0015% | -1.32 | 2.19 (crop 96) | 1.79 | 1.59 | no leak detected | 0.097 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 556.6 | 556.6 | -0.000 | -0.0000% | -0.27 | 1.31 (crop 54) | 1.44 | 2.21 | no leak detected | 0.132 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 875.0 | 875.0 | +0.036 | +0.0041% | -0.83 | 2.44 (crop 26) | 2.62 | 2.44 | no leak detected | 0.218 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1481.8 | 1481.8 | +0.009 | +0.0006% | +0.59 | 2.07 (crop 1) | 1.56 | 2.78 | no leak detected | 0.404 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 927.1 | 927.1 | +0.029 | +0.0032% | -0.87 | 2.60 (crop 41) | 3.00 | 2.35 | no leak detected | 0.340 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 50028 | 49972 | 1291.7 | 1291.7 | -0.065 | -0.0051% | +0.43 | 2.43 (crop 28) | 2.35 | 1.08 | no leak detected | 0.488 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 1122.4 | 1122.4 | +0.013 | +0.0012% | +1.26 | 2.70 (crop 0) | 1.10 | 1.66 | no leak detected | 0.364 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 963.5 | 963.5 | +0.031 | +0.0032% | -0.47 | 2.32 (crop 47) | 1.63 | 1.70 | no leak detected | 0.360 |
| compress (copy inlined into the wrapper) | state and block | 128 | 100274 | 99726 | 160.8 | 160.8 | -0.002 | -0.0012% | -1.33 | 1.96 (crop 99) | 1.72 | 1.94 | no leak detected | 0.046 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 100170 | 99830 | 164.7 | 165.0 | -0.005 | -0.0028% | -0.93 | 1.83 (crop 77) | 1.51 | 1.50 | no leak detected | 0.046 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 128 | 100365 | 99635 | 165.4 | 165.4 | -0.004 | -0.0026% | -0.16 | 1.94 (crop 38) | 2.58 | 1.48 | no leak detected | 0.050 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 229.8 | 229.8 | -0.000 | -0.0001% | -0.90 | 1.99 (crop 79) | 1.39 | 2.69 | no leak detected | 0.055 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 224.6 | 224.6 | +0.001 | +0.0003% | +0.21 | 1.49 (crop 48) | 2.87 | 1.93 | no leak detected | 0.058 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 32 | 100343 | 99657 | 710.9 | 710.9 | +0.007 | +0.0010% | +0.88 | 1.61 (crop 42) | 1.46 | 1.08 | no leak detected | 0.182 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 16 | 99943 | 100057 | 1734.4 | 1734.4 | -0.037 | -0.0021% | -0.03 | 3.51 (crop 23) | 1.81 | 2.15 | no leak detected | 0.477 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1619.8 | 1619.8 | +0.041 | +0.0025% | +0.29 | 2.06 (crop 44) | 1.23 | 2.00 | no leak detected | 0.560 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 750.0 | 750.0 | -0.004 | -0.0006% | +0.27 | 2.34 (crop 71) | 1.74 | 1.53 | no leak detected | 0.262 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 751.3 | 751.3 | -0.006 | -0.0008% | +0.18 | 1.94 (crop 16) | 1.94 | 1.82 | no leak detected | 0.293 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 912.8 | 912.8 | -0.013 | -0.0014% | -1.02 | 1.54 (crop 45) | 2.48 | 1.80 | no leak detected | 0.332 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 3385.4 | 3385.4 | +0.204 | +0.0060% | +0.58 | 1.70 (crop 33) | 1.66 | 2.24 | no leak detected | 1.199 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 49819 | 50181 | 2541.7 | 2541.7 | -0.014 | -0.0006% | -0.41 | 2.18 (crop 5) | 2.67 | 2.18 | no leak detected | 0.945 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 24932 | 25068 | 10083.3 | 10083.3 | -1.293 | -0.0128% | +1.07 | 2.20 (crop 16) | 1.56 | 2.49 | no leak detected | 5.195 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 87916.7 | 87875.0 | +26.425 | +0.0301% | +0.82 | 3.12 (crop 44) | 1.76 | 2.21 | no leak detected | 49.097 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 38791.7 | 38750.0 | +7.707 | +0.0199% | +0.97 | 2.84 (crop 59) | 1.70 | 1.00 | no leak detected | 27.714 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 2250.0 | 2250.0 | -0.064 | -0.0028% | -1.70 | 2.43 (crop 73) | 2.36 | 2.93 | no leak detected | 1.130 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 4987 | 5013 | 20416.7 | 20416.7 | +13.461 | +0.0659% | +3.14 | 7.86 (crop 36) | 1.97 | 1.05 | **t > 4.5** | 26.209 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 95041.7 | 95041.7 | +2.442 | +0.0026% | -0.84 | 2.59 (crop 4) | 2.76 | 1.51 | no leak detected | 30.044 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 48666.7 | 48666.7 | +0.987 | +0.0020% | +1.33 | 2.56 (crop 0) | 2.71 | 1.66 | no leak detected | 19.646 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 95041.7 | 95041.7 | +12.816 | +0.0135% | -0.48 | 1.23 (crop 51) | 3.03 | 2.22 | no leak detected | 71.553 |
| xmss_node/z=1 | SK.seed | 1 | 4983 | 5017 | 190375.0 | 190416.7 | -6.712 | -0.0035% | +0.30 | 1.33 (crop 6) | 1.53 | 2.15 | no leak detected | 114.437 |
| xmss_node/z=2 | SK.seed | 1 | 1553 | 1447 | 381791.7 | 382041.7 | -352.063 | -0.0919% | -1.59 | 2.46 (crop 29) | 2.17 | 1.84 | no leak detected | 339.730 |
| xmss_node/z=3 | SK.seed | 1 | 1514 | 1486 | 764208.3 | 764458.3 | -237.799 | -0.0311% | -1.54 | 1.94 (crop 75) | 1.38 | 1.10 | no leak detected | 485.100 |
| xmss_node/z=4 | SK.seed | 1 | 1492 | 1508 | 1535291.7 | 1533875.0 | +790.114 | +0.0515% | +2.21 | 2.61 (crop 16) | 1.15 | 1.79 | no leak detected | 695.952 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 49170583.3 | 49167458.3 | -10137.147 | -0.0206% | -1.35 | 2.48 (crop 9) | 1.54 | 2.31 | no leak detected | 9277.019 |
| fors_sk_gen | SK.seed | 128 | 99973 | 100027 | 168.6 | 168.6 | +0.008 | +0.0047% | +0.81 | 2.30 (crop 29) | 2.24 | 3.00 | no leak detected | 0.044 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 432.9 | 432.9 | +0.060 | +0.0138% | -0.17 | 2.72 (crop 37) | 2.11 | 1.46 | no leak detected | 0.165 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 928.4 | 928.4 | -0.026 | -0.0028% | +0.70 | 1.68 (crop 8) | 2.53 | 2.22 | no leak detected | 0.322 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3932.3 | 3932.3 | -0.280 | -0.0071% | +0.68 | 1.97 (crop 34) | 2.13 | 2.08 | no leak detected | 2.269 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 31375.0 | 31375.0 | -16.380 | -0.0523% | +1.67 | 2.37 (crop 33) | 1.91 | 1.30 | no leak detected | 50.895 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 62750.0 | 62750.0 | -26.081 | -0.0417% | -0.40 | 3.62 (crop 7) | 2.89 | 1.79 | no leak detected | 69.089 |
| fors_node/z=8 | SK.seed | 1 | 2466 | 2534 | 125625.0 | 125625.0 | -35.576 | -0.0284% | -0.01 | 1.94 (crop 27) | 1.62 | 2.05 | no leak detected | 112.391 |
| fors_node/z=12 | SK.seed | 1 | 1013 | 987 | 2024208.3 | 2024375.0 | -39.286 | -0.0019% | -0.47 | 1.82 (crop 56) | 0.79 | 2.26 | no leak detected | 902.160 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 28357916.7 | 28369333.3 | +1103.133 | +0.0039% | -0.03 | 1.36 (crop 6) | 1.91 | 2.04 | no leak detected | 7610.594 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 49173208.3 | 49183208.3 | -4071.383 | -0.0083% | -0.88 | 1.93 (crop 0) | 2.45 | 2.45 | no leak detected | 7244.899 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.9 | 1.0 | -130.762 | -197.5643% | -70.36 | 75.16 (crop 58) | 3.14 | 1.08 | leak detected (expected: control) | 4.332 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 796.9 | 796.9 | +89.677 | +11.8682% | +1.24 | 120.56 (crop 2) | 1.76 | 1.06 | leak detected (expected: control) | 2.931 |
20:30  up 2 days, 10:49, 4 users, load averages: 1.66 1.61 1.59
