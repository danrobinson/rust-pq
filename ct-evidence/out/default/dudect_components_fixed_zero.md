20:11  up 2 days, 10:30, 4 users, load averages: 1.85 1.70 1.70
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 204.4 | 204.4 | -0.098 | -0.0480% | +0.00 | 13.87 (crop 28) | 1.91 | 1.26 | **t > 4.5** | 0.057 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 189.5 | 189.5 | -0.040 | -0.0213% | +0.11 | 8.91 (crop 16) | 1.68 | 1.48 | **t > 4.5** | 0.055 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 167.3 | 167.6 | -0.014 | -0.0084% | -0.44 | 19.62 (crop 14) | 0.86 | 1.85 | **t > 4.5** | 0.059 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 339.2 | 339.2 | -0.024 | -0.0069% | -1.45 | 21.10 (crop 19) | 1.92 | 1.11 | **t > 4.5** | 0.123 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 339.2 | 339.8 | +0.254 | +0.0738% | -2.04 | 38.11 (crop 13) | 2.80 | 1.25 | **t > 4.5** | 0.115 |
| sha256/len=119 | all message bytes | 128 | 99937 | 100063 | 300.8 | 301.1 | -0.028 | -0.0091% | -5.19 | 76.68 (crop 12) | 1.28 | 2.30 | **t > 4.5** | 0.105 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 473.3 | 474.0 | -0.071 | -0.0148% | -2.69 | 28.56 (crop 16) | 1.59 | 2.82 | **t > 4.5** | 0.165 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 751.3 | 751.3 | +0.017 | +0.0021% | -2.90 | 42.36 (crop 9) | 1.96 | 1.08 | **t > 4.5** | 0.311 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1260.4 | 1263.0 | +0.320 | +0.0245% | -1.96 | 58.56 (crop 8) | 2.36 | 1.40 | **t > 4.5** | 0.574 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 790.4 | 791.7 | -0.200 | -0.0252% | -0.96 | 7.71 (crop 21) | 1.40 | 2.37 | **t > 4.5** | 0.373 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 50028 | 49972 | 1105.5 | 1105.5 | -0.527 | -0.0470% | -0.81 | 2.17 (crop 48) | 1.22 | 1.46 | no leak detected | 0.519 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 958.3 | 958.3 | +0.085 | +0.0087% | -0.41 | 1.92 (crop 22) | 1.48 | 1.60 | no leak detected | 0.459 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 828.1 | 828.1 | +0.203 | +0.0243% | +0.30 | 7.93 (crop 23) | 2.02 | 1.84 | **t > 4.5** | 0.390 |
| compress (copy inlined into the wrapper) | state and block | 256 | 100274 | 99726 | 134.8 | 136.2 | -2.374 | -1.7349% | -116.20 | 312.21 (crop 20) | 1.12 | 1.32 | **t > 4.5** | 0.046 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 100170 | 99830 | 141.9 | 141.9 | +0.095 | +0.0659% | +0.06 | 2.67 (crop 32) | 1.93 | 1.75 | no leak detected | 0.063 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 100365 | 99635 | 142.3 | 142.3 | +0.172 | +0.1196% | -1.05 | 6.67 (crop 31) | 1.67 | 0.96 | **t > 4.5** | 0.050 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 200.5 | 200.5 | -0.026 | -0.0131% | -1.15 | 5.46 (crop 11) | 1.77 | 1.73 | **t > 4.5** | 0.061 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 197.9 | 197.9 | -0.011 | -0.0055% | -0.07 | 12.28 (crop 14) | 2.45 | 1.87 | **t > 4.5** | 0.063 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 64 | 100343 | 99657 | 608.1 | 608.1 | +0.033 | +0.0053% | -2.02 | 21.64 (crop 3) | 1.70 | 1.91 | **t > 4.5** | 0.205 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 16 | 99943 | 100057 | 1479.2 | 1479.2 | +1.155 | +0.0761% | -1.28 | 22.48 (crop 6) | 1.39 | 1.64 | **t > 4.5** | 0.595 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1372.4 | 1372.4 | +2.867 | +0.2052% | -0.43 | 31.33 (crop 5) | 1.37 | 1.61 | **t > 4.5** | 0.717 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 639.3 | 639.3 | -0.188 | -0.0291% | -1.04 | 1.47 (crop 26) | 1.75 | 1.91 | no leak detected | 0.309 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 643.2 | 643.2 | +0.078 | +0.0120% | -0.24 | 3.95 (crop 14) | 1.97 | 2.07 | no leak detected | 0.333 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 781.2 | 781.2 | +0.098 | +0.0123% | -1.73 | 1.83 (crop 21) | 1.07 | 1.48 | no leak detected | 0.400 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 2880.2 | 2880.2 | +0.317 | +0.0107% | -0.99 | 1.50 (crop 19) | 1.11 | 1.65 | no leak detected | 1.594 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 49819 | 50181 | 2026.0 | 2028.6 | -2.050 | -0.1010% | -3.11 | 63.61 (crop 13) | 1.82 | 1.18 | **t > 4.5** | 0.848 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 24932 | 25068 | 8072.9 | 8083.3 | -12.905 | -0.1596% | -2.30 | 55.38 (crop 18) | 2.64 | 1.25 | **t > 4.5** | 5.787 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 70500.0 | 70625.0 | -124.336 | -0.1757% | -1.51 | 41.75 (crop 20) | 2.03 | 1.28 | **t > 4.5** | 70.707 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 31125.0 | 31166.7 | -25.973 | -0.0834% | -1.04 | 23.38 (crop 14) | 2.10 | 1.14 | **t > 4.5** | 33.852 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 1885.4 | 1888.0 | +11.270 | +0.5772% | -2.34 | 43.02 (crop 13) | 2.41 | 2.58 | **t > 4.5** | 1.624 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 4987 | 5013 | 17208.3 | 17208.3 | +172.621 | +0.9607% | -4.31 | 19.53 (crop 8) | 2.06 | 1.92 | **t > 4.5** | 35.141 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 76625.0 | 76625.0 | -0.657 | -0.0009% | +0.75 | 1.26 (crop 27) | 1.75 | 0.96 | no leak detected | 44.898 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 39375.0 | 39375.0 | -3.319 | -0.0084% | +1.30 | 1.34 (crop 4) | 1.56 | 1.59 | no leak detected | 25.463 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 76625.0 | 76625.0 | -14.612 | -0.0190% | -0.90 | 2.01 (crop 55) | 2.56 | 1.26 | no leak detected | 93.714 |
| xmss_node/z=1 | SK.seed | 1 | 4982 | 5018 | 153375.0 | 153375.0 | +70.328 | +0.0456% | +0.46 | 2.02 (crop 31) | 2.03 | 1.32 | no leak detected | 186.136 |
| xmss_node/z=2 | SK.seed | 1 | 1547 | 1453 | 306916.7 | 306916.7 | -50.453 | -0.0163% | +1.46 | 1.82 (crop 22) | 2.59 | 2.22 | no leak detected | 630.118 |
| xmss_node/z=3 | SK.seed | 1 | 1518 | 1482 | 614250.0 | 614458.3 | +124.542 | +0.0201% | +0.22 | 3.28 (crop 7) | 1.91 | 1.87 | no leak detected | 1091.629 |
| xmss_node/z=4 | SK.seed | 1 | 1489 | 1511 | 1240291.7 | 1239166.7 | +519.563 | +0.0420% | +0.09 | 2.32 (crop 7) | 1.73 | 2.80 | no leak detected | 2494.159 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 39682000.0 | 39727958.3 | -76661.722 | -0.1916% | -1.64 | 2.25 (crop 57) | 1.78 | 1.89 | no leak detected | 84458.533 |
| fors_sk_gen | SK.seed | 128 | 99973 | 100027 | 146.2 | 146.2 | +0.017 | +0.0116% | +1.85 | 3.50 (crop 13) | 0.86 | 1.96 | no leak detected | 0.060 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 371.1 | 371.1 | +0.150 | +0.0399% | +0.64 | 3.20 (crop 2) | 0.91 | 1.20 | no leak detected | 0.212 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 789.1 | 789.1 | -0.241 | -0.0299% | -0.32 | 1.71 (crop 37) | 1.38 | 1.22 | no leak detected | 0.451 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3255.2 | 3255.2 | +2.946 | +0.0871% | +0.73 | 1.65 (crop 15) | 1.49 | 1.94 | no leak detected | 4.231 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 26166.7 | 26208.3 | -62.504 | -0.2232% | -1.72 | 2.01 (crop 94) | 2.40 | 3.14 | no leak detected | 85.224 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 52208.3 | 52250.0 | -66.179 | -0.1188% | -1.16 | 1.41 (crop 76) | 3.03 | 0.86 | no leak detected | 154.818 |
| fors_node/z=8 | SK.seed | 1 | 2464 | 2536 | 104500.0 | 104500.0 | +220.312 | +0.2002% | +0.49 | 1.84 (crop 19) | 1.12 | 2.45 | no leak detected | 286.041 |
| fors_node/z=12 | SK.seed | 1 | 1014 | 986 | 1694666.7 | 1694750.0 | -933.820 | -0.0536% | +0.05 | 1.77 (crop 0) | 1.99 | 1.41 | no leak detected | 5923.025 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 25166166.7 | 25232833.3 | +96231.511 | +0.3852% | -1.09 | 1.09 | 1.94 | 1.91 | no leak detected | 125147.950 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 39721375.0 | 39715125.0 | -8632.432 | -0.0216% | -0.44 | 1.68 (crop 10) | 2.38 | 1.41 | no leak detected | 57869.557 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 3405.2 | 1.0 | +3194.992 | +176.8970% | +1082.61 | 1083.07 (crop 58) | 2.53 | 1.51 | leak detected (expected: control) | 2.956 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 1.3 | 677.1 | -599.713 | -198.9356% | -274.72 | 289.09 (crop 36) | 1.37 | 1.24 | leak detected (expected: control) | 2.486 |
20:25  up 2 days, 10:44, 4 users, load averages: 1.58 1.65 1.62
