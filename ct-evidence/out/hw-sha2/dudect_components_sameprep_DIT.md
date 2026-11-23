21:50  up 2 days, 12:09, 4 users, load averages: 2.41 2.52 2.32
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 110.8 | 110.8 | -0.001 | -0.0012% | -0.43 | 2.21 (crop 3) | 1.03 | 1.16 | no leak detected | 0.027 |
| sha256/len=16 | all message bytes | 256 | 100068 | 99932 | 90.2 | 90.2 | -0.001 | -0.0006% | +2.31 | 2.54 (crop 95) | 1.71 | 1.82 | no leak detected | 0.020 |
| sha256/len=55 | all message bytes | 256 | 100065 | 99935 | 64.1 | 64.1 | +0.001 | +0.0022% | -1.16 | 1.95 (crop 55) | 1.07 | 1.50 | no leak detected | 0.015 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 120.1 | 120.1 | -0.002 | -0.0020% | +0.04 | 1.78 (crop 62) | 1.77 | 2.25 | no leak detected | 0.024 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 114.6 | 114.6 | -0.006 | -0.0049% | -0.52 | 2.39 (crop 0) | 2.14 | 1.29 | no leak detected | 0.035 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 76.8 | 76.8 | -0.006 | -0.0083% | -1.56 | 2.23 (crop 14) | 1.24 | 1.28 | no leak detected | 0.016 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 140.8 | 141.0 | -0.003 | -0.0022% | -0.76 | 2.53 (crop 1) | 2.07 | 2.13 | no leak detected | 0.027 |
| sha256/len=256 | all message bytes | 128 | 99847 | 100153 | 174.5 | 174.5 | +0.002 | +0.0009% | -0.02 | 1.34 (crop 77) | 1.73 | 1.69 | no leak detected | 0.039 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 216.1 | 216.1 | +0.001 | +0.0006% | +0.11 | 1.50 (crop 56) | 1.47 | 2.34 | no leak detected | 0.089 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 422.5 | 422.5 | -0.015 | -0.0036% | -0.35 | 1.80 (crop 38) | 2.09 | 2.00 | no leak detected | 0.124 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 480.5 | 480.5 | -0.023 | -0.0049% | -0.44 | 1.59 (crop 5) | 1.48 | 1.36 | no leak detected | 0.138 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 472.0 | 472.0 | +0.036 | +0.0077% | -1.00 | 2.79 (crop 33) | 1.24 | 1.83 | no leak detected | 0.126 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 455.1 | 454.4 | +0.003 | +0.0006% | -2.07 | 2.13 (crop 9) | 1.21 | 1.90 | no leak detected | 0.118 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 17.5 | 17.5 | +0.000 | +0.0019% | +0.64 | 1.68 (crop 17) | 2.03 | 1.69 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 38.2 | 38.2 | -0.002 | -0.0065% | -2.12 | 2.75 (crop 97) | 1.44 | 1.58 | no leak detected | 0.008 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 37.3 | 37.3 | -0.002 | -0.0051% | -0.32 | 1.13 (crop 47) | 1.51 | 1.96 | no leak detected | 0.009 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 98.8 | 98.8 | +0.003 | +0.0028% | +0.82 | 2.90 (crop 58) | 2.16 | 1.21 | no leak detected | 0.022 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 97.5 | 97.5 | -0.000 | -0.0004% | -0.85 | 1.93 (crop 57) | 2.15 | 1.11 | no leak detected | 0.022 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 128 | 100343 | 99657 | 171.5 | 171.5 | +0.009 | +0.0054% | -0.42 | 3.09 (crop 39) | 2.41 | 2.05 | no leak detected | 0.037 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 64 | 99943 | 100057 | 344.4 | 344.4 | -0.017 | -0.0049% | +0.07 | 2.48 (crop 21) | 1.45 | 1.65 | no leak detected | 0.079 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 209.0 | 209.0 | +0.003 | +0.0012% | +0.36 | 2.44 (crop 0) | 1.93 | 1.52 | no leak detected | 0.061 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 128 | 50086 | 49914 | 187.8 | 187.8 | +0.009 | +0.0046% | +0.49 | 2.67 (crop 72) | 1.20 | 1.81 | no leak detected | 0.060 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 198.9 | 198.9 | -0.004 | -0.0020% | -0.14 | 2.21 (crop 55) | 2.24 | 2.00 | no leak detected | 0.060 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 222.7 | 223.0 | -0.018 | -0.0082% | -1.58 | 3.07 (crop 42) | 1.97 | 1.68 | no leak detected | 0.063 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 600.9 | 600.9 | -0.008 | -0.0013% | -0.03 | 2.19 (crop 41) | 2.72 | 1.43 | no leak detected | 0.160 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 315.1 | 315.1 | -0.002 | -0.0006% | +0.21 | 2.14 (crop 69) | 1.87 | 1.85 | no leak detected | 0.106 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 816.4 | 816.4 | -0.022 | -0.0027% | -0.52 | 1.90 (crop 14) | 1.22 | 1.87 | no leak detected | 0.343 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6958.3 | 6958.3 | -0.193 | -0.0028% | +1.28 | 1.33 (crop 2) | 1.62 | 2.49 | no leak detected | 4.474 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3166.7 | 3166.7 | -0.691 | -0.0219% | -0.36 | 2.04 (crop 29) | 1.07 | 1.47 | no leak detected | 2.246 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 225.9 | 225.9 | -0.016 | -0.0070% | -1.35 | 2.09 (crop 38) | 1.75 | 2.17 | no leak detected | 0.088 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1828.1 | 1828.1 | -0.204 | -0.0112% | +0.59 | 3.03 (crop 0) | 1.17 | 1.46 | no leak detected | 1.435 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7729.2 | 7729.2 | +0.258 | +0.0033% | +1.59 | 2.11 (crop 69) | 2.22 | 1.19 | no leak detected | 3.153 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4333.3 | 4333.3 | -0.142 | -0.0033% | +0.31 | 2.80 (crop 1) | 1.62 | 1.27 | no leak detected | 1.885 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7729.2 | 7729.2 | +0.461 | +0.0060% | +0.74 | 2.90 (crop 1) | 1.81 | 2.08 | no leak detected | 7.369 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15500.0 | 15500.0 | -0.668 | -0.0043% | -0.92 | 2.94 (crop 0) | 1.66 | 1.40 | no leak detected | 17.361 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 31083.3 | 31041.7 | +6.256 | +0.0202% | +1.36 | 1.73 (crop 62) | 1.32 | 1.37 | no leak detected | 56.372 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 62125.0 | 62125.0 | -8.011 | -0.0129% | +0.71 | 2.22 (crop 7) | 1.53 | 1.19 | no leak detected | 74.088 |
| xmss_node/z=4 | SK.seed | 1 | 1495 | 1505 | 124333.3 | 124375.0 | -45.743 | -0.0368% | -0.93 | 2.23 (crop 25) | 1.33 | 1.41 | no leak detected | 145.657 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 4005083.3 | 4002208.3 | +94.598 | +0.0024% | +0.96 | 1.80 (crop 8) | 1.98 | 2.65 | no leak detected | 2241.262 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 37.4 | 37.4 | -0.000 | -0.0009% | -0.99 | 1.59 (crop 96) | 2.30 | 2.03 | no leak detected | 0.007 |
| fors_node/z=0 | SK.seed | 128 | 49853 | 50147 | 157.2 | 157.2 | +0.093 | +0.0585% | +1.07 | 2.23 (crop 33) | 1.26 | 1.04 | no leak detected | 0.135 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 229.5 | 229.2 | +0.054 | +0.0236% | +0.40 | 2.32 (crop 26) | 1.06 | 1.51 | no leak detected | 0.094 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 555.3 | 555.3 | -0.107 | -0.0193% | +0.72 | 1.74 (crop 30) | 1.19 | 1.87 | no leak detected | 0.318 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3260.4 | 3260.4 | +0.825 | +0.0253% | +0.90 | 1.93 (crop 44) | 1.37 | 2.42 | no leak detected | 4.571 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6302.1 | 6291.7 | +2.361 | +0.0375% | +0.47 | 2.00 (crop 28) | 0.65 | 1.29 | no leak detected | 7.641 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12583.3 | 12583.3 | +0.583 | +0.0046% | -1.23 | 2.33 (crop 72) | 1.09 | 1.56 | no leak detected | 18.066 |
| fors_node/z=12 | SK.seed | 1 | 1008 | 992 | 202333.3 | 202250.0 | +45.984 | +0.0227% | +1.11 | 2.05 (crop 45) | 0.90 | 1.74 | no leak detected | 216.500 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2866125.0 | 2865375.0 | -138.630 | -0.0048% | +0.29 | 1.86 (crop 0) | 1.24 | 1.44 | no leak detected | 2598.774 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 4005541.7 | 4008916.7 | -770.128 | -0.0192% | -1.56 | 2.23 (crop 61) | 2.20 | 1.85 | no leak detected | 1645.165 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.7 | 1.0 | -133.343 | -197.6668% | -70.36 | 75.16 (crop 58) | 2.65 | 1.94 | leak detected (expected: control) | 4.414 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 64 | 10079 | 9921 | 276.7 | 276.7 | +32.846 | +12.5402% | +0.89 | 121.30 (crop 2) | 1.12 | 1.21 | leak detected (expected: control) | 1.013 |
21:53  up 2 days, 12:12, 4 users, load averages: 2.59 2.61 2.40
