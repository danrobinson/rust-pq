21:53  up 2 days, 12:12, 4 users, load averages: 2.59 2.61 2.40
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = all-zero secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 89.4 | 89.4 | +0.001 | +0.0016% | -2.38 | 2.83 (crop 85) | 1.14 | 1.02 | no leak detected | 0.027 |
| sha256/len=16 | all message bytes | 512 | 100068 | 99932 | 73.9 | 73.9 | +0.002 | +0.0028% | +0.17 | 3.54 (crop 38) | 1.25 | 1.72 | no leak detected | 0.022 |
| sha256/len=55 | all message bytes | 512 | 100065 | 99935 | 48.0 | 48.0 | -0.022 | -0.0449% | -2.64 | 12.28 (crop 11) | 1.38 | 1.38 | **t > 4.5** | 0.015 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 103.0 | 102.9 | +0.007 | +0.0066% | +0.27 | 4.20 (crop 17) | 0.95 | 1.13 | no leak detected | 0.030 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 100.3 | 100.3 | -0.031 | -0.0304% | -1.27 | 1.57 (crop 4) | 1.12 | 0.85 | no leak detected | 0.045 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 62.7 | 62.7 | +0.027 | +0.0419% | +0.21 | 22.17 (crop 16) | 1.18 | 1.29 | **t > 4.5** | 0.025 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 116.2 | 116.2 | -0.011 | -0.0095% | +0.41 | 3.23 (crop 15) | 1.23 | 1.28 | no leak detected | 0.035 |
| sha256/len=256 | all message bytes | 256 | 99847 | 100153 | 152.8 | 152.8 | +0.028 | +0.0184% | +0.69 | 1.58 (crop 32) | 1.31 | 0.79 | no leak detected | 0.035 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 188.2 | 188.2 | +0.019 | +0.0099% | +0.43 | 8.02 (crop 14) | 1.55 | 1.66 | **t > 4.5** | 0.050 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 318.4 | 318.4 | -0.084 | -0.0260% | -1.27 | 3.18 (crop 17) | 1.10 | 1.16 | no leak detected | 0.184 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 380.2 | 380.2 | -0.128 | -0.0329% | -0.28 | 1.99 (crop 25) | 1.27 | 1.63 | no leak detected | 0.204 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 367.8 | 367.8 | +0.106 | +0.0281% | -0.37 | 2.55 (crop 17) | 1.56 | 1.65 | no leak detected | 0.201 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 356.1 | 356.1 | -0.137 | -0.0376% | -2.05 | 2.10 (crop 95) | 1.15 | 1.93 | no leak detected | 0.206 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 15.7 | 15.7 | +0.001 | +0.0095% | -0.04 | 1.72 (crop 53) | 2.18 | 1.34 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 25.2 | 25.2 | +0.017 | +0.0681% | +1.95 | 7.99 (crop 22) | 1.08 | 1.62 | **t > 4.5** | 0.015 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 24.6 | 24.7 | -0.002 | -0.0069% | -1.70 | 1.88 (crop 86) | 1.41 | 1.87 | no leak detected | 0.014 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 83.0 | 83.0 | +0.014 | +0.0164% | +2.40 | 5.74 (crop 17) | 1.58 | 1.42 | **t > 4.5** | 0.024 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 79.6 | 79.6 | +0.020 | +0.0250% | +0.25 | 4.48 (crop 33) | 1.19 | 1.28 | no leak detected | 0.024 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 128 | 100343 | 99657 | 136.1 | 136.1 | +0.137 | +0.0956% | +1.62 | 3.22 (crop 0) | 2.15 | 1.83 | no leak detected | 0.077 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 64 | 99943 | 100057 | 304.0 | 304.0 | -0.009 | -0.0028% | +0.21 | 1.93 (crop 20) | 1.53 | 2.40 | no leak detected | 0.089 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 192.1 | 192.1 | +0.012 | +0.0061% | +0.28 | 1.38 (crop 30) | 2.02 | 1.54 | no leak detected | 0.068 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 128 | 50086 | 49914 | 158.2 | 158.2 | -0.009 | -0.0054% | +2.34 | 3.58 (crop 10) | 1.44 | 1.58 | no leak detected | 0.094 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 161.5 | 161.5 | -0.111 | -0.0656% | +0.46 | 1.90 (crop 19) | 2.38 | 2.04 | no leak detected | 0.135 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 221.7 | 221.7 | +0.013 | +0.0065% | -0.12 | 1.39 (crop 9) | 1.01 | 0.80 | no leak detected | 0.137 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 535.8 | 535.8 | -0.040 | -0.0074% | -0.94 | 2.44 (crop 9) | 1.88 | 1.48 | no leak detected | 0.202 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 314.5 | 314.5 | +0.003 | +0.0009% | -1.01 | 2.45 (crop 56) | 1.42 | 1.59 | no leak detected | 0.113 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 816.4 | 816.4 | +0.021 | +0.0026% | +0.07 | 1.59 (crop 85) | 1.09 | 1.09 | no leak detected | 0.335 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6968.8 | 6968.8 | -1.186 | -0.0170% | -1.44 | 2.14 (crop 1) | 2.20 | 1.51 | no leak detected | 4.964 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3151.0 | 3151.0 | +0.325 | +0.0103% | -0.42 | 1.51 (crop 4) | 1.45 | 1.51 | no leak detected | 2.376 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 223.6 | 223.6 | -0.019 | -0.0085% | -1.60 | 2.41 (crop 10) | 1.71 | 1.36 | no leak detected | 0.109 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1828.1 | 1828.1 | +0.242 | +0.0133% | -1.43 | 1.44 (crop 97) | 1.75 | 2.13 | no leak detected | 1.861 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7687.5 | 7687.5 | -0.174 | -0.0023% | +1.37 | 1.58 (crop 45) | 1.74 | 1.08 | no leak detected | 3.506 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4312.5 | 4312.5 | -0.430 | -0.0100% | +0.32 | 1.94 (crop 44) | 1.77 | 1.32 | no leak detected | 1.962 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7687.5 | 7687.5 | -0.895 | -0.0117% | +0.15 | 1.86 (crop 4) | 1.39 | 2.43 | no leak detected | 6.995 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15416.7 | 15416.7 | +1.635 | +0.0106% | -0.55 | 1.85 (crop 0) | 1.91 | 1.26 | no leak detected | 12.242 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30875.0 | 30833.3 | +14.510 | +0.0471% | +0.05 | 2.43 (crop 51) | 1.37 | 2.81 | no leak detected | 44.510 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 61708.3 | 61708.3 | +14.973 | +0.0243% | -1.36 | 1.71 (crop 58) | 1.99 | 2.66 | no leak detected | 69.046 |
| xmss_node/z=4 | SK.seed | 1 | 1495 | 1505 | 123541.7 | 123458.3 | +48.841 | +0.0396% | +1.68 | 2.65 (crop 56) | 1.62 | 1.19 | no leak detected | 131.574 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3973708.3 | 3974875.0 | +504.180 | +0.0127% | +0.16 | 0.98 (crop 8) | 1.35 | 1.41 | no leak detected | 2560.406 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 25.1 | 25.1 | +0.021 | +0.0842% | +1.22 | 21.73 (crop 29) | 1.97 | 2.20 | **t > 4.5** | 0.014 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 160.2 | 160.2 | +0.021 | +0.0129% | -0.26 | 1.37 (crop 2) | 0.68 | 0.96 | no leak detected | 0.103 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 225.6 | 225.6 | +0.023 | +0.0101% | +1.32 | 2.36 (crop 75) | 1.42 | 0.99 | no leak detected | 0.120 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 554.7 | 554.7 | +0.032 | +0.0058% | -0.67 | 2.08 (crop 16) | 1.52 | 1.05 | no leak detected | 0.283 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3244.8 | 3244.8 | +0.223 | +0.0069% | -0.92 | 1.26 (crop 13) | 1.56 | 1.39 | no leak detected | 4.015 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6260.4 | 6260.4 | -4.233 | -0.0678% | +0.70 | 2.09 (crop 2) | 2.07 | 1.51 | no leak detected | 9.361 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12562.5 | 12562.5 | -0.808 | -0.0064% | -1.08 | 1.82 (crop 1) | 1.55 | 0.72 | no leak detected | 18.086 |
| fors_node/z=12 | SK.seed | 1 | 1006 | 994 | 202333.3 | 202375.0 | +105.605 | +0.0523% | -0.42 | 2.22 (crop 3) | 2.32 | 1.97 | no leak detected | 252.267 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2875291.7 | 2872125.0 | +2742.402 | +0.0955% | +1.09 | 2.31 (crop 0) | 1.79 | 1.49 | no leak detected | 2754.768 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3985166.7 | 3982666.7 | +816.194 | +0.0205% | +1.56 | 1.58 (crop 76) | 1.80 | 2.67 | no leak detected | 1639.013 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 32 | 9933 | 10067 | 3440.1 | 630.2 | +2791.435 | +137.5073% | +2475.47 | 3426.97 (crop 42) | 0.87 | 0.59 | leak detected (expected: control) | 1.140 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 64 | 10079 | 9921 | 1.3 | 320.3 | -317.488 | -197.9541% | -2235.10 | 14202.82 (crop 14) | 1.49 | 1.11 | leak detected (expected: control) | 0.144 |
21:55  up 2 days, 12:14, 4 users, load averages: 2.71 2.60 2.42
