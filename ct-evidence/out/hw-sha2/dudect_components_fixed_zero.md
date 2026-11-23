21:11  up 2 days, 11:31, 4 users, load averages: 1.97 2.09 1.91
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 88.1 | 88.1 | -0.044 | -0.0497% | +0.05 | 6.57 (crop 22) | 1.01 | 1.41 | **t > 4.5** | 0.029 |
| sha256/len=16 | all message bytes | 512 | 100068 | 99932 | 72.8 | 72.8 | +0.009 | +0.0117% | +0.25 | 2.77 (crop 34) | 1.73 | 1.65 | no leak detected | 0.022 |
| sha256/len=55 | all message bytes | 512 | 100065 | 99935 | 46.4 | 46.4 | -0.029 | -0.0618% | -2.11 | 9.58 (crop 15) | 1.72 | 1.70 | **t > 4.5** | 0.020 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 100.9 | 100.9 | +0.038 | +0.0373% | -0.11 | 2.84 (crop 31) | 1.09 | 1.62 | no leak detected | 0.034 |
| sha256/len=64 | all message bytes | 256 | 100273 | 99727 | 98.3 | 98.3 | +0.033 | +0.0328% | +0.23 | 2.66 (crop 27) | 1.03 | 1.36 | no leak detected | 0.034 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 61.3 | 61.4 | +0.010 | +0.0153% | -3.13 | 15.57 (crop 21) | 0.94 | 1.22 | **t > 4.5** | 0.027 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 114.7 | 114.7 | +0.008 | +0.0070% | +0.70 | 2.23 (crop 9) | 1.34 | 1.19 | no leak detected | 0.040 |
| sha256/len=256 | all message bytes | 256 | 99847 | 100153 | 153.6 | 153.6 | -0.034 | -0.0217% | +0.52 | 1.81 (crop 1) | 1.37 | 1.13 | no leak detected | 0.044 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 184.6 | 184.6 | +0.000 | +0.0001% | +1.38 | 6.23 (crop 2) | 1.53 | 2.41 | **t > 4.5** | 0.057 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 309.9 | 309.9 | -0.033 | -0.0105% | +1.17 | 1.95 (crop 70) | 1.44 | 1.08 | no leak detected | 0.190 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 378.9 | 378.9 | -0.003 | -0.0008% | +0.13 | 3.59 (crop 7) | 1.66 | 1.27 | no leak detected | 0.237 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 362.0 | 362.0 | +0.042 | +0.0112% | +1.61 | 2.24 (crop 47) | 1.63 | 1.04 | no leak detected | 0.213 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 350.9 | 350.9 | -0.009 | -0.0023% | -0.16 | 1.70 (crop 2) | 1.18 | 1.06 | no leak detected | 0.237 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 15.4 | 15.4 | -0.001 | -0.0055% | +0.95 | 2.87 (crop 17) | 1.66 | 1.37 | no leak detected | 0.004 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 24.7 | 24.7 | +0.012 | +0.0479% | +1.36 | 8.09 (crop 26) | 2.89 | 1.64 | **t > 4.5** | 0.013 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 24.1 | 24.1 | -0.002 | -0.0101% | +0.19 | 1.76 (crop 11) | 1.49 | 1.79 | no leak detected | 0.015 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 81.2 | 81.2 | +0.005 | +0.0056% | +1.13 | 3.32 (crop 0) | 0.86 | 1.46 | no leak detected | 0.027 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 78.3 | 78.1 | +0.013 | +0.0168% | +2.52 | 6.61 (crop 3) | 1.26 | 1.59 | **t > 4.5** | 0.027 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 256 | 100343 | 99657 | 132.0 | 132.0 | -0.031 | -0.0227% | -0.38 | 9.25 (crop 13) | 1.47 | 2.42 | **t > 4.5** | 0.060 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 128 | 99943 | 100057 | 299.8 | 299.8 | -0.031 | -0.0104% | -0.30 | 2.10 (crop 2) | 2.18 | 1.91 | no leak detected | 0.087 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 188.2 | 188.2 | +0.024 | +0.0129% | +0.73 | 7.39 (crop 20) | 1.54 | 0.99 | **t > 4.5** | 0.084 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 128 | 50086 | 49914 | 156.6 | 156.6 | -0.062 | -0.0387% | +1.03 | 2.75 (crop 9) | 1.36 | 2.00 | no leak detected | 0.091 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 158.5 | 158.2 | +0.077 | +0.0467% | +0.65 | 1.48 (crop 7) | 2.25 | 1.56 | no leak detected | 0.138 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 203.5 | 203.8 | -0.008 | -0.0040% | -0.24 | 1.63 (crop 7) | 1.25 | 0.84 | no leak detected | 0.145 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 526.0 | 526.0 | +0.089 | +0.0167% | -0.48 | 2.14 (crop 10) | 1.49 | 1.19 | no leak detected | 0.234 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 307.9 | 307.9 | +0.006 | +0.0018% | +0.22 | 2.59 (crop 13) | 1.52 | 2.21 | no leak detected | 0.125 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 799.5 | 799.5 | -0.095 | -0.0119% | +1.43 | 1.91 (crop 41) | 2.10 | 1.67 | no leak detected | 0.444 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6822.9 | 6822.9 | +2.854 | +0.0418% | -0.78 | 3.40 (crop 24) | 1.64 | 0.93 | no leak detected | 6.261 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3083.3 | 3083.3 | +1.015 | +0.0329% | +1.71 | 5.36 (crop 48) | 1.60 | 1.60 | **t > 4.5** | 2.611 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 219.1 | 219.1 | +0.013 | +0.0058% | +0.62 | 1.77 (crop 6) | 1.57 | 2.17 | no leak detected | 0.110 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1773.4 | 1773.4 | +1.455 | +0.0821% | +1.23 | 3.60 (crop 40) | 1.53 | 1.22 | no leak detected | 2.040 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7552.1 | 7552.1 | +0.583 | +0.0077% | +0.98 | 1.24 (crop 10) | 1.38 | 1.62 | no leak detected | 3.731 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4244.8 | 4244.8 | +0.005 | +0.0001% | +0.05 | 2.18 (crop 6) | 1.44 | 1.97 | no leak detected | 2.273 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7572.9 | 7572.9 | +0.722 | +0.0095% | -0.55 | 2.04 (crop 0) | 1.26 | 2.23 | no leak detected | 9.311 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15145.8 | 15145.8 | -1.843 | -0.0122% | +1.31 | 1.35 (crop 2) | 1.12 | 2.16 | no leak detected | 16.357 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30250.0 | 30250.0 | +13.008 | +0.0430% | -1.30 | 2.20 (crop 12) | 1.31 | 1.98 | no leak detected | 63.177 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 60541.7 | 60500.0 | +10.859 | +0.0180% | +1.03 | 2.52 (crop 41) | 2.32 | 1.50 | no leak detected | 97.854 |
| xmss_node/z=4 | SK.seed | 1 | 1494 | 1506 | 121000.0 | 121000.0 | +21.676 | +0.0179% | +1.63 | 1.76 (crop 22) | 2.01 | 2.60 | no leak detected | 145.043 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3899916.7 | 3898541.7 | +933.108 | +0.0239% | +0.16 | 1.45 (crop 12) | 1.59 | 1.92 | no leak detected | 2330.840 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 24.6 | 24.6 | +0.022 | +0.0880% | +2.02 | 18.76 (crop 33) | 1.71 | 1.67 | **t > 4.5** | 0.012 |
| fors_node/z=0 | SK.seed | 256 | 49853 | 50147 | 148.8 | 148.8 | -0.038 | -0.0257% | -0.35 | 2.69 (crop 16) | 1.03 | 1.08 | no leak detected | 0.070 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 217.4 | 217.4 | +0.031 | +0.0140% | -0.43 | 1.67 (crop 24) | 1.71 | 1.25 | no leak detected | 0.090 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 538.4 | 538.4 | +0.069 | +0.0128% | +0.77 | 1.52 (crop 30) | 1.64 | 1.79 | no leak detected | 0.334 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3166.7 | 3166.7 | +0.485 | +0.0153% | -0.02 | 1.59 (crop 55) | 1.38 | 1.76 | no leak detected | 5.456 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6125.0 | 6125.0 | -1.433 | -0.0235% | +1.56 | 1.56 | 1.35 | 1.96 | no leak detected | 10.244 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12333.3 | 12333.3 | -6.426 | -0.0522% | +0.36 | 1.81 (crop 2) | 1.32 | 1.92 | no leak detected | 20.608 |
| fors_node/z=12 | SK.seed | 1 | 1007 | 993 | 197875.0 | 197750.0 | +49.820 | +0.0252% | -0.20 | 1.58 (crop 37) | 2.91 | 1.96 | no leak detected | 264.607 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2803291.7 | 2798500.0 | +929.436 | +0.0332% | +1.81 | 2.08 (crop 62) | 2.50 | 1.81 | no leak detected | 2725.274 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3903166.7 | 3902208.3 | -344.081 | -0.0088% | +0.28 | 1.73 (crop 2) | 1.85 | 1.03 | no leak detected | 1628.159 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 3405.0 | 1.0 | +3194.909 | +176.9173% | +1084.25 | 1084.28 (crop 89) | 2.54 | 2.26 | leak detected (expected: control) | 2.949 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 128 | 10079 | 9921 | 1.6 | 208.0 | -181.881 | -196.5548% | -275.99 | 289.77 (crop 36) | 1.54 | 0.99 | leak detected (expected: control) | 0.752 |
21:24  up 2 days, 11:43, 4 users, load averages: 1.39 1.60 1.72
