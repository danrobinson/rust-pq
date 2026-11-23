21:08  up 2 days, 11:28, 4 users, load averages: 2.30 1.96 1.82
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 89.8 | 89.8 | -0.049 | -0.0541% | -1.27 | 8.27 (crop 18) | 1.09 | 1.14 | **t > 4.5** | 0.023 |
| sha256/len=16 | all message bytes | 512 | 100068 | 99932 | 74.3 | 74.3 | +0.001 | +0.0011% | +1.63 | 3.21 (crop 2) | 1.34 | 0.91 | no leak detected | 0.023 |
| sha256/len=55 | all message bytes | 512 | 100065 | 99935 | 48.4 | 48.4 | -0.008 | -0.0163% | -0.86 | 2.74 (crop 29) | 1.18 | 1.39 | no leak detected | 0.016 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 103.5 | 103.5 | -0.016 | -0.0158% | -0.19 | 1.75 (crop 7) | 1.69 | 0.85 | no leak detected | 0.029 |
| sha256/len=64 | all message bytes | 256 | 100273 | 99727 | 111.7 | 111.7 | -0.010 | -0.0092% | -0.88 | 1.69 (crop 8) | 1.36 | 1.60 | no leak detected | 0.036 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 62.7 | 62.7 | -0.003 | -0.0043% | +0.36 | 2.40 (crop 19) | 1.53 | 1.49 | no leak detected | 0.025 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 117.0 | 117.0 | -0.034 | -0.0282% | -0.51 | 1.62 (crop 29) | 1.35 | 1.50 | no leak detected | 0.036 |
| sha256/len=256 | all message bytes | 128 | 99847 | 100153 | 154.3 | 154.3 | +0.017 | +0.0108% | -0.71 | 1.81 (crop 15) | 1.09 | 1.19 | no leak detected | 0.046 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 188.2 | 188.2 | +0.009 | +0.0049% | +0.95 | 1.51 (crop 0) | 1.17 | 1.08 | no leak detected | 0.047 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 343.8 | 343.8 | +0.041 | +0.0122% | -0.02 | 1.39 (crop 0) | 1.55 | 1.08 | no leak detected | 0.186 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 418.6 | 418.6 | -0.017 | -0.0042% | +1.02 | 1.31 (crop 99) | 1.40 | 1.03 | no leak detected | 0.204 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 391.3 | 391.9 | +0.005 | +0.0012% | +0.05 | 1.56 (crop 7) | 2.52 | 0.92 | no leak detected | 0.193 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 390.0 | 390.0 | -0.071 | -0.0183% | -1.03 | 1.65 (crop 54) | 0.91 | 1.33 | no leak detected | 0.198 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 15.7 | 15.7 | -0.001 | -0.0043% | -1.10 | 2.48 (crop 34) | 2.44 | 2.07 | no leak detected | 0.003 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 25.7 | 25.7 | +0.001 | +0.0058% | +1.18 | 2.01 (crop 39) | 1.02 | 1.15 | no leak detected | 0.016 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 24.7 | 24.7 | +0.000 | +0.0007% | -1.42 | 1.42 | 2.47 | 2.18 | no leak detected | 0.018 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 87.4 | 87.6 | -0.032 | -0.0365% | -0.87 | 2.02 (crop 8) | 1.40 | 1.45 | no leak detected | 0.039 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 82.2 | 82.2 | -0.002 | -0.0020% | -0.89 | 2.79 (crop 10) | 1.68 | 1.85 | no leak detected | 0.033 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 256 | 100343 | 99657 | 134.6 | 134.6 | +0.058 | +0.0417% | +0.59 | 2.34 (crop 34) | 1.88 | 1.22 | no leak detected | 0.058 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 64 | 99943 | 100057 | 306.0 | 306.0 | -0.027 | -0.0089% | -0.48 | 2.09 (crop 14) | 1.54 | 1.17 | no leak detected | 0.081 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 192.4 | 192.4 | +0.015 | +0.0076% | +0.63 | 4.00 (crop 22) | 1.27 | 1.28 | no leak detected | 0.071 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 128 | 50086 | 49914 | 160.2 | 160.2 | +0.001 | +0.0006% | +1.17 | 1.19 (crop 1) | 1.94 | 1.35 | no leak detected | 0.084 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 256 | 50111 | 49889 | 177.1 | 176.9 | +0.073 | +0.0410% | +0.12 | 2.75 (crop 2) | 2.21 | 1.69 | no leak detected | 0.122 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 204.8 | 205.1 | -0.088 | -0.0437% | +0.34 | 1.43 (crop 47) | 1.27 | 2.01 | no leak detected | 0.144 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 527.3 | 527.3 | -0.055 | -0.0104% | +0.56 | 2.77 (crop 5) | 1.97 | 1.61 | no leak detected | 0.231 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 307.9 | 307.9 | +0.015 | +0.0047% | +0.71 | 1.80 (crop 35) | 3.68 | 1.17 | no leak detected | 0.116 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 799.5 | 799.5 | -0.125 | -0.0156% | -1.56 | 2.43 (crop 29) | 1.96 | 1.96 | no leak detected | 0.379 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6812.5 | 6802.1 | +4.804 | +0.0707% | +0.46 | 6.14 (crop 37) | 1.85 | 2.04 | **t > 4.5** | 5.206 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3083.3 | 3083.3 | +0.640 | +0.0208% | -0.15 | 2.84 (crop 29) | 1.39 | 1.37 | no leak detected | 2.444 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 221.0 | 221.0 | -0.035 | -0.0156% | +0.11 | 2.37 (crop 0) | 1.39 | 1.72 | no leak detected | 0.106 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1817.7 | 1817.7 | +0.823 | +0.0453% | +0.99 | 2.03 (crop 50) | 1.64 | 1.13 | no leak detected | 1.700 |
| wots_pk_gen | SK.seed | 2 | 24780 | 25220 | 7687.5 | 7687.5 | -0.099 | -0.0013% | +0.66 | 1.11 (crop 35) | 1.12 | 1.64 | no leak detected | 4.085 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4328.1 | 4328.1 | +0.399 | +0.0092% | -0.47 | 2.55 (crop 0) | 1.55 | 1.15 | no leak detected | 1.849 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7531.2 | 7531.2 | -0.027 | -0.0004% | -0.16 | 0.99 (crop 65) | 1.59 | 1.28 | no leak detected | 7.384 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15104.2 | 15104.2 | +1.422 | +0.0094% | -1.08 | 1.89 (crop 71) | 2.30 | 2.95 | no leak detected | 16.019 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30208.3 | 30208.3 | -16.623 | -0.0550% | -1.47 | 2.82 (crop 45) | 2.11 | 1.38 | no leak detected | 57.424 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 60458.3 | 60500.0 | -5.302 | -0.0088% | +0.27 | 1.39 (crop 51) | 1.96 | 2.26 | no leak detected | 94.936 |
| xmss_node/z=4 | SK.seed | 1 | 1499 | 1501 | 121000.0 | 121000.0 | -20.622 | -0.0170% | -1.08 | 1.46 (crop 29) | 1.63 | 1.55 | no leak detected | 172.705 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3898208.3 | 3897083.3 | +893.805 | +0.0229% | +0.16 | 1.75 (crop 3) | 2.61 | 2.13 | no leak detected | 2758.473 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 24.7 | 24.7 | +0.000 | +0.0001% | -0.93 | 2.19 (crop 56) | 1.53 | 1.79 | no leak detected | 0.013 |
| fors_node/z=0 | SK.seed | 128 | 49853 | 50147 | 155.9 | 155.9 | +0.047 | +0.0301% | +1.01 | 2.01 (crop 22) | 0.94 | 0.77 | no leak detected | 0.074 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 217.8 | 217.8 | +0.020 | +0.0092% | -0.53 | 1.84 (crop 12) | 1.42 | 0.87 | no leak detected | 0.087 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 538.4 | 537.8 | +0.019 | +0.0035% | +1.71 | 2.48 (crop 77) | 2.16 | 1.46 | no leak detected | 0.336 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3171.9 | 3166.7 | +1.134 | +0.0358% | +1.58 | 2.55 (crop 97) | 2.09 | 2.12 | no leak detected | 5.645 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6135.4 | 6145.8 | -2.015 | -0.0329% | +0.01 | 1.77 (crop 8) | 1.94 | 1.34 | no leak detected | 12.122 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12333.3 | 12333.3 | +7.432 | +0.0604% | +1.04 | 2.09 (crop 52) | 1.75 | 2.07 | no leak detected | 25.951 |
| fors_node/z=12 | SK.seed | 1 | 1010 | 990 | 197875.0 | 197750.0 | -134.288 | -0.0680% | +0.82 | 2.27 (crop 6) | 2.30 | 3.71 | no leak detected | 283.356 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2811041.7 | 2819041.7 | -2043.678 | -0.0727% | -1.75 | 1.98 (crop 66) | 2.36 | 2.04 | no leak detected | 4414.668 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3906291.7 | 3903833.3 | +3374.921 | +0.0865% | +1.28 | 2.79 (crop 25) | 3.14 | 1.79 | no leak detected | 2051.062 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.9 | 1.0 | -91.130 | -196.3696% | -70.44 | 75.67 (crop 58) | 2.81 | 1.63 | leak detected (expected: control) | 2.992 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 128 | 10079 | 9921 | 207.4 | 207.7 | +23.487 | +11.7875% | +0.97 | 108.03 (crop 2) | 1.55 | 1.86 | leak detected (expected: control) | 0.794 |
21:11  up 2 days, 11:31, 4 users, load averages: 1.97 2.09 1.91
