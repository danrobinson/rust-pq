21:28  up 2 days, 11:47, 4 users, load averages: 1.36 1.50 1.65
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 88.5 | 88.5 | -0.002 | -0.0025% | -0.28 | 1.44 (crop 42) | 1.23 | 1.06 | no leak detected | 0.028 |
| sha256/len=16 | all message bytes | 512 | 100068 | 99932 | 73.0 | 73.0 | +0.002 | +0.0022% | +1.01 | 1.98 (crop 37) | 1.40 | 1.89 | no leak detected | 0.021 |
| sha256/len=55 | all message bytes | 512 | 100065 | 99935 | 47.1 | 47.1 | +0.001 | +0.0027% | -0.10 | 1.34 (crop 41) | 1.69 | 1.42 | no leak detected | 0.019 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 100.7 | 100.7 | +0.003 | +0.0027% | +0.44 | 1.02 (crop 26) | 1.22 | 1.59 | no leak detected | 0.031 |
| sha256/len=64 | all message bytes | 256 | 100273 | 99727 | 109.4 | 109.4 | +0.048 | +0.0457% | -0.60 | 1.79 (crop 47) | 1.30 | 0.99 | no leak detected | 0.040 |
| sha256/len=119 | all message bytes | 256 | 99937 | 100063 | 61.4 | 61.4 | -0.008 | -0.0133% | -0.95 | 1.61 (crop 13) | 1.71 | 1.98 | no leak detected | 0.027 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 114.1 | 114.1 | +0.043 | +0.0373% | -0.13 | 2.96 (crop 26) | 1.63 | 1.45 | no leak detected | 0.039 |
| sha256/len=256 | all message bytes | 256 | 99847 | 100153 | 151.4 | 151.4 | -0.022 | -0.0144% | -2.43 | 2.72 (crop 94) | 1.46 | 2.03 | no leak detected | 0.045 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 184.2 | 184.2 | -0.020 | -0.0105% | -0.95 | 3.14 (crop 6) | 1.46 | 1.13 | no leak detected | 0.059 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 343.1 | 343.1 | +0.065 | +0.0195% | +1.03 | 1.38 (crop 74) | 1.20 | 0.75 | no leak detected | 0.196 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 406.2 | 406.2 | -0.153 | -0.0382% | -0.44 | 1.46 (crop 11) | 1.36 | 1.47 | no leak detected | 0.215 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 391.3 | 391.3 | -0.013 | -0.0034% | -0.08 | 1.27 (crop 3) | 0.95 | 1.31 | no leak detected | 0.199 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 376.3 | 376.3 | -0.045 | -0.0120% | -1.54 | 1.84 (crop 91) | 1.02 | 1.31 | no leak detected | 0.211 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 15.4 | 15.4 | +0.000 | +0.0020% | +0.78 | 1.47 (crop 63) | 1.69 | 1.38 | no leak detected | 0.004 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 24.6 | 24.6 | -0.003 | -0.0110% | +0.78 | 2.83 (crop 26) | 1.71 | 1.84 | no leak detected | 0.014 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 24.1 | 24.1 | -0.006 | -0.0245% | +0.32 | 1.67 (crop 28) | 1.30 | 1.83 | no leak detected | 0.015 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 91.1 | 91.1 | -0.006 | -0.0064% | -0.60 | 1.67 (crop 9) | 1.53 | 3.34 | no leak detected | 0.042 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 80.6 | 80.6 | -0.070 | -0.0839% | -0.65 | 2.64 (crop 24) | 0.79 | 1.91 | no leak detected | 0.042 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 256 | 100343 | 99657 | 132.8 | 132.8 | -0.046 | -0.0328% | -0.52 | 1.72 (crop 14) | 2.11 | 0.84 | no leak detected | 0.078 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 128 | 99943 | 100057 | 300.1 | 300.1 | -0.028 | -0.0094% | +1.54 | 1.99 (crop 4) | 2.51 | 2.20 | no leak detected | 0.093 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 188.2 | 188.2 | -0.008 | -0.0042% | +1.51 | 1.77 (crop 75) | 1.89 | 2.02 | no leak detected | 0.089 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 256 | 50086 | 49914 | 157.2 | 157.2 | +0.005 | +0.0028% | -1.29 | 1.92 (crop 10) | 1.94 | 1.86 | no leak detected | 0.086 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 164.4 | 164.7 | -0.011 | -0.0062% | -1.53 | 3.04 (crop 8) | 1.81 | 1.93 | no leak detected | 0.144 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 217.1 | 217.4 | +0.036 | +0.0177% | -0.00 | 2.35 (crop 4) | 2.46 | 1.62 | no leak detected | 0.140 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 529.3 | 529.3 | +0.139 | +0.0259% | +0.62 | 2.27 (crop 3) | 1.43 | 1.47 | no leak detected | 0.250 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 307.9 | 307.9 | -0.017 | -0.0056% | -1.29 | 3.47 (crop 49) | 2.74 | 1.85 | no leak detected | 0.140 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 799.5 | 799.5 | -0.078 | -0.0098% | +1.22 | 1.89 (crop 34) | 2.13 | 1.82 | no leak detected | 0.465 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6802.1 | 6802.1 | -1.729 | -0.0254% | +0.97 | 3.28 (crop 45) | 1.95 | 1.68 | no leak detected | 6.151 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3083.3 | 3078.1 | -0.040 | -0.0013% | -1.40 | 2.19 (crop 82) | 2.16 | 1.61 | no leak detected | 2.860 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 218.8 | 218.8 | +0.032 | +0.0148% | +0.60 | 2.03 (crop 14) | 1.53 | 1.81 | no leak detected | 0.121 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1773.4 | 1773.4 | -0.984 | -0.0555% | -0.72 | 2.51 (crop 30) | 1.35 | 1.79 | no leak detected | 2.303 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7531.2 | 7531.2 | -0.350 | -0.0047% | +0.19 | 1.69 (crop 48) | 1.78 | 1.52 | no leak detected | 4.224 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4229.2 | 4229.2 | +0.053 | +0.0013% | -0.23 | 2.04 (crop 0) | 2.11 | 1.35 | no leak detected | 2.323 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7531.2 | 7531.2 | +1.676 | +0.0223% | +1.98 | 2.30 (crop 7) | 1.74 | 1.53 | no leak detected | 9.451 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15083.3 | 15083.3 | +5.046 | +0.0335% | +0.21 | 2.62 (crop 40) | 1.57 | 2.04 | no leak detected | 18.088 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30208.3 | 30250.0 | -14.405 | -0.0477% | -0.69 | 2.36 (crop 43) | 2.01 | 1.79 | no leak detected | 59.907 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 60458.3 | 60458.3 | +15.394 | +0.0255% | +1.03 | 2.72 (crop 7) | 1.85 | 1.91 | no leak detected | 100.537 |
| xmss_node/z=4 | SK.seed | 1 | 1496 | 1504 | 120916.7 | 120916.7 | -27.110 | -0.0224% | -0.49 | 1.55 (crop 6) | 2.00 | 3.22 | no leak detected | 159.432 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3900708.3 | 3897125.0 | +2042.924 | +0.0524% | +1.97 | 2.26 (crop 63) | 2.20 | 1.99 | no leak detected | 2841.197 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 24.6 | 24.6 | -0.001 | -0.0050% | -0.71 | 2.87 (crop 42) | 2.57 | 1.67 | no leak detected | 0.012 |
| fors_node/z=0 | SK.seed | 256 | 49853 | 50147 | 145.5 | 145.5 | +0.032 | +0.0217% | -0.83 | 1.39 (crop 6) | 1.23 | 1.19 | no leak detected | 0.085 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 213.9 | 213.9 | +0.004 | +0.0020% | +0.02 | 2.37 (crop 1) | 1.61 | 1.21 | no leak detected | 0.099 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 535.8 | 536.5 | -0.045 | -0.0083% | -0.80 | 1.99 (crop 40) | 3.33 | 1.33 | no leak detected | 0.366 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3177.1 | 3182.3 | -1.380 | -0.0435% | -1.61 | 2.13 (crop 52) | 0.99 | 1.42 | no leak detected | 6.685 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6156.2 | 6156.2 | -2.141 | -0.0349% | -0.18 | 1.96 (crop 8) | 1.27 | 1.43 | no leak detected | 11.700 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12291.7 | 12291.7 | -2.684 | -0.0219% | +0.89 | 2.05 (crop 81) | 1.78 | 1.51 | no leak detected | 22.746 |
| fors_node/z=12 | SK.seed | 1 | 1010 | 990 | 197250.0 | 197291.7 | -85.301 | -0.0433% | -0.27 | 1.59 (crop 3) | 1.41 | 1.21 | no leak detected | 268.509 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2809708.3 | 2807125.0 | +212.339 | +0.0076% | +0.35 | 1.45 (crop 0) | 2.63 | 2.08 | no leak detected | 3374.819 |
| fors_pk_gen | SK.seed | 1 | 145 | 155 | 2778375.0 | 2775416.7 | +1673.848 | +0.0603% | +1.99 | 2.35 (crop 62) | 2.38 | 1.72 | no leak detected | 3033.708 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3907333.3 | 3906833.3 | +719.001 | +0.0184% | -0.07 | 1.26 (crop 6) | 2.15 | 1.28 | no leak detected | 1997.334 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 1.7 | 1.0 | +2.530 | +1.9020% | -0.45 | 2.71 (crop 20) | 2.96 | 2.06 | no leak detected | 4.152 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 128 | 10079 | 9921 | 207.0 | 207.0 | +0.990 | +0.5001% | +0.57 | 2.92 (crop 13) | 1.27 | 1.26 | no leak detected | 1.093 |
21:31  up 2 days, 11:51, 4 users, load averages: 1.74 1.56 1.63
