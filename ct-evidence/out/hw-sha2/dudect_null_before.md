21:05  up 2 days, 11:24, 4 users, load averages: 1.87 1.87 1.78
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 1 | 99951 | 100049 | 125.0 | 125.0 | +0.379 | +0.3080% | +3.01 | 3.19 (crop 20) | 1.20 | 1.19 | no leak detected | 0.349 |
| sha256/len=16 | all message bytes | 512 | 100068 | 99932 | 73.2 | 73.2 | +0.009 | +0.0124% | -1.11 | 2.19 (crop 44) | 1.15 | 1.14 | no leak detected | 0.022 |
| sha256/len=55 | all message bytes | 512 | 100065 | 99935 | 47.5 | 47.4 | +0.003 | +0.0064% | +2.11 | 2.56 (crop 54) | 1.11 | 1.33 | no leak detected | 0.018 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 100.9 | 100.9 | +0.010 | +0.0101% | -0.29 | 2.25 (crop 50) | 2.38 | 1.30 | no leak detected | 0.033 |
| sha256/len=64 | all message bytes | 256 | 100273 | 99727 | 99.1 | 99.1 | -0.004 | -0.0040% | -0.79 | 1.82 (crop 68) | 0.86 | 2.13 | no leak detected | 0.034 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 61.5 | 61.5 | -0.010 | -0.0153% | -0.05 | 2.15 (crop 8) | 2.57 | 1.34 | no leak detected | 0.025 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 114.7 | 114.7 | +0.019 | +0.0163% | +0.46 | 1.51 (crop 1) | 1.43 | 1.19 | no leak detected | 0.037 |
| sha256/len=256 | all message bytes | 256 | 99847 | 100153 | 151.9 | 151.9 | +0.021 | +0.0141% | -0.65 | 1.93 (crop 28) | 1.10 | 1.74 | no leak detected | 0.038 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 184.2 | 184.2 | +0.012 | +0.0067% | -0.21 | 1.63 (crop 12) | 1.59 | 1.41 | no leak detected | 0.056 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 315.8 | 315.8 | -0.153 | -0.0479% | -1.74 | 2.46 (crop 4) | 1.44 | 0.94 | no leak detected | 0.195 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 411.5 | 412.1 | -0.228 | -0.0562% | -1.10 | 1.66 (crop 94) | 1.91 | 1.99 | no leak detected | 0.241 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 365.2 | 364.6 | -0.007 | -0.0018% | +0.10 | 2.53 (crop 4) | 1.44 | 1.44 | no leak detected | 0.206 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 353.5 | 353.5 | -0.026 | -0.0071% | -0.27 | 1.55 (crop 20) | 1.44 | 1.27 | no leak detected | 0.216 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 15.4 | 15.4 | +0.000 | +0.0030% | +0.01 | 1.43 (crop 3) | 1.39 | 1.62 | no leak detected | 0.004 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 24.7 | 24.7 | -0.002 | -0.0063% | -0.76 | 1.76 (crop 49) | 1.54 | 2.67 | no leak detected | 0.014 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 24.1 | 24.1 | -0.000 | -0.0001% | +0.69 | 1.30 (crop 47) | 2.70 | 1.37 | no leak detected | 0.014 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 87.6 | 87.6 | -0.028 | -0.0316% | -0.14 | 2.30 (crop 1) | 1.79 | 1.67 | no leak detected | 0.040 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 84.3 | 84.3 | -0.010 | -0.0114% | -1.17 | 1.52 (crop 63) | 2.10 | 1.22 | no leak detected | 0.035 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 256 | 100343 | 99657 | 133.5 | 133.3 | -0.025 | -0.0182% | -0.58 | 1.84 (crop 19) | 1.42 | 0.89 | no leak detected | 0.071 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 128 | 99943 | 100057 | 299.2 | 299.5 | -0.085 | -0.0284% | -0.15 | 2.62 (crop 30) | 1.63 | 1.22 | no leak detected | 0.083 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 188.2 | 188.2 | -0.006 | -0.0034% | +0.60 | 2.05 (crop 28) | 2.30 | 1.26 | no leak detected | 0.084 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 256 | 50086 | 49914 | 155.8 | 155.8 | +0.047 | +0.0297% | -0.39 | 2.16 (crop 6) | 1.66 | 1.62 | no leak detected | 0.080 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 179.0 | 178.4 | +0.188 | +0.1056% | +1.02 | 1.56 (crop 76) | 2.12 | 2.55 | no leak detected | 0.137 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 202.5 | 202.8 | -0.105 | -0.0523% | -1.55 | 1.82 (crop 5) | 1.64 | 3.08 | no leak detected | 0.145 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 534.5 | 534.5 | -0.065 | -0.0121% | -1.53 | 2.32 (crop 6) | 1.43 | 2.14 | no leak detected | 0.222 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 308.6 | 308.6 | +0.012 | +0.0040% | -0.99 | 2.62 (crop 51) | 1.72 | 1.67 | no leak detected | 0.130 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 799.5 | 799.5 | +0.090 | +0.0113% | +0.15 | 2.27 (crop 26) | 2.65 | 1.53 | no leak detected | 0.448 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6802.1 | 6812.5 | -1.229 | -0.0181% | +0.33 | 2.32 (crop 44) | 1.07 | 1.55 | no leak detected | 5.813 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3083.3 | 3083.3 | +0.160 | +0.0052% | -1.27 | 2.03 (crop 79) | 1.35 | 1.70 | no leak detected | 2.388 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 220.4 | 220.4 | -0.013 | -0.0060% | -0.31 | 2.69 (crop 45) | 1.28 | 1.40 | no leak detected | 0.102 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1776.0 | 1776.0 | -0.394 | -0.0222% | -0.87 | 1.87 (crop 0) | 1.99 | 2.27 | no leak detected | 1.961 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7531.2 | 7531.2 | +0.288 | +0.0038% | +0.29 | 1.58 (crop 1) | 1.87 | 1.29 | no leak detected | 3.478 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4239.6 | 4239.6 | -0.257 | -0.0061% | -0.31 | 2.57 (crop 41) | 1.61 | 1.88 | no leak detected | 1.948 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7531.2 | 7531.2 | +0.341 | +0.0045% | +0.76 | 2.63 (crop 51) | 1.31 | 1.20 | no leak detected | 8.628 |
| xmss_node/z=1 | SK.seed | 1 | 4982 | 5018 | 15125.0 | 15083.3 | +2.000 | +0.0133% | -0.17 | 1.92 (crop 46) | 1.14 | 2.30 | no leak detected | 21.678 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30250.0 | 30291.7 | -6.914 | -0.0228% | +0.02 | 2.13 (crop 5) | 1.73 | 1.94 | no leak detected | 68.074 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 60458.3 | 60458.3 | +9.669 | +0.0160% | +0.49 | 2.17 (crop 49) | 1.65 | 1.87 | no leak detected | 95.518 |
| xmss_node/z=4 | SK.seed | 1 | 1493 | 1507 | 121000.0 | 120916.7 | +27.053 | +0.0224% | +0.25 | 1.78 (crop 5) | 2.49 | 1.40 | no leak detected | 161.099 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3899333.3 | 3901041.7 | -789.781 | -0.0203% | -0.80 | 1.18 (crop 17) | 1.60 | 1.61 | no leak detected | 2752.321 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 24.7 | 24.7 | +0.002 | +0.0081% | +0.04 | 1.64 (crop 30) | 1.21 | 1.59 | no leak detected | 0.013 |
| fors_node/z=0 | SK.seed | 256 | 49853 | 50147 | 157.9 | 157.9 | -0.060 | -0.0382% | -1.67 | 1.67 | 1.28 | 1.01 | no leak detected | 0.105 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 218.4 | 218.4 | -0.047 | -0.0216% | -1.52 | 1.79 (crop 35) | 0.89 | 1.48 | no leak detected | 0.099 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 536.5 | 536.5 | +0.024 | +0.0044% | -0.44 | 1.76 (crop 58) | 1.34 | 1.55 | no leak detected | 0.340 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3187.5 | 3187.5 | -0.475 | -0.0149% | -0.18 | 2.13 (crop 44) | 1.26 | 1.36 | no leak detected | 6.102 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6145.8 | 6156.2 | -0.963 | -0.0157% | -0.82 | 0.87 (crop 43) | 1.51 | 1.29 | no leak detected | 10.903 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12312.5 | 12312.5 | -2.909 | -0.0237% | -1.85 | 2.22 (crop 70) | 1.45 | 1.72 | no leak detected | 20.885 |
| fors_node/z=12 | SK.seed | 1 | 1010 | 990 | 197458.3 | 197500.0 | -144.110 | -0.0730% | -0.06 | 1.21 (crop 32) | 1.19 | 1.15 | no leak detected | 266.578 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2819166.7 | 2813041.7 | +4262.206 | +0.1515% | +0.58 | 2.10 (crop 31) | 1.36 | 1.83 | no leak detected | 4493.341 |
| fors_pk_gen | SK.seed | 1 | 145 | 155 | 2783375.0 | 2784000.0 | +258.212 | +0.0093% | -0.79 | 1.68 (crop 19) | 1.58 | 3.01 | no leak detected | 3313.480 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3904166.7 | 3904666.7 | -895.657 | -0.0230% | -0.82 | 1.40 (crop 62) | 1.39 | 2.70 | no leak detected | 1726.251 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 1.2 | 1.0 | +4.206 | +3.1232% | -0.46 | 2.61 (crop 1) | 2.85 | 2.22 | no leak detected | 4.203 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 64 | 10079 | 9921 | 211.6 | 211.6 | +0.858 | +0.4286% | +0.58 | 2.55 (crop 14) | 1.35 | 1.00 | no leak detected | 1.089 |
21:08  up 2 days, 11:28, 4 users, load averages: 2.30 1.96 1.82
