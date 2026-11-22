21:37  up 2 days, 11:57, 4 users, load averages: 2.58 2.33 1.97
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 240.2 | 240.2 | +0.002 | +0.0009% | +1.17 | 2.37 (crop 0) | 1.77 | 1.48 | no leak detected | 0.051 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 225.3 | 225.3 | +0.001 | +0.0004% | +0.31 | 2.06 (crop 4) | 1.10 | 1.06 | no leak detected | 0.046 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 199.2 | 199.2 | -0.004 | -0.0021% | +0.49 | 1.98 (crop 45) | 2.36 | 1.38 | no leak detected | 0.041 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 405.6 | 405.6 | -0.026 | -0.0064% | -1.59 | 2.99 (crop 25) | 1.51 | 1.42 | no leak detected | 0.085 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 401.0 | 401.0 | +0.020 | +0.0050% | +1.68 | 2.27 (crop 12) | 2.14 | 1.45 | no leak detected | 0.089 |
| sha256/len=119 | all message bytes | 64 | 99937 | 100063 | 361.3 | 361.3 | -0.008 | -0.0023% | +0.10 | 1.79 (crop 20) | 0.86 | 2.41 | no leak detected | 0.081 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 570.3 | 570.3 | -0.019 | -0.0033% | +0.30 | 2.41 (crop 15) | 1.94 | 1.47 | no leak detected | 0.111 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 895.8 | 895.8 | -0.007 | -0.0007% | -0.67 | 1.54 (crop 7) | 1.85 | 2.43 | no leak detected | 0.177 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1518.2 | 1518.2 | +0.026 | +0.0017% | -0.76 | 1.44 (crop 80) | 2.66 | 1.91 | no leak detected | 0.340 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 949.2 | 949.2 | -0.022 | -0.0023% | +0.87 | 2.66 (crop 22) | 2.25 | 0.87 | no leak detected | 0.307 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 8 | 50028 | 49972 | 1322.9 | 1322.9 | +0.007 | +0.0005% | +0.15 | 1.49 (crop 85) | 1.53 | 1.24 | no leak detected | 0.622 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 16 | 50008 | 49992 | 1145.8 | 1145.8 | +0.083 | +0.0073% | -0.15 | 2.30 (crop 3) | 1.40 | 1.15 | no leak detected | 0.425 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 987.0 | 987.0 | -0.071 | -0.0072% | -0.22 | 2.30 (crop 48) | 2.16 | 1.28 | no leak detected | 0.294 |
| compress (copy inlined into the wrapper) | state and block | 128 | 100274 | 99726 | 164.1 | 164.1 | +0.000 | +0.0002% | -0.18 | 1.77 (crop 0) | 1.65 | 1.96 | no leak detected | 0.038 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 100170 | 99830 | 168.3 | 168.3 | -0.000 | -0.0001% | -0.39 | 1.38 (crop 20) | 2.08 | 1.85 | no leak detected | 0.040 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 128 | 100365 | 99635 | 168.6 | 168.6 | -0.004 | -0.0026% | +0.65 | 2.81 (crop 35) | 3.01 | 1.77 | no leak detected | 0.039 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 234.0 | 234.0 | +0.003 | +0.0014% | -0.88 | 2.24 (crop 2) | 1.70 | 1.59 | no leak detected | 0.050 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 229.8 | 229.8 | -0.009 | -0.0041% | +0.41 | 2.61 (crop 5) | 1.64 | 1.44 | no leak detected | 0.049 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 32 | 100343 | 99657 | 726.6 | 726.6 | -0.013 | -0.0018% | -0.70 | 1.28 (crop 0) | 0.98 | 1.41 | no leak detected | 0.162 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 8 | 99943 | 100057 | 1770.8 | 1770.8 | -0.016 | -0.0009% | +0.69 | 1.84 (crop 51) | 2.44 | 1.67 | no leak detected | 0.455 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1653.6 | 1653.6 | -0.035 | -0.0021% | +0.99 | 1.56 (crop 98) | 1.54 | 2.17 | no leak detected | 0.539 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 769.5 | 769.5 | -0.033 | -0.0043% | -0.77 | 1.52 (crop 0) | 1.65 | 1.21 | no leak detected | 0.266 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 772.1 | 772.1 | -0.059 | -0.0076% | -1.45 | 3.28 (crop 72) | 2.11 | 1.28 | no leak detected | 0.239 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 937.5 | 937.5 | +0.032 | +0.0034% | -0.67 | 2.11 (crop 0) | 1.22 | 2.04 | no leak detected | 0.291 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 3463.5 | 3463.5 | -0.061 | -0.0018% | -1.15 | 2.09 (crop 80) | 2.82 | 1.33 | no leak detected | 1.059 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 49819 | 50181 | 2593.8 | 2593.8 | -0.150 | -0.0058% | -2.01 | 3.17 (crop 2) | 1.83 | 1.22 | no leak detected | 0.832 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 24932 | 25068 | 10270.8 | 10291.7 | -0.950 | -0.0092% | +0.39 | 2.28 (crop 5) | 2.03 | 1.77 | no leak detected | 4.819 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 89833.3 | 89791.7 | +11.652 | +0.0130% | +1.30 | 3.08 (crop 40) | 3.05 | 1.82 | no leak detected | 39.967 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 39583.3 | 39583.3 | -3.448 | -0.0087% | -0.61 | 1.95 (crop 21) | 2.25 | 1.26 | no leak detected | 25.758 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 2296.9 | 2296.9 | +0.033 | +0.0014% | +0.70 | 1.31 (crop 37) | 1.72 | 1.63 | no leak detected | 0.890 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 4987 | 5013 | 20833.3 | 20833.3 | -3.708 | -0.0178% | +2.03 | 2.56 (crop 93) | 1.74 | 2.16 | no leak detected | 27.062 |
| wots_pk_gen | SK.seed | 1 | 24781 | 25219 | 97041.7 | 97083.3 | -7.799 | -0.0080% | -0.99 | 2.57 (crop 24) | 2.36 | 2.35 | no leak detected | 26.947 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 49666.7 | 49666.7 | -2.281 | -0.0046% | -0.38 | 2.22 (crop 36) | 1.77 | 1.22 | no leak detected | 17.700 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 97083.3 | 97083.3 | +21.318 | +0.0220% | +0.78 | 2.16 (crop 28) | 1.97 | 1.46 | no leak detected | 59.698 |
| xmss_node/z=1 | SK.seed | 1 | 4984 | 5016 | 194208.3 | 194208.3 | +1.569 | +0.0008% | +1.04 | 1.50 (crop 23) | 1.90 | 1.18 | no leak detected | 86.119 |
| xmss_node/z=2 | SK.seed | 1 | 1554 | 1446 | 389166.7 | 389125.0 | -27.355 | -0.0070% | -0.79 | 1.74 (crop 16) | 1.96 | 1.85 | no leak detected | 248.279 |
| xmss_node/z=3 | SK.seed | 1 | 1514 | 1486 | 780375.0 | 779875.0 | -11.572 | -0.0015% | -0.48 | 2.76 (crop 19) | 2.14 | 2.56 | no leak detected | 361.637 |
| xmss_node/z=4 | SK.seed | 1 | 1493 | 1507 | 1564083.3 | 1564166.7 | -298.612 | -0.0191% | -1.07 | 1.87 (crop 6) | 1.06 | 2.61 | no leak detected | 651.791 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 50123416.7 | 50118833.3 | +15168.343 | +0.0303% | +1.44 | 2.53 (crop 50) | 1.83 | 2.25 | no leak detected | 10378.545 |
| fors_sk_gen | SK.seed | 128 | 99973 | 100027 | 172.5 | 172.5 | +0.006 | +0.0033% | +0.64 | 1.76 (crop 34) | 1.87 | 1.77 | no leak detected | 0.039 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 439.5 | 439.5 | -0.050 | -0.0113% | -0.23 | 2.19 (crop 39) | 1.86 | 1.28 | no leak detected | 0.142 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 958.3 | 958.3 | +0.071 | +0.0074% | -0.22 | 1.97 (crop 36) | 1.74 | 2.23 | no leak detected | 0.281 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 4015.6 | 4015.6 | -0.294 | -0.0073% | +0.42 | 1.87 (crop 37) | 0.93 | 2.59 | no leak detected | 2.036 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 32083.3 | 32083.3 | -0.964 | -0.0030% | +0.89 | 2.04 (crop 6) | 0.96 | 1.74 | no leak detected | 37.003 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 64708.3 | 64708.3 | +14.365 | +0.0223% | -0.21 | 1.94 (crop 9) | 1.62 | 2.03 | no leak detected | 62.138 |
| fors_node/z=8 | SK.seed | 1 | 2466 | 2534 | 129666.7 | 129750.0 | -61.070 | -0.0472% | -1.35 | 2.03 (crop 3) | 1.65 | 1.91 | no leak detected | 99.425 |
| fors_node/z=12 | SK.seed | 1 | 1013 | 987 | 2073958.3 | 2073541.7 | +376.085 | +0.0182% | -0.12 | 1.58 (crop 42) | 1.62 | 1.12 | no leak detected | 1041.755 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 28911583.3 | 28912750.0 | +1860.203 | +0.0064% | +1.18 | 1.46 (crop 9) | 2.84 | 2.58 | no leak detected | 12546.380 |
| fors_pk_gen | SK.seed | 1 | 147 | 153 | 28978000.0 | 28958583.3 | +8010.167 | +0.0277% | +0.92 | 1.55 (crop 24) | 2.40 | 2.09 | no leak detected | 13773.013 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 50127875.0 | 50127875.0 | -5453.005 | -0.0109% | +0.87 | 1.62 (crop 89) | 1.96 | 2.43 | no leak detected | 9279.413 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.8 | 1.2 | -133.310 | -197.5988% | -70.37 | 75.17 (crop 58) | 2.44 | 1.73 | leak detected (expected: control) | 4.412 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 815.1 | 815.1 | +98.155 | +12.7307% | +1.02 | 119.92 (crop 2) | 1.20 | 1.82 | leak detected (expected: control) | 2.977 |
21:43  up 2 days, 12:02, 4 users, load averages: 2.48 2.45 2.13
