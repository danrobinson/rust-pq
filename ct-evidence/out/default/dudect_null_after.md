20:30  up 2 days, 10:49, 4 users, load averages: 1.66 1.61 1.59
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 204.8 | 204.8 | -0.007 | -0.0033% | +0.43 | 1.22 (crop 37) | 1.50 | 1.61 | no leak detected | 0.055 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 189.1 | 189.1 | +0.001 | +0.0004% | +1.44 | 2.57 (crop 73) | 1.66 | 1.83 | no leak detected | 0.057 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 167.6 | 167.6 | -0.042 | -0.0247% | -2.04 | 2.83 (crop 64) | 1.38 | 2.37 | no leak detected | 0.057 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 339.8 | 339.8 | -0.063 | -0.0182% | -0.18 | 2.03 (crop 14) | 2.88 | 1.66 | no leak detected | 0.118 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 339.2 | 339.2 | +0.042 | +0.0123% | +1.22 | 1.40 (crop 98) | 1.98 | 1.67 | no leak detected | 0.122 |
| sha256/len=119 | all message bytes | 128 | 99937 | 100063 | 301.4 | 301.4 | -0.051 | -0.0165% | -0.08 | 1.19 (crop 38) | 0.76 | 1.38 | no leak detected | 0.102 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 474.6 | 474.6 | -0.175 | -0.0357% | -1.53 | 2.66 (crop 72) | 1.73 | 1.41 | no leak detected | 0.181 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 751.3 | 751.3 | +0.084 | +0.0110% | +0.68 | 1.73 (crop 83) | 1.54 | 1.00 | no leak detected | 0.289 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1263.0 | 1263.0 | +0.116 | +0.0090% | -1.43 | 1.89 (crop 16) | 2.26 | 1.56 | no leak detected | 0.530 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 790.4 | 790.4 | -0.046 | -0.0058% | +0.83 | 2.29 (crop 0) | 0.97 | 1.83 | no leak detected | 0.316 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 50028 | 49972 | 1106.8 | 1106.8 | +0.315 | +0.0282% | -0.34 | 1.26 (crop 15) | 1.24 | 1.78 | no leak detected | 0.476 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 960.9 | 960.9 | +0.102 | +0.0105% | +0.97 | 1.33 (crop 26) | 1.29 | 2.49 | no leak detected | 0.417 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 829.4 | 829.4 | -0.156 | -0.0187% | -1.27 | 1.71 (crop 74) | 1.24 | 1.22 | no leak detected | 0.350 |
| compress (copy inlined into the wrapper) | state and block | 256 | 100274 | 99726 | 136.1 | 136.1 | +0.020 | +0.0143% | +0.78 | 1.91 (crop 46) | 2.36 | 2.76 | no leak detected | 0.047 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 100170 | 99830 | 141.8 | 141.8 | +0.033 | +0.0230% | +0.49 | 1.89 (crop 1) | 1.94 | 1.05 | no leak detected | 0.051 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 100365 | 99635 | 142.3 | 142.3 | +0.009 | +0.0061% | -1.27 | 2.14 (crop 23) | 1.72 | 3.76 | no leak detected | 0.052 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 201.5 | 201.5 | -0.039 | -0.0192% | -1.67 | 2.42 (crop 27) | 1.18 | 1.80 | no leak detected | 0.071 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 197.3 | 197.3 | +0.034 | +0.0173% | -0.10 | 1.98 (crop 27) | 1.21 | 1.38 | no leak detected | 0.068 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 64 | 100343 | 99657 | 608.1 | 608.1 | -0.150 | -0.0241% | -0.30 | 1.83 (crop 21) | 1.98 | 1.32 | no leak detected | 0.219 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 16 | 99943 | 100057 | 1481.8 | 1481.8 | +0.409 | +0.0267% | +0.66 | 1.84 (crop 43) | 1.50 | 1.42 | no leak detected | 0.595 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1372.4 | 1372.4 | +0.205 | +0.0148% | -0.03 | 1.29 (crop 39) | 2.13 | 1.68 | no leak detected | 0.739 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 639.3 | 639.3 | -0.103 | -0.0160% | -1.95 | 2.24 (crop 91) | 1.51 | 2.05 | no leak detected | 0.329 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 641.9 | 641.9 | +0.116 | +0.0179% | -0.65 | 1.68 (crop 41) | 1.63 | 1.52 | no leak detected | 0.291 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 779.9 | 781.2 | -0.048 | -0.0060% | +0.04 | 2.81 (crop 19) | 0.87 | 2.01 | no leak detected | 0.403 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 2885.4 | 2885.4 | -0.868 | -0.0292% | -1.08 | 1.63 (crop 67) | 0.93 | 1.51 | no leak detected | 1.717 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 49819 | 50181 | 2028.6 | 2028.6 | +0.081 | +0.0040% | +1.15 | 2.60 (crop 12) | 1.72 | 1.58 | no leak detected | 0.890 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 24932 | 25068 | 8083.3 | 8083.3 | +0.696 | +0.0086% | +1.66 | 1.87 (crop 26) | 1.72 | 1.74 | no leak detected | 6.643 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 70666.7 | 70666.7 | +9.142 | +0.0129% | +1.45 | 1.67 (crop 38) | 2.11 | 1.13 | no leak detected | 73.585 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 31166.7 | 31166.7 | +7.099 | +0.0227% | +0.99 | 2.30 (crop 21) | 1.73 | 1.83 | no leak detected | 36.992 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 1893.2 | 1893.2 | -0.316 | -0.0160% | -1.03 | 1.61 (crop 12) | 1.77 | 0.99 | no leak detected | 1.645 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 4987 | 5013 | 17291.7 | 17291.7 | +42.382 | +0.2325% | +1.44 | 2.07 (crop 62) | 1.79 | 1.27 | no leak detected | 34.504 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 76625.0 | 76625.0 | +11.308 | +0.0147% | +2.77 | 3.42 (crop 39) | 1.79 | 1.62 | no leak detected | 44.947 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 39375.0 | 39375.0 | -11.760 | -0.0298% | -0.19 | 2.69 (crop 32) | 1.27 | 2.63 | no leak detected | 27.914 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 76625.0 | 76625.0 | +14.352 | +0.0187% | -1.73 | 2.26 (crop 36) | 1.34 | 1.95 | no leak detected | 90.878 |
| xmss_node/z=1 | SK.seed | 1 | 4981 | 5019 | 153458.3 | 153416.7 | +37.632 | +0.0244% | -1.41 | 1.79 (crop 65) | 1.38 | 2.73 | no leak detected | 164.514 |
| xmss_node/z=2 | SK.seed | 1 | 1549 | 1451 | 306958.3 | 307000.0 | +184.814 | +0.0597% | -0.56 | 1.65 (crop 14) | 3.14 | 1.87 | no leak detected | 772.509 |
| xmss_node/z=3 | SK.seed | 1 | 1518 | 1482 | 617333.3 | 616541.7 | +0.287 | +0.0000% | +1.29 | 2.39 (crop 1) | 1.93 | 1.81 | no leak detected | 1444.579 |
| xmss_node/z=4 | SK.seed | 1 | 1489 | 1511 | 1239750.0 | 1239958.3 | -56.393 | -0.0046% | -1.42 | 2.65 (crop 1) | 1.99 | 2.45 | no leak detected | 2282.238 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 39698375.0 | 39698958.3 | +44786.490 | +0.1122% | +0.35 | 1.52 (crop 2) | 2.46 | 1.87 | no leak detected | 89287.160 |
| fors_sk_gen | SK.seed | 256 | 99973 | 100027 | 146.2 | 146.2 | +0.038 | +0.0257% | +0.26 | 1.66 (crop 13) | 0.98 | 1.29 | no leak detected | 0.049 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 370.4 | 370.4 | -0.071 | -0.0190% | -0.29 | 1.17 (crop 27) | 0.86 | 1.68 | no leak detected | 0.190 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 786.5 | 786.5 | -0.320 | -0.0401% | -1.06 | 2.45 (crop 29) | 1.07 | 1.45 | no leak detected | 0.433 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3250.0 | 3250.0 | -2.926 | -0.0881% | -0.49 | 1.75 (crop 31) | 1.67 | 1.16 | no leak detected | 3.733 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 26041.7 | 26041.7 | -84.978 | -0.3178% | -2.25 | 2.54 (crop 83) | 1.13 | 1.60 | no leak detected | 77.299 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 52250.0 | 52208.3 | +19.895 | +0.0360% | +0.64 | 1.96 (crop 5) | 1.80 | 1.62 | no leak detected | 151.366 |
| fors_node/z=8 | SK.seed | 1 | 2462 | 2538 | 106500.0 | 104708.3 | +506.579 | +0.4535% | +1.05 | 2.13 (crop 35) | 2.11 | 1.67 | no leak detected | 295.690 |
| fors_node/z=12 | SK.seed | 1 | 1014 | 986 | 1696666.7 | 1699000.0 | -1656.391 | -0.0937% | +0.07 | 2.24 (crop 12) | 1.53 | 1.93 | no leak detected | 6493.858 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 25032791.7 | 25213958.3 | -57523.405 | -0.2314% | -1.40 | 2.50 (crop 3) | 2.47 | 2.03 | no leak detected | 134480.132 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 39710166.7 | 39720125.0 | -9108.122 | -0.0228% | -1.60 | 2.71 (crop 3) | 2.07 | 1.77 | no leak detected | 56622.983 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 1.3 | 1.0 | +5.140 | +3.8643% | -0.46 | 2.29 (crop 26) | 2.48 | 2.04 | no leak detected | 4.149 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 678.4 | 678.4 | +3.736 | +0.5780% | +0.90 | 2.86 (crop 13) | 1.33 | 1.20 | no leak detected | 3.500 |
20:35  up 2 days, 10:54, 4 users, load averages: 1.34 1.53 1.56
