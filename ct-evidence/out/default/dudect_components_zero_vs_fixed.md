21:43  up 2 days, 12:02, 4 users, load averages: 2.48 2.45 2.13
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-fixed; fixed class = all-zero secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 209.3 | 209.3 | +0.001 | +0.0003% | +2.21 | 2.21 | 1.41 | 1.45 | no leak detected | 0.047 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 194.3 | 194.7 | -0.047 | -0.0239% | -2.07 | 8.35 (crop 28) | 1.84 | 1.06 | **t > 4.5** | 0.046 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 170.6 | 170.6 | -0.057 | -0.0332% | -1.08 | 9.77 (crop 19) | 2.63 | 2.24 | **t > 4.5** | 0.042 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 347.7 | 347.7 | -0.038 | -0.0109% | -0.03 | 8.38 (crop 17) | 1.35 | 1.87 | **t > 4.5** | 0.105 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 348.3 | 348.3 | +0.051 | +0.0144% | -0.40 | 29.51 (crop 14) | 0.99 | 1.09 | **t > 4.5** | 0.113 |
| sha256/len=119 | all message bytes | 64 | 99937 | 100063 | 307.9 | 307.9 | +0.202 | +0.0643% | -4.38 | 38.27 (crop 13) | 1.36 | 1.51 | **t > 4.5** | 0.111 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 485.7 | 485.7 | -0.192 | -0.0387% | -1.20 | 16.38 (crop 16) | 1.33 | 1.77 | **t > 4.5** | 0.162 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 768.2 | 768.2 | -0.042 | -0.0053% | -2.19 | 56.33 (crop 9) | 1.58 | 1.49 | **t > 4.5** | 0.276 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1286.5 | 1289.1 | +0.146 | +0.0110% | -3.03 | 57.83 (crop 9) | 1.48 | 1.54 | **t > 4.5** | 0.507 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 809.9 | 811.2 | +0.086 | +0.0105% | -0.66 | 7.14 (crop 18) | 1.56 | 1.65 | **t > 4.5** | 0.328 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 8 | 50028 | 49972 | 1135.4 | 1135.4 | -0.105 | -0.0091% | -0.33 | 4.94 (crop 14) | 1.08 | 1.61 | **t > 4.5** | 0.629 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 979.2 | 979.2 | -0.042 | -0.0042% | -0.30 | 2.51 (crop 29) | 0.93 | 1.76 | no leak detected | 0.348 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 846.4 | 846.4 | -0.028 | -0.0033% | +0.51 | 10.45 (crop 20) | 1.43 | 1.21 | **t > 4.5** | 0.317 |
| compress (copy inlined into the wrapper) | state and block | 256 | 100274 | 99726 | 138.0 | 139.2 | -0.766 | -0.5499% | -102.50 | 238.37 (crop 19) | 1.73 | 1.45 | **t > 4.5** | 0.039 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 100170 | 99830 | 145.0 | 145.0 | +0.043 | +0.0292% | +0.31 | 3.86 (crop 15) | 1.77 | 0.92 | no leak detected | 0.049 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 100365 | 99635 | 145.2 | 145.2 | +0.139 | +0.0942% | -1.46 | 14.06 (crop 18) | 1.22 | 1.74 | **t > 4.5** | 0.046 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 206.1 | 206.1 | -0.028 | -0.0134% | -0.78 | 6.05 (crop 10) | 1.34 | 1.58 | **t > 4.5** | 0.058 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 201.2 | 201.5 | -0.014 | -0.0067% | -2.01 | 6.00 (crop 20) | 1.02 | 2.26 | **t > 4.5** | 0.057 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 32 | 100343 | 99657 | 621.1 | 621.1 | +0.087 | +0.0138% | -0.95 | 7.99 (crop 9) | 2.07 | 1.05 | **t > 4.5** | 0.216 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 16 | 99943 | 100057 | 1513.0 | 1513.0 | +0.562 | +0.0361% | -1.30 | 20.10 (crop 5) | 1.99 | 2.82 | **t > 4.5** | 0.565 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1401.0 | 1403.6 | +1.699 | +0.1184% | +0.77 | 34.51 (crop 7) | 0.97 | 1.80 | **t > 4.5** | 0.753 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 653.6 | 653.6 | -0.014 | -0.0021% | +1.91 | 1.91 | 1.44 | 1.37 | no leak detected | 0.290 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 657.6 | 657.6 | +0.210 | +0.0314% | -0.73 | 4.97 (crop 8) | 1.42 | 1.01 | **t > 4.5** | 0.308 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 796.9 | 796.9 | -0.250 | -0.0308% | -0.19 | 2.43 (crop 20) | 1.60 | 1.82 | no leak detected | 0.382 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 2947.9 | 2947.9 | +2.055 | +0.0677% | +0.70 | 2.00 (crop 23) | 1.68 | 2.32 | no leak detected | 1.553 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 49819 | 50181 | 2070.3 | 2070.3 | +0.063 | +0.0030% | -0.31 | 4.82 (crop 18) | 1.93 | 1.46 | **t > 4.5** | 1.163 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 24932 | 25068 | 8250.0 | 8250.0 | -12.163 | -0.1467% | -3.29 | 34.56 (crop 18) | 1.60 | 2.23 | **t > 4.5** | 6.728 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 72166.7 | 72375.0 | -128.591 | -0.1746% | -1.33 | 38.98 (crop 18) | 1.37 | 1.60 | **t > 4.5** | 96.361 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 31916.7 | 31958.3 | -69.440 | -0.2156% | -1.37 | 24.67 (crop 4) | 1.64 | 2.15 | **t > 4.5** | 39.226 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 1934.9 | 1937.5 | +13.690 | +0.6698% | -2.63 | 40.30 (crop 9) | 1.46 | 1.38 | **t > 4.5** | 1.672 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 4987 | 5013 | 17833.3 | 17854.2 | +208.669 | +1.1072% | -2.66 | 13.22 (crop 19) | 1.28 | 0.98 | **t > 4.5** | 36.905 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 78208.3 | 78208.3 | -1.442 | -0.0018% | -0.01 | 1.80 (crop 10) | 2.11 | 2.26 | no leak detected | 51.383 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 40208.3 | 40208.3 | +3.845 | +0.0095% | -0.09 | 1.77 (crop 40) | 1.07 | 2.14 | no leak detected | 28.040 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 78208.3 | 78208.3 | -29.025 | -0.0369% | -0.98 | 2.96 (crop 46) | 1.62 | 1.80 | no leak detected | 112.129 |
| xmss_node/z=1 | SK.seed | 1 | 4983 | 5017 | 156625.0 | 156625.0 | -15.065 | -0.0096% | -0.55 | 1.93 (crop 24) | 1.97 | 1.78 | no leak detected | 225.267 |
| xmss_node/z=2 | SK.seed | 1 | 1549 | 1451 | 313375.0 | 313333.3 | +33.854 | +0.0107% | +1.52 | 1.92 (crop 25) | 1.59 | 1.59 | no leak detected | 808.165 |
| xmss_node/z=3 | SK.seed | 1 | 1516 | 1484 | 627333.3 | 627250.0 | +453.746 | +0.0718% | +0.45 | 1.94 (crop 35) | 1.78 | 2.68 | no leak detected | 1339.276 |
| xmss_node/z=4 | SK.seed | 1 | 1490 | 1510 | 1264208.3 | 1263166.7 | +738.346 | +0.0583% | -0.13 | 2.25 (crop 11) | 1.43 | 2.18 | no leak detected | 3185.658 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 40556541.7 | 40522166.7 | +58510.254 | +0.1428% | -0.00 | 2.76 (crop 25) | 1.95 | 2.63 | no leak detected | 111590.157 |
| fors_sk_gen | SK.seed | 256 | 99973 | 100027 | 148.8 | 148.8 | -0.016 | -0.0108% | +0.30 | 3.78 (crop 5) | 1.14 | 1.98 | no leak detected | 0.048 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 380.2 | 380.9 | -0.017 | -0.0043% | +0.16 | 1.35 (crop 12) | 1.06 | 1.49 | no leak detected | 0.200 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 806.0 | 806.0 | -0.160 | -0.0194% | +0.31 | 1.32 (crop 20) | 1.12 | 1.22 | no leak detected | 0.438 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3317.7 | 3317.7 | -1.569 | -0.0462% | +1.01 | 2.25 (crop 0) | 1.29 | 1.56 | no leak detected | 3.575 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 26625.0 | 26625.0 | +1.711 | +0.0064% | -0.06 | 1.38 (crop 37) | 2.29 | 1.96 | no leak detected | 35.940 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 53291.7 | 53291.7 | +45.464 | +0.0822% | -0.71 | 1.33 (crop 24) | 1.39 | 1.92 | no leak detected | 138.363 |
| fors_node/z=8 | SK.seed | 1 | 2461 | 2539 | 106500.0 | 106541.7 | -271.108 | -0.2480% | -2.79 | 2.79 | 1.30 | 2.19 | no leak detected | 244.299 |
| fors_node/z=12 | SK.seed | 1 | 1013 | 987 | 1725125.0 | 1726000.0 | -3069.742 | -0.1731% | -1.04 | 1.31 (crop 59) | 1.57 | 2.17 | no leak detected | 6153.491 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 25129666.7 | 25128083.3 | +108073.432 | +0.4314% | -0.44 | 1.77 (crop 1) | 1.64 | 2.17 | no leak detected | 136388.655 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 40494500.0 | 40500875.0 | +33439.446 | +0.0820% | -1.51 | 1.72 (crop 26) | 3.13 | 2.65 | no leak detected | 90835.498 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 32 | 9933 | 10067 | 3427.1 | 630.2 | +2790.867 | +137.3629% | +2704.83 | 9033.98 (crop 20) | 1.91 | 1.65 | leak detected (expected: control) | 1.043 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 1.3 | 1039.1 | -1036.695 | -199.3187% | -1970.04 | 29882.74 (crop 20) | 1.56 | 1.31 | leak detected (expected: control) | 0.533 |
21:46  up 2 days, 12:06, 4 users, load averages: 2.37 2.62 2.30
