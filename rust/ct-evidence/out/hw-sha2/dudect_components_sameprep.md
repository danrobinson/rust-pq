21:46  up 2 days, 12:06, 4 users, load averages: 2.37 2.62 2.30
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 90.7 | 90.8 | -0.093 | -0.1019% | -1.69 | 6.73 (crop 2) | 1.42 | 1.43 | **t > 4.5** | 0.032 |
| sha256/len=16 | all message bytes | 512 | 100068 | 99932 | 74.8 | 74.8 | -0.002 | -0.0032% | -0.23 | 2.59 (crop 26) | 1.26 | 1.03 | no leak detected | 0.022 |
| sha256/len=55 | all message bytes | 512 | 100065 | 99935 | 48.4 | 48.4 | -0.010 | -0.0212% | -1.79 | 4.08 (crop 5) | 2.03 | 1.18 | no leak detected | 0.017 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 102.7 | 102.7 | +0.004 | +0.0034% | -0.26 | 2.75 (crop 25) | 2.12 | 1.22 | no leak detected | 0.033 |
| sha256/len=64 | all message bytes | 256 | 100273 | 99727 | 101.1 | 101.1 | -0.018 | -0.0181% | -0.49 | 2.71 (crop 19) | 1.42 | 1.09 | no leak detected | 0.032 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 62.9 | 62.9 | -0.003 | -0.0052% | -0.34 | 3.38 (crop 0) | 1.29 | 0.94 | no leak detected | 0.023 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 117.7 | 117.7 | -0.000 | -0.0003% | +0.03 | 1.63 (crop 5) | 2.35 | 1.59 | no leak detected | 0.035 |
| sha256/len=256 | all message bytes | 256 | 99847 | 100153 | 154.3 | 154.3 | -0.012 | -0.0075% | -1.26 | 1.91 (crop 6) | 1.20 | 1.17 | no leak detected | 0.035 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 187.8 | 187.8 | +0.010 | +0.0054% | +0.08 | 2.19 (crop 20) | 1.72 | 2.28 | no leak detected | 0.050 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 323.6 | 323.6 | +0.017 | +0.0053% | +0.28 | 1.98 (crop 11) | 1.09 | 1.41 | no leak detected | 0.174 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 387.4 | 387.4 | -0.057 | -0.0145% | -0.99 | 2.41 (crop 0) | 1.47 | 1.30 | no leak detected | 0.213 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 374.3 | 374.3 | -0.161 | -0.0422% | -0.77 | 1.94 (crop 30) | 1.61 | 1.49 | no leak detected | 0.195 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 358.7 | 358.7 | +0.103 | +0.0283% | +0.44 | 3.24 (crop 1) | 1.93 | 1.35 | no leak detected | 0.207 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 15.8 | 15.8 | +0.000 | +0.0022% | -1.65 | 2.06 (crop 18) | 2.03 | 3.04 | no leak detected | 0.004 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 25.3 | 25.3 | -0.002 | -0.0088% | -0.56 | 1.90 (crop 51) | 1.73 | 1.83 | no leak detected | 0.014 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 24.7 | 24.7 | +0.003 | +0.0102% | -0.59 | 1.83 (crop 0) | 2.22 | 2.19 | no leak detected | 0.016 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 90.3 | 90.5 | -0.016 | -0.0178% | -0.46 | 1.54 (crop 1) | 1.08 | 1.82 | no leak detected | 0.040 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 81.4 | 81.4 | +0.007 | +0.0080% | -0.45 | 3.52 (crop 9) | 1.79 | 1.07 | no leak detected | 0.038 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 128 | 100343 | 99657 | 136.7 | 136.4 | +0.041 | +0.0282% | -1.02 | 3.52 (crop 11) | 1.69 | 1.96 | no leak detected | 0.081 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 64 | 99943 | 100057 | 306.0 | 306.0 | +0.012 | +0.0040% | -0.06 | 1.53 (crop 7) | 2.08 | 1.44 | no leak detected | 0.093 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 192.1 | 192.1 | -0.001 | -0.0004% | -0.31 | 1.29 (crop 43) | 1.17 | 1.31 | no leak detected | 0.068 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 128 | 50086 | 49914 | 161.5 | 161.5 | -0.026 | -0.0158% | -0.12 | 2.37 (crop 12) | 1.50 | 0.77 | no leak detected | 0.089 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 192.7 | 193.4 | -0.128 | -0.0708% | -1.61 | 1.61 | 1.85 | 0.94 | no leak detected | 0.131 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 223.0 | 223.0 | +0.069 | +0.0330% | -0.35 | 0.89 (crop 9) | 1.82 | 1.41 | no leak detected | 0.130 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 539.1 | 539.1 | -0.022 | -0.0040% | -1.34 | 1.75 (crop 2) | 1.82 | 1.13 | no leak detected | 0.218 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 64 | 49819 | 50181 | 315.1 | 315.1 | -0.024 | -0.0075% | -0.52 | 2.46 (crop 31) | 1.37 | 1.40 | no leak detected | 0.110 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 816.4 | 816.4 | -0.025 | -0.0031% | -1.74 | 1.74 | 1.25 | 2.46 | no leak detected | 0.381 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6968.8 | 6968.8 | -0.987 | -0.0142% | +0.19 | 1.61 (crop 50) | 3.39 | 1.31 | no leak detected | 4.823 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3156.2 | 3156.2 | +0.146 | +0.0046% | +0.46 | 1.60 (crop 79) | 2.88 | 1.84 | no leak detected | 2.317 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 225.3 | 225.3 | -0.016 | -0.0072% | -1.05 | 1.60 (crop 0) | 1.97 | 1.39 | no leak detected | 0.085 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1812.5 | 1815.1 | -0.751 | -0.0413% | +0.86 | 2.27 (crop 1) | 1.17 | 1.49 | no leak detected | 1.838 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7687.5 | 7687.5 | +0.131 | +0.0017% | -0.57 | 1.68 (crop 87) | 1.85 | 0.88 | no leak detected | 3.303 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4317.7 | 4317.7 | -0.009 | -0.0002% | +0.20 | 1.38 (crop 3) | 2.24 | 1.37 | no leak detected | 1.856 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7687.5 | 7687.5 | -0.497 | -0.0065% | -0.10 | 2.22 (crop 7) | 2.15 | 1.49 | no leak detected | 7.330 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15416.7 | 15416.7 | +1.483 | +0.0096% | -0.23 | 3.17 (crop 6) | 1.35 | 2.00 | no leak detected | 16.106 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30875.0 | 30875.0 | +4.485 | +0.0146% | -1.12 | 1.73 (crop 0) | 1.66 | 1.46 | no leak detected | 55.268 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 61750.0 | 61708.3 | +3.125 | +0.0051% | -0.11 | 2.58 (crop 22) | 2.26 | 2.41 | no leak detected | 85.840 |
| xmss_node/z=4 | SK.seed | 1 | 1495 | 1505 | 123875.0 | 123791.7 | +93.827 | +0.0754% | +0.04 | 2.09 (crop 46) | 1.27 | 1.67 | no leak detected | 135.701 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3985125.0 | 3978250.0 | +2173.971 | +0.0545% | +2.15 | 2.48 (crop 59) | 1.41 | 1.40 | no leak detected | 4708.730 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 25.1 | 25.1 | -0.000 | -0.0005% | +0.28 | 1.32 (crop 0) | 1.77 | 1.10 | no leak detected | 0.014 |
| fors_node/z=0 | SK.seed | 256 | 49853 | 50147 | 152.2 | 152.2 | -0.047 | -0.0303% | +0.30 | 1.36 (crop 30) | 1.25 | 0.96 | no leak detected | 0.100 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 222.3 | 222.3 | +0.001 | +0.0003% | -0.14 | 2.37 (crop 44) | 1.33 | 1.41 | no leak detected | 0.094 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 550.1 | 550.1 | -0.091 | -0.0165% | -0.37 | 1.97 (crop 26) | 1.45 | 1.31 | no leak detected | 0.255 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3234.4 | 3234.4 | +0.268 | +0.0083% | +0.76 | 1.65 (crop 89) | 1.05 | 1.78 | no leak detected | 3.517 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6270.8 | 6270.8 | +1.552 | +0.0248% | +1.00 | 1.70 (crop 99) | 2.10 | 1.74 | no leak detected | 7.887 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12687.5 | 12687.5 | -6.029 | -0.0477% | +0.14 | 1.97 (crop 1) | 2.12 | 1.35 | no leak detected | 17.473 |
| fors_node/z=12 | SK.seed | 1 | 1010 | 990 | 202458.3 | 202541.7 | -196.287 | -0.0969% | +0.15 | 2.25 (crop 21) | 1.71 | 1.35 | no leak detected | 239.977 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2863000.0 | 2861458.3 | -1253.078 | -0.0438% | -0.45 | 1.56 (crop 7) | 1.60 | 1.63 | no leak detected | 2761.471 |
| fors_pk_gen | SK.seed | 1 | 145 | 155 | 2834916.7 | 2833541.7 | -315.375 | -0.0111% | +0.59 | 1.46 (crop 1) | 1.66 | 2.66 | no leak detected | 2467.491 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3978583.3 | 3979166.7 | +221.790 | +0.0056% | -0.90 | 1.14 (crop 24) | 2.37 | 1.71 | no leak detected | 1584.872 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.7 | 1.0 | -91.969 | -196.6676% | -70.48 | 75.66 (crop 58) | 2.44 | 0.93 | leak detected (expected: control) | 3.008 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 128 | 10079 | 9921 | 211.9 | 211.9 | +23.807 | +11.8272% | +1.35 | 114.68 (crop 2) | 2.20 | 1.46 | leak detected (expected: control) | 0.777 |
21:50  up 2 days, 12:09, 4 users, load averages: 2.41 2.52 2.32
