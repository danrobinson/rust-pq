20:06  up 2 days, 10:26, 4 users, load averages: 1.40 1.60 1.70
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 205.1 | 205.1 | -0.097 | -0.0476% | -2.46 | 12.74 (crop 28) | 1.34 | 1.75 | **t > 4.5** | 0.055 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 189.5 | 189.5 | -0.009 | -0.0049% | -0.35 | 1.99 (crop 27) | 1.38 | 1.82 | no leak detected | 0.057 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 167.0 | 167.0 | -0.038 | -0.0225% | -1.02 | 5.93 (crop 26) | 1.78 | 1.45 | **t > 4.5** | 0.056 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 340.5 | 341.1 | +0.002 | +0.0005% | +1.22 | 5.91 (crop 16) | 1.32 | 1.40 | **t > 4.5** | 0.124 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 339.8 | 339.8 | -0.003 | -0.0008% | -1.90 | 2.51 (crop 15) | 1.10 | 1.30 | no leak detected | 0.129 |
| sha256/len=119 | all message bytes | 128 | 99937 | 100063 | 300.8 | 300.8 | +0.136 | +0.0438% | -0.87 | 5.36 (crop 9) | 1.30 | 2.63 | **t > 4.5** | 0.113 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 474.6 | 474.6 | -0.106 | -0.0218% | +0.40 | 2.68 (crop 13) | 2.13 | 1.63 | no leak detected | 0.177 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 751.3 | 751.3 | +0.190 | +0.0247% | +1.47 | 2.01 (crop 9) | 1.21 | 1.85 | no leak detected | 0.293 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1260.4 | 1260.4 | +0.189 | +0.0145% | +0.46 | 1.26 (crop 4) | 1.80 | 1.88 | no leak detected | 0.551 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 789.1 | 787.8 | +0.321 | +0.0403% | +1.78 | 3.12 (crop 43) | 1.32 | 1.92 | no leak detected | 0.367 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 50028 | 49972 | 1104.2 | 1104.2 | +0.101 | +0.0090% | -0.27 | 2.21 (crop 18) | 1.39 | 1.77 | no leak detected | 0.493 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 955.7 | 955.7 | -0.012 | -0.0013% | +0.22 | 1.38 (crop 27) | 1.13 | 1.46 | no leak detected | 0.430 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 824.2 | 824.2 | +0.005 | +0.0007% | -0.11 | 1.21 (crop 1) | 1.25 | 1.12 | no leak detected | 0.381 |
| compress (copy inlined into the wrapper) | state and block | 256 | 100274 | 99726 | 135.9 | 136.1 | +0.338 | +0.2455% | -7.25 | 129.64 (crop 7) | 1.75 | 1.88 | **t > 4.5** | 0.047 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 100170 | 99830 | 141.6 | 141.6 | -0.007 | -0.0048% | +1.73 | 2.79 (crop 27) | 0.99 | 1.67 | no leak detected | 0.044 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 100365 | 99635 | 142.4 | 142.3 | -0.193 | -0.1334% | +0.90 | 22.16 (crop 18) | 1.60 | 1.80 | **t > 4.5** | 0.048 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 202.5 | 202.5 | +0.017 | +0.0081% | -3.05 | 5.49 (crop 23) | 2.80 | 0.94 | **t > 4.5** | 0.064 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 198.2 | 198.2 | -0.047 | -0.0235% | -2.49 | 4.45 (crop 15) | 1.85 | 2.37 | no leak detected | 0.061 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 64 | 100343 | 99657 | 607.4 | 607.4 | +0.101 | +0.0165% | -0.29 | 1.13 (crop 3) | 1.25 | 1.66 | no leak detected | 0.198 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 16 | 99943 | 100057 | 1479.2 | 1479.2 | -0.209 | -0.0138% | +0.60 | 1.36 (crop 0) | 1.15 | 2.29 | no leak detected | 0.576 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1369.8 | 1369.8 | +0.224 | +0.0161% | -1.23 | 2.70 (crop 16) | 1.64 | 2.05 | no leak detected | 0.748 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 639.3 | 639.3 | +0.277 | +0.0429% | +0.68 | 2.07 (crop 31) | 0.95 | 1.58 | no leak detected | 0.315 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 644.5 | 644.5 | +0.002 | +0.0003% | -1.33 | 2.79 (crop 24) | 1.65 | 1.02 | no leak detected | 0.317 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 778.6 | 778.6 | +0.708 | +0.0891% | +1.30 | 2.99 (crop 41) | 1.51 | 1.02 | no leak detected | 0.401 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 2880.2 | 2885.4 | -1.500 | -0.0504% | -1.37 | 2.07 (crop 2) | 1.29 | 1.66 | no leak detected | 1.745 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 49819 | 50181 | 2026.0 | 2031.2 | -2.423 | -0.1193% | -2.99 | 57.71 (crop 16) | 0.99 | 2.33 | **t > 4.5** | 1.117 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 24932 | 25068 | 8083.3 | 8083.3 | +0.615 | +0.0076% | +0.28 | 1.99 (crop 33) | 1.15 | 1.64 | no leak detected | 6.727 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 70708.3 | 70666.7 | +4.135 | +0.0058% | -1.75 | 3.60 (crop 23) | 1.29 | 2.30 | no leak detected | 61.146 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 31166.7 | 31166.7 | +10.458 | +0.0334% | -0.70 | 5.80 (crop 28) | 1.50 | 2.12 | **t > 4.5** | 36.805 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 1895.8 | 1898.4 | -1.308 | -0.0656% | -1.73 | 2.05 (crop 86) | 1.11 | 2.13 | no leak detected | 1.687 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 4987 | 5013 | 17291.7 | 17250.0 | -17.962 | -0.0987% | +0.72 | 6.10 (crop 11) | 1.42 | 2.60 | **t > 4.5** | 33.724 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 76625.0 | 76625.0 | +0.752 | +0.0010% | +0.92 | 1.72 (crop 41) | 1.52 | 1.28 | no leak detected | 41.256 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 39375.0 | 39375.0 | +2.097 | +0.0053% | -1.01 | 1.24 (crop 16) | 2.51 | 3.44 | no leak detected | 26.671 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 76625.0 | 76625.0 | +11.526 | +0.0150% | +0.59 | 2.54 (crop 38) | 2.44 | 1.47 | no leak detected | 87.238 |
| xmss_node/z=1 | SK.seed | 1 | 4985 | 5015 | 153458.3 | 153458.3 | +17.908 | +0.0116% | -1.17 | 1.89 (crop 6) | 1.96 | 1.74 | no leak detected | 216.861 |
| xmss_node/z=2 | SK.seed | 1 | 1552 | 1448 | 306958.3 | 307000.0 | -508.157 | -0.1644% | -1.86 | 2.71 (crop 33) | 2.02 | 2.48 | no leak detected | 699.938 |
| xmss_node/z=3 | SK.seed | 1 | 1518 | 1482 | 616958.3 | 617208.3 | -2.667 | -0.0004% | +0.65 | 1.91 (crop 11) | 2.40 | 1.96 | no leak detected | 1056.523 |
| xmss_node/z=4 | SK.seed | 1 | 1493 | 1507 | 1238958.3 | 1238291.7 | -125.394 | -0.0101% | -0.07 | 1.10 (crop 2) | 1.60 | 2.18 | no leak detected | 2113.485 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 39727250.0 | 39720250.0 | +23082.780 | +0.0578% | +0.07 | 1.70 (crop 2) | 2.17 | 1.86 | no leak detected | 89273.715 |
| fors_sk_gen | SK.seed | 128 | 99973 | 100027 | 146.5 | 146.5 | -0.046 | -0.0309% | -0.87 | 1.38 (crop 57) | 1.27 | 1.82 | no leak detected | 0.060 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 372.4 | 371.7 | -0.006 | -0.0016% | +0.61 | 5.56 (crop 23) | 0.88 | 1.12 | **t > 4.5** | 0.205 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 787.8 | 787.8 | -0.167 | -0.0210% | -1.57 | 2.13 (crop 47) | 1.96 | 1.61 | no leak detected | 0.393 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3250.0 | 3250.0 | +0.663 | +0.0201% | +0.30 | 1.64 (crop 2) | 2.31 | 1.09 | no leak detected | 3.319 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 26166.7 | 26166.7 | -14.345 | -0.0526% | -0.56 | 1.87 (crop 3) | 1.11 | 2.08 | no leak detected | 73.814 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 52166.7 | 52166.7 | -1.913 | -0.0036% | -1.36 | 1.61 (crop 91) | 2.09 | 2.24 | no leak detected | 119.903 |
| fors_node/z=8 | SK.seed | 1 | 2465 | 2535 | 104416.7 | 104416.7 | +237.272 | +0.2181% | +1.27 | 1.81 (crop 16) | 2.57 | 2.31 | no leak detected | 268.583 |
| fors_node/z=12 | SK.seed | 1 | 1014 | 986 | 1698958.3 | 1700500.0 | +4271.822 | +0.2413% | +0.48 | 1.89 (crop 2) | 2.15 | 1.99 | no leak detected | 6513.608 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 24735458.3 | 24693458.3 | +19886.752 | +0.0810% | -0.27 | 3.11 (crop 3) | 2.31 | 1.70 | no leak detected | 127849.752 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 39771791.7 | 39809250.0 | -13944.640 | -0.0347% | -1.63 | 2.77 (crop 12) | 1.81 | 1.75 | no leak detected | 63626.152 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.9 | 1.1 | -90.169 | -196.4072% | -70.44 | 75.64 (crop 58) | 2.45 | 1.53 | leak detected (expected: control) | 2.954 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 679.7 | 679.7 | +81.294 | +12.5474% | +1.32 | 115.60 (crop 2) | 1.33 | 2.09 | leak detected (expected: control) | 2.543 |
20:11  up 2 days, 10:30, 4 users, load averages: 1.85 1.70 1.70
