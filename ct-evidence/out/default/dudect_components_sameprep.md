21:33  up 2 days, 11:52, 4 users, load averages: 2.44 1.84 1.73
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519; both classes prepared by the same code path

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 210.3 | 210.3 | -0.091 | -0.0431% | -2.42 | 12.92 (crop 10) | 2.40 | 1.49 | **t > 4.5** | 0.052 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 194.3 | 194.3 | -0.010 | -0.0049% | +0.12 | 1.74 (crop 1) | 1.19 | 2.21 | no leak detected | 0.047 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 170.2 | 170.2 | +0.009 | +0.0050% | +0.49 | 7.32 (crop 5) | 1.78 | 1.04 | **t > 4.5** | 0.053 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 348.3 | 348.3 | +0.089 | +0.0251% | -0.78 | 3.31 (crop 16) | 1.41 | 1.51 | no leak detected | 0.109 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 348.3 | 348.3 | +0.118 | +0.0334% | +0.92 | 2.28 (crop 35) | 1.13 | 1.12 | no leak detected | 0.112 |
| sha256/len=119 | all message bytes | 64 | 99937 | 100063 | 307.9 | 307.9 | -0.062 | -0.0197% | -1.16 | 1.34 (crop 10) | 0.88 | 1.79 | no leak detected | 0.112 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 485.7 | 485.7 | -0.141 | -0.0286% | -2.77 | 3.53 (crop 23) | 2.03 | 1.21 | no leak detected | 0.150 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 769.5 | 769.5 | -0.105 | -0.0134% | -0.62 | 2.29 (crop 22) | 1.30 | 1.33 | no leak detected | 0.263 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1289.1 | 1289.1 | +0.387 | +0.0290% | +0.59 | 1.37 (crop 2) | 1.17 | 1.29 | no leak detected | 0.522 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 808.6 | 808.6 | +0.034 | +0.0042% | +0.05 | 2.41 (crop 0) | 1.26 | 1.12 | no leak detected | 0.339 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 32 | 50028 | 49972 | 1130.2 | 1130.2 | +0.169 | +0.0149% | +0.57 | 1.73 (crop 48) | 1.05 | 0.90 | no leak detected | 0.399 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 979.2 | 979.2 | +0.046 | +0.0046% | -0.43 | 1.09 (crop 5) | 1.26 | 1.12 | no leak detected | 0.378 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 845.1 | 845.1 | +0.035 | +0.0040% | -1.02 | 2.02 (crop 2) | 1.61 | 2.12 | no leak detected | 0.341 |
| compress (copy inlined into the wrapper) | state and block | 256 | 100274 | 99726 | 139.0 | 139.0 | +0.072 | +0.0514% | -3.34 | 67.86 (crop 11) | 1.60 | 1.87 | **t > 4.5** | 0.045 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 128 | 100170 | 99830 | 145.2 | 145.2 | -0.016 | -0.0106% | -0.15 | 1.90 (crop 24) | 1.54 | 0.98 | no leak detected | 0.051 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 100365 | 99635 | 145.0 | 145.0 | -0.036 | -0.0246% | -0.93 | 16.56 (crop 20) | 1.72 | 3.35 | **t > 4.5** | 0.047 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 204.1 | 204.1 | -0.035 | -0.0173% | -1.36 | 7.69 (crop 25) | 1.53 | 1.81 | **t > 4.5** | 0.053 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 201.2 | 201.2 | -0.013 | -0.0065% | -0.29 | 13.25 (crop 17) | 1.61 | 1.30 | **t > 4.5** | 0.056 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 32 | 100343 | 99657 | 623.7 | 623.7 | -0.002 | -0.0003% | -0.75 | 1.66 (crop 0) | 2.08 | 1.54 | no leak detected | 0.240 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 8 | 99943 | 100057 | 1515.6 | 1515.6 | +0.369 | +0.0236% | +0.63 | 1.53 (crop 19) | 2.37 | 1.40 | no leak detected | 0.648 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1403.6 | 1403.6 | +0.043 | +0.0030% | -0.42 | 1.96 (crop 3) | 1.19 | 2.81 | no leak detected | 0.750 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 653.6 | 653.6 | -0.145 | -0.0218% | -1.05 | 2.41 (crop 8) | 1.20 | 1.87 | no leak detected | 0.309 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 656.2 | 656.2 | -0.084 | -0.0125% | -0.21 | 1.56 (crop 23) | 1.02 | 0.84 | no leak detected | 0.338 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 796.9 | 796.9 | +0.198 | +0.0242% | +2.01 | 2.21 (crop 3) | 1.68 | 2.00 | no leak detected | 0.394 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 2937.5 | 2937.5 | +1.262 | +0.0420% | +0.00 | 2.42 (crop 22) | 2.62 | 1.21 | no leak detected | 1.513 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 49819 | 50181 | 2072.9 | 2078.1 | -3.200 | -0.1535% | -2.80 | 65.15 (crop 11) | 1.50 | 1.12 | **t > 4.5** | 1.199 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 24932 | 25068 | 8250.0 | 8250.0 | -1.043 | -0.0126% | +0.40 | 2.01 (crop 10) | 1.22 | 2.74 | no leak detected | 5.726 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 72166.7 | 72166.7 | +18.027 | +0.0249% | +0.19 | 3.68 (crop 43) | 0.96 | 2.22 | no leak detected | 51.229 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 31916.7 | 31916.7 | +2.830 | +0.0087% | +0.90 | 2.70 (crop 5) | 2.05 | 1.58 | no leak detected | 36.509 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 1929.7 | 1929.7 | +0.601 | +0.0303% | +0.01 | 1.65 (crop 1) | 1.62 | 1.00 | no leak detected | 1.399 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 4987 | 5013 | 17541.7 | 17541.7 | -41.721 | -0.2333% | -2.09 | 2.69 (crop 68) | 1.41 | 1.29 | no leak detected | 25.986 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 78250.0 | 78250.0 | +1.626 | +0.0021% | +0.31 | 2.23 (crop 1) | 1.25 | 1.39 | no leak detected | 54.845 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 40208.3 | 40208.3 | -3.107 | -0.0077% | +1.69 | 2.60 (crop 0) | 1.51 | 2.30 | no leak detected | 28.678 |
| xmss_node/z=0 | SK.seed | 1 | 5038 | 4962 | 78250.0 | 78250.0 | -89.482 | -0.1128% | -2.60 | 2.69 (crop 76) | 1.69 | 1.17 | no leak detected | 127.320 |
| xmss_node/z=1 | SK.seed | 1 | 4982 | 5018 | 156541.7 | 156541.7 | +30.269 | +0.0192% | +0.45 | 2.50 (crop 2) | 2.21 | 1.72 | no leak detected | 205.545 |
| xmss_node/z=2 | SK.seed | 1 | 1555 | 1445 | 313375.0 | 313375.0 | -251.866 | -0.0798% | -0.49 | 2.71 (crop 16) | 1.75 | 1.18 | no leak detected | 751.077 |
| xmss_node/z=3 | SK.seed | 1 | 1514 | 1486 | 628458.3 | 627250.0 | +388.441 | +0.0615% | -0.13 | 2.21 (crop 19) | 1.48 | 1.87 | no leak detected | 1610.741 |
| xmss_node/z=4 | SK.seed | 1 | 1493 | 1507 | 1263791.7 | 1262458.3 | +427.740 | +0.0338% | +0.40 | 2.85 (crop 44) | 1.60 | 1.92 | no leak detected | 2834.551 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 40501041.7 | 40503583.3 | +4151.592 | +0.0102% | +0.00 | 2.31 (crop 19) | 2.63 | 1.65 | no leak detected | 115788.952 |
| fors_sk_gen | SK.seed | 256 | 99973 | 100027 | 148.4 | 148.4 | +0.015 | +0.0102% | +0.51 | 2.28 (crop 17) | 1.26 | 1.32 | no leak detected | 0.048 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 373.7 | 373.7 | -0.091 | -0.0239% | -0.45 | 6.16 (crop 4) | 1.03 | 1.23 | **t > 4.5** | 0.185 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 798.2 | 798.2 | -0.273 | -0.0338% | -0.88 | 2.12 (crop 20) | 1.18 | 1.18 | no leak detected | 0.416 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3312.5 | 3312.5 | -4.998 | -0.1477% | -2.31 | 3.14 (crop 66) | 2.06 | 2.17 | no leak detected | 3.389 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 26666.7 | 26666.7 | -94.218 | -0.3409% | -1.17 | 2.24 (crop 21) | 3.06 | 1.06 | no leak detected | 71.477 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 53250.0 | 53250.0 | +81.331 | +0.1466% | +1.63 | 1.71 (crop 56) | 2.06 | 1.37 | no leak detected | 142.530 |
| fors_node/z=8 | SK.seed | 1 | 2467 | 2533 | 106708.3 | 106708.3 | -143.698 | -0.1313% | -0.77 | 1.92 (crop 2) | 2.06 | 1.52 | no leak detected | 241.021 |
| fors_node/z=12 | SK.seed | 1 | 1013 | 987 | 1724625.0 | 1725541.7 | -8222.146 | -0.4632% | -1.45 | 2.80 (crop 22) | 1.56 | 1.68 | no leak detected | 6161.799 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 25295708.3 | 24973166.7 | +78881.581 | +0.3147% | -0.24 | 1.84 (crop 5) | 2.33 | 2.14 | no leak detected | 145836.026 |
| fors_pk_gen | SK.seed | 1 | 147 | 153 | 25376291.7 | 24890208.3 | +264971.301 | +1.0559% | +0.63 | 2.36 (crop 16) | 2.51 | 2.75 | no leak detected | 150919.226 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 40535708.3 | 40523041.7 | +28323.817 | +0.0693% | +1.58 | 1.83 (crop 89) | 2.48 | 1.47 | no leak detected | 87675.045 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.9 | 1.0 | -92.011 | -196.5025% | -70.51 | 75.68 (crop 58) | 2.54 | 1.50 | leak detected (expected: control) | 3.006 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 692.7 | 692.7 | +83.356 | +12.6668% | +1.44 | 118.63 (crop 2) | 1.36 | 2.06 | leak detected (expected: control) | 2.550 |
21:37  up 2 days, 11:57, 4 users, load averages: 2.58 2.33 1.97
