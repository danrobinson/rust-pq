20:01  up 2 days, 10:21, 4 users, load averages: 1.74 1.78 1.79
slhdsa build: default; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = random-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 99951 | 100049 | 204.4 | 204.4 | -0.004 | -0.0020% | +0.32 | 1.52 (crop 37) | 1.82 | 2.37 | no leak detected | 0.061 |
| sha256/len=16 | all message bytes | 128 | 100068 | 99932 | 188.5 | 188.5 | +0.004 | +0.0023% | +0.54 | 1.66 (crop 28) | 1.40 | 1.48 | no leak detected | 0.058 |
| sha256/len=55 | all message bytes | 128 | 100065 | 99935 | 165.7 | 165.7 | +0.003 | +0.0018% | +0.05 | 1.37 (crop 16) | 2.04 | 2.17 | no leak detected | 0.058 |
| sha256/len=56 | all message bytes | 64 | 99834 | 100166 | 340.5 | 340.5 | +0.009 | +0.0026% | +0.86 | 1.92 (crop 15) | 1.68 | 1.61 | no leak detected | 0.120 |
| sha256/len=64 | all message bytes | 64 | 100273 | 99727 | 339.8 | 339.8 | +0.032 | +0.0094% | +0.67 | 3.11 (crop 21) | 1.17 | 1.16 | no leak detected | 0.125 |
| sha256/len=119 | all message bytes | 128 | 99937 | 100063 | 301.1 | 301.1 | +0.126 | +0.0408% | +0.52 | 2.70 (crop 21) | 1.59 | 1.09 | no leak detected | 0.111 |
| sha256/len=120 | all message bytes | 64 | 100162 | 99838 | 474.6 | 474.6 | +0.261 | +0.0536% | +2.27 | 3.84 (crop 23) | 2.40 | 1.53 | no leak detected | 0.177 |
| sha256/len=256 | all message bytes | 32 | 99847 | 100153 | 751.3 | 751.3 | -0.256 | -0.0329% | +0.40 | 2.38 (crop 12) | 1.76 | 1.81 | no leak detected | 0.307 |
| sha256/len=560 | all message bytes | 16 | 99792 | 100208 | 1260.4 | 1260.4 | +0.128 | +0.0098% | -0.00 | 1.75 (crop 2) | 1.00 | 1.62 | no leak detected | 0.564 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 50084 | 49916 | 787.8 | 787.8 | -0.040 | -0.0050% | -0.69 | 1.77 (crop 24) | 0.96 | 1.44 | no leak detected | 0.373 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 16 | 50028 | 49972 | 1106.8 | 1106.8 | -0.143 | -0.0128% | +0.86 | 1.79 (crop 26) | 1.72 | 1.77 | no leak detected | 0.571 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 50008 | 49992 | 954.4 | 954.4 | +0.148 | +0.0153% | -0.20 | 1.81 (crop 27) | 1.05 | 1.94 | no leak detected | 0.418 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 49843 | 50157 | 825.5 | 825.5 | -0.339 | -0.0405% | -0.91 | 2.13 (crop 26) | 1.83 | 1.93 | no leak detected | 0.387 |
| compress (copy inlined into the wrapper) | state and block | 128 | 100274 | 99726 | 136.1 | 136.1 | +0.052 | +0.0376% | +0.53 | 2.02 (crop 16) | 0.84 | 2.07 | no leak detected | 0.058 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 256 | 100170 | 99830 | 141.8 | 141.8 | -0.011 | -0.0077% | -0.25 | 2.53 (crop 20) | 1.51 | 1.88 | no leak detected | 0.052 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 256 | 100365 | 99635 | 142.3 | 142.3 | -0.002 | -0.0016% | -0.63 | 2.46 (crop 23) | 1.47 | 1.39 | no leak detected | 0.050 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 128 | 99824 | 100176 | 200.2 | 200.2 | +0.027 | +0.0132% | -1.60 | 1.60 | 1.42 | 2.19 | no leak detected | 0.064 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 128 | 100034 | 99966 | 196.0 | 196.0 | +0.070 | +0.0357% | +1.94 | 2.66 (crop 31) | 2.12 | 2.07 | no leak detected | 0.063 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 32 | 100343 | 99657 | 606.8 | 606.8 | -0.052 | -0.0084% | -0.63 | 1.87 (crop 1) | 3.26 | 2.19 | no leak detected | 0.246 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 8 | 99943 | 100057 | 1484.4 | 1484.4 | +0.636 | +0.0416% | +1.06 | 1.68 (crop 6) | 1.56 | 1.30 | no leak detected | 0.692 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 16 | 49909 | 50091 | 1377.6 | 1377.6 | -0.399 | -0.0282% | +0.43 | 1.60 (crop 19) | 0.97 | 1.54 | no leak detected | 0.841 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 50086 | 49914 | 641.9 | 641.9 | -0.098 | -0.0151% | -0.95 | 1.88 (crop 15) | 1.14 | 1.58 | no leak detected | 0.344 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 50111 | 49889 | 644.5 | 644.5 | +0.412 | +0.0628% | -0.52 | 2.37 (crop 6) | 2.50 | 1.61 | no leak detected | 0.348 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 32 | 49842 | 50158 | 781.2 | 781.2 | +0.933 | +0.1156% | +1.49 | 3.32 (crop 26) | 1.64 | 1.60 | no leak detected | 0.447 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 49969 | 50031 | 2890.6 | 2890.6 | -0.806 | -0.0271% | -0.34 | 1.78 (crop 1) | 1.47 | 1.71 | no leak detected | 1.691 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 49819 | 50181 | 2028.6 | 2028.6 | +0.050 | +0.0024% | +1.57 | 1.57 | 1.91 | 1.87 | no leak detected | 1.057 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 24932 | 25068 | 8083.3 | 8083.3 | -0.142 | -0.0018% | +0.85 | 1.47 (crop 2) | 2.05 | 1.95 | no leak detected | 5.475 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 9942 | 10058 | 70708.3 | 70708.3 | +61.973 | +0.0868% | -0.56 | 2.67 (crop 25) | 1.24 | 1.15 | no leak detected | 86.221 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 1 | 10088 | 9912 | 31166.7 | 31166.7 | +6.693 | +0.0212% | -1.79 | 2.69 (crop 1) | 2.10 | 1.60 | no leak detected | 42.690 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 25144 | 24856 | 1895.8 | 1895.8 | -0.367 | -0.0184% | -0.50 | 2.28 (crop 18) | 1.29 | 1.48 | no leak detected | 1.714 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 2 | 4987 | 5013 | 17270.8 | 17250.0 | +16.992 | +0.0933% | +1.27 | 1.93 (crop 69) | 1.89 | 1.56 | no leak detected | 35.149 |
| wots_pk_gen | SK.seed | 1 | 24780 | 25220 | 76625.0 | 76625.0 | -32.398 | -0.0419% | +0.22 | 2.10 (crop 35) | 2.09 | 2.01 | no leak detected | 56.298 |
| wots_sign | SK.seed (message m public, fixed) | 1 | 25121 | 24879 | 39375.0 | 39375.0 | +20.912 | +0.0521% | -0.35 | 2.00 (crop 20) | 1.35 | 1.02 | no leak detected | 34.426 |
| xmss_node/z=0 | SK.seed | 1 | 5039 | 4961 | 76666.7 | 76666.7 | +68.547 | +0.0885% | +0.33 | 2.08 (crop 30) | 2.15 | 0.89 | no leak detected | 128.307 |
| xmss_node/z=1 | SK.seed | 1 | 4982 | 5018 | 153458.3 | 153458.3 | +85.142 | +0.0551% | +0.66 | 2.06 (crop 41) | 2.24 | 1.91 | no leak detected | 210.421 |
| xmss_node/z=2 | SK.seed | 1 | 1547 | 1453 | 307041.7 | 307041.7 | +272.243 | +0.0876% | +0.01 | 1.73 (crop 34) | 2.54 | 2.33 | no leak detected | 885.312 |
| xmss_node/z=3 | SK.seed | 1 | 1518 | 1482 | 616000.0 | 617333.3 | -453.899 | -0.0732% | -1.10 | 2.28 (crop 43) | 1.21 | 2.49 | no leak detected | 1258.825 |
| xmss_node/z=4 | SK.seed | 1 | 1489 | 1511 | 1241166.7 | 1241458.3 | -784.138 | -0.0631% | +1.51 | 2.69 (crop 18) | 2.39 | 1.55 | no leak detected | 2834.403 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 247 | 253 | 39739541.7 | 39916958.3 | +9066.704 | +0.0226% | -0.19 | 2.77 (crop 16) | 2.08 | 2.32 | no leak detected | 94655.732 |
| fors_sk_gen | SK.seed | 256 | 99973 | 100027 | 146.2 | 146.2 | +0.002 | +0.0015% | +0.60 | 2.24 (crop 23) | 1.21 | 1.44 | no leak detected | 0.050 |
| fors_node/z=0 | SK.seed | 64 | 49853 | 50147 | 370.4 | 370.4 | -0.031 | -0.0081% | -0.28 | 2.02 (crop 11) | 0.72 | 0.87 | no leak detected | 0.221 |
| fors_node/z=1 | SK.seed | 32 | 49730 | 50270 | 786.5 | 786.5 | +0.148 | +0.0186% | +1.46 | 1.79 (crop 85) | 1.52 | 1.45 | no leak detected | 0.438 |
| fors_node/z=3 | SK.seed | 8 | 14992 | 15008 | 3250.0 | 3250.0 | -1.055 | -0.0320% | +2.09 | 2.17 (crop 92) | 2.05 | 2.09 | no leak detected | 3.379 |
| fors_node/z=6 | SK.seed | 1 | 2554 | 2446 | 26083.3 | 26041.7 | -9.647 | -0.0364% | +0.04 | 1.27 (crop 25) | 1.23 | 1.90 | no leak detected | 81.859 |
| fors_node/z=7 | SK.seed | 1 | 2515 | 2485 | 52083.3 | 52083.3 | -14.913 | -0.0286% | -0.07 | 3.02 (crop 23) | 2.02 | 1.81 | no leak detected | 102.787 |
| fors_node/z=8 | SK.seed | 1 | 2464 | 2536 | 104458.3 | 104416.7 | +195.880 | +0.1811% | +0.51 | 1.67 (crop 20) | 1.37 | 1.82 | no leak detected | 262.284 |
| fors_node/z=12 | SK.seed | 1 | 1014 | 986 | 1692166.7 | 1692500.0 | +5205.961 | +0.3003% | +1.41 | 1.77 (crop 48) | 2.05 | 1.55 | no leak detected | 5783.245 |
| fors_sign | SK.seed (md public, fixed) | 1 | 151 | 149 | 24760708.3 | 24308083.3 | +133672.792 | +0.5464% | +1.10 | 2.17 (crop 39) | 1.68 | 1.62 | no leak detected | 122119.388 |
| fors_pk_gen | SK.seed | 1 | 147 | 153 | 24051375.0 | 24198958.3 | +805.308 | +0.0033% | -0.07 | 2.58 (crop 9) | 2.58 | 1.94 | no leak detected | 110045.541 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 506 | 494 | 39711750.0 | 39694125.0 | +52899.648 | +0.1326% | +0.83 | 1.79 (crop 10) | 1.72 | 1.26 | no leak detected | 55904.521 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 1.4 | 1.0 | +3.191 | +2.4013% | -0.44 | 2.79 (crop 5) | 2.30 | 2.36 | no leak detected | 4.148 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 10079 | 9921 | 675.8 | 675.8 | +4.006 | +0.6228% | +0.95 | 2.62 (crop 14) | 1.39 | 0.95 | no leak detected | 3.498 |
20:06  up 2 days, 10:26, 4 users, load averages: 1.40 1.60 1.70
