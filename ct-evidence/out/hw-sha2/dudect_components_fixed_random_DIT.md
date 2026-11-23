21:24  up 2 days, 11:43, 4 users, load averages: 1.39 1.60 1.72
slhdsa build: hw-sha2; clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 1; classes = fixed-random; fixed class = one fixed pseudo-random secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 | std err of mean diff, uncropped (ns) |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 256 | 99951 | 100049 | 108.6 | 108.6 | +0.000 | +0.0002% | +0.88 | 1.95 (crop 89) | 0.80 | 1.11 | no leak detected | 0.027 |
| sha256/len=16 | all message bytes | 256 | 100068 | 99932 | 88.5 | 88.5 | +0.000 | +0.0002% | -0.06 | 1.79 (crop 40) | 1.89 | 1.40 | no leak detected | 0.026 |
| sha256/len=55 | all message bytes | 256 | 100065 | 99935 | 63.0 | 63.0 | -0.005 | -0.0084% | -0.72 | 2.64 (crop 30) | 1.70 | 2.24 | no leak detected | 0.019 |
| sha256/len=56 | all message bytes | 256 | 99834 | 100166 | 118.0 | 118.0 | +0.001 | +0.0008% | -0.48 | 3.24 (crop 1) | 1.70 | 1.21 | no leak detected | 0.028 |
| sha256/len=64 | all message bytes | 256 | 100273 | 99727 | 112.6 | 112.6 | +0.001 | +0.0008% | +0.51 | 2.21 (crop 1) | 1.58 | 3.00 | no leak detected | 0.028 |
| sha256/len=119 | all message bytes | 512 | 99937 | 100063 | 75.0 | 75.0 | +0.001 | +0.0010% | -2.01 | 2.34 (crop 99) | 1.76 | 1.80 | no leak detected | 0.017 |
| sha256/len=120 | all message bytes | 256 | 100162 | 99838 | 138.0 | 138.0 | +0.000 | +0.0001% | -0.53 | 2.23 (crop 1) | 2.36 | 1.92 | no leak detected | 0.031 |
| sha256/len=256 | all message bytes | 128 | 99847 | 100153 | 170.9 | 170.9 | -0.003 | -0.0018% | +0.13 | 2.18 (crop 73) | 1.84 | 1.77 | no leak detected | 0.048 |
| sha256/len=560 | all message bytes | 128 | 99792 | 100208 | 212.2 | 212.2 | -0.000 | -0.0001% | -0.07 | 1.52 (crop 8) | 2.73 | 1.39 | no leak detected | 0.051 |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 64 | 50084 | 49916 | 413.4 | 413.4 | -0.002 | -0.0005% | +1.87 | 2.09 (crop 51) | 1.38 | 1.64 | no leak detected | 0.155 |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 64 | 50028 | 49972 | 470.7 | 470.7 | +0.012 | +0.0025% | +1.12 | 1.69 (crop 87) | 1.90 | 1.70 | no leak detected | 0.170 |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 64 | 50008 | 49992 | 462.9 | 462.9 | +0.005 | +0.0010% | -0.62 | 3.60 (crop 2) | 1.49 | 2.09 | no leak detected | 0.153 |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 64 | 49843 | 50157 | 444.0 | 444.0 | +0.026 | +0.0059% | +1.72 | 2.52 (crop 96) | 1.78 | 1.80 | no leak detected | 0.154 |
| compress (copy inlined into the wrapper) | state and block | 2048 | 100274 | 99726 | 17.2 | 17.2 | +0.000 | +0.0006% | +1.59 | 1.89 (crop 93) | 1.32 | 1.60 | no leak detected | 0.004 |
| thash_short/len=16 | m (SK.seed / chain value / node values) | 1024 | 100170 | 99830 | 37.4 | 37.4 | +0.001 | +0.0020% | +0.38 | 2.98 (crop 42) | 3.31 | 3.03 | no leak detected | 0.008 |
| thash_short/len=32 | m (SK.seed / chain value / node values) | 1024 | 100365 | 99635 | 36.5 | 36.5 | +0.002 | +0.0045% | +0.89 | 1.59 (crop 8) | 1.03 | 1.83 | no leak detected | 0.010 |
| thash/len=16 | m (len=224: the 14 FORS roots) | 256 | 99824 | 100176 | 96.8 | 96.8 | +0.002 | +0.0022% | +0.47 | 1.71 (crop 14) | 1.29 | 0.92 | no leak detected | 0.027 |
| thash/len=32 | m (len=224: the 14 FORS roots) | 256 | 100034 | 99966 | 94.9 | 94.9 | -0.000 | -0.0005% | +1.15 | 1.96 (crop 67) | 2.23 | 1.68 | no leak detected | 0.024 |
| thash/len=224 | m (len=224: the 14 FORS roots) | 128 | 100343 | 99657 | 168.0 | 168.0 | -0.004 | -0.0025% | -0.02 | 2.51 (crop 19) | 1.75 | 1.31 | no leak detected | 0.048 |
| thash/len=560 | m (len=224: the 14 FORS roots) | 64 | 99943 | 100057 | 336.6 | 336.6 | -0.012 | -0.0036% | +0.28 | 1.45 (crop 29) | 1.33 | 2.54 | no leak detected | 0.092 |
| thash_values | all 35 blocks (the values are the WOTS+ chain ends) | 128 | 49909 | 50091 | 204.8 | 204.8 | +0.004 | +0.0017% | +1.95 | 2.13 (crop 99) | 2.05 | 2.01 | no leak detected | 0.071 |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 128 | 50086 | 49914 | 184.2 | 184.2 | +0.013 | +0.0070% | +0.29 | 3.29 (crop 0) | 1.85 | 1.73 | no leak detected | 0.072 |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 128 | 50111 | 49889 | 195.6 | 195.6 | -0.004 | -0.0023% | -0.99 | 2.44 (crop 55) | 1.97 | 1.22 | no leak detected | 0.075 |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 128 | 49842 | 50158 | 217.8 | 217.8 | -0.001 | -0.0005% | -0.01 | 1.54 (crop 0) | 2.59 | 2.35 | no leak detected | 0.075 |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 64 | 49969 | 50031 | 587.9 | 587.9 | -0.013 | -0.0023% | -1.38 | 2.29 (crop 42) | 1.83 | 1.99 | no leak detected | 0.185 |
| chain_blocks/n=1,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 49819 | 50181 | 308.3 | 308.3 | -0.005 | -0.0017% | -0.30 | 1.63 (crop 6) | 1.99 | 2.29 | no leak detected | 0.101 |
| chain_blocks/n=4,steps=0..15 | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 32 | 24932 | 25068 | 800.8 | 800.8 | +0.044 | +0.0055% | +2.15 | 2.15 | 1.22 | 1.82 | no leak detected | 0.438 |
| chain_blocks/n=35,steps=0..15 (wots_pk_gen) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 4 | 9942 | 10058 | 6802.1 | 6802.1 | +2.052 | +0.0302% | +0.50 | 2.63 (crop 29) | 2.26 | 1.49 | no leak detected | 4.976 |
| chain_blocks/n=35,steps=0..d_i (wots_sign) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 8 | 10088 | 9912 | 3099.0 | 3099.0 | +1.811 | +0.0585% | +0.32 | 5.91 (crop 32) | 1.33 | 1.60 | **t > 4.5** | 2.397 |
| chain_blocks/n=14,steps=t_i..t_i+1 (FORS paths) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 128 | 25144 | 24856 | 221.0 | 221.0 | +0.003 | +0.0012% | +1.32 | 2.39 (crop 43) | 1.53 | 1.52 | no leak detected | 0.106 |
| chain_blocks/n=128,steps=t_i..t_i+1 (FORS batch) | bytes 16..64 of every block (the step ranges and the 16-byte prefixes are public and fixed) | 16 | 4987 | 5013 | 1791.7 | 1789.1 | +1.445 | +0.0808% | +2.04 | 6.02 (crop 42) | 1.58 | 2.36 | **t > 4.5** | 1.813 |
| wots_pk_gen | SK.seed | 4 | 24780 | 25220 | 7572.9 | 7572.9 | +0.287 | +0.0038% | -0.28 | 1.28 (crop 49) | 1.62 | 2.34 | no leak detected | 3.451 |
| wots_sign | SK.seed (message m public, fixed) | 8 | 25121 | 24879 | 4239.6 | 4239.6 | -0.318 | -0.0075% | -1.02 | 1.89 (crop 61) | 2.05 | 2.13 | no leak detected | 2.008 |
| xmss_node/z=0 | SK.seed | 4 | 5039 | 4961 | 7572.9 | 7572.9 | -0.829 | -0.0110% | -0.49 | 2.34 (crop 11) | 1.62 | 2.18 | no leak detected | 8.814 |
| xmss_node/z=1 | SK.seed | 2 | 4982 | 5018 | 15187.5 | 15187.5 | -1.902 | -0.0125% | -2.09 | 3.51 (crop 91) | 1.19 | 2.12 | no leak detected | 16.984 |
| xmss_node/z=2 | SK.seed | 1 | 1543 | 1457 | 30416.7 | 30416.7 | -2.708 | -0.0089% | -1.23 | 1.45 (crop 19) | 1.51 | 1.39 | no leak detected | 60.836 |
| xmss_node/z=3 | SK.seed | 1 | 1535 | 1465 | 60875.0 | 60875.0 | -7.950 | -0.0131% | -1.16 | 2.23 (crop 58) | 1.87 | 1.89 | no leak detected | 92.458 |
| xmss_node/z=4 | SK.seed | 1 | 1495 | 1505 | 121750.0 | 121750.0 | -3.836 | -0.0031% | +1.26 | 1.41 (crop 79) | 2.07 | 1.82 | no leak detected | 154.307 |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 245 | 255 | 3926541.7 | 3929500.0 | -2582.687 | -0.0658% | -1.08 | 1.98 (crop 13) | 2.13 | 2.35 | no leak detected | 2629.112 |
| fors_sk_gen | SK.seed | 1024 | 99973 | 100027 | 36.6 | 36.6 | -0.001 | -0.0022% | -0.83 | 2.39 (crop 41) | 2.40 | 1.55 | no leak detected | 0.008 |
| fors_node/z=0 | SK.seed | 256 | 49853 | 50147 | 149.7 | 149.7 | -0.001 | -0.0009% | -0.38 | 1.96 (crop 53) | 1.00 | 1.23 | no leak detected | 0.077 |
| fors_node/z=1 | SK.seed | 128 | 49730 | 50270 | 224.3 | 224.0 | -0.018 | -0.0081% | -0.23 | 2.07 (crop 11) | 0.70 | 1.98 | no leak detected | 0.106 |
| fors_node/z=3 | SK.seed | 64 | 14992 | 15008 | 539.1 | 539.1 | +0.094 | +0.0174% | -0.77 | 2.34 (crop 42) | 2.66 | 1.34 | no leak detected | 0.305 |
| fors_node/z=6 | SK.seed | 8 | 2554 | 2446 | 3187.5 | 3182.3 | +1.938 | +0.0609% | +1.75 | 3.17 (crop 37) | 1.20 | 2.31 | no leak detected | 4.799 |
| fors_node/z=7 | SK.seed | 4 | 2515 | 2485 | 6135.4 | 6135.4 | -1.233 | -0.0201% | -0.27 | 1.74 (crop 63) | 0.98 | 1.51 | no leak detected | 8.993 |
| fors_node/z=8 | SK.seed | 2 | 2465 | 2535 | 12375.0 | 12375.0 | -2.790 | -0.0225% | +0.10 | 1.84 (crop 16) | 2.05 | 1.65 | no leak detected | 20.303 |
| fors_node/z=12 | SK.seed | 1 | 1010 | 990 | 198750.0 | 198750.0 | -77.236 | -0.0388% | +0.60 | 2.01 (crop 44) | 2.00 | 1.86 | no leak detected | 232.706 |
| fors_sign | SK.seed (md public, fixed) | 1 | 152 | 148 | 2805958.3 | 2802000.0 | +1059.021 | +0.0378% | +1.08 | 3.07 (crop 2) | 3.38 | 2.07 | no leak detected | 2709.098 |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 509 | 491 | 3931500.0 | 3930791.7 | +1494.354 | +0.0380% | +0.32 | 1.18 (crop 32) | 1.88 | 1.14 | no leak detected | 1907.973 |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 16384 | 9933 | 10067 | 0.9 | 1.0 | -130.752 | -197.4585% | -70.36 | 75.17 (crop 58) | 2.44 | 1.84 | leak detected (expected: control) | 4.328 |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 64 | 10079 | 9921 | 272.8 | 272.8 | +32.170 | +12.4607% | +1.31 | 119.40 (crop 2) | 1.40 | 1.63 | leak detected (expected: control) | 1.008 |
21:28  up 2 days, 11:47, 4 users, load averages: 1.36 1.50 1.65
