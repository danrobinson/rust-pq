clock: mach_absolute_time, 41.667 ns/tick, observed granularity 41.7 ns; PSTATE.DIT = 0; classes = fixed-random; fixed class = all-zero secret; seed 13688519

| function (public params) | secret varied | calls per measurement | n class 0 | n class 1 | median class 0 (ns) | median class 1 (ns) | mean(class 0) - mean(class 1), 10%-trimmed (ns) | relative | t (uncropped) | max abs t (101 tests) | null max abs t (within class 1) | null max abs t (within class 0) | verdict at 4.5 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| sha256/len=1 | all message bytes | 128 | 199749 | 200251 | 206.4 | 206.7 | -0.122 | -0.0584% | -3.70 | 12.86 (crop 13) | 1.00 | 1.20 | **t > 4.5** |
| sha256/len=16 | all message bytes | 128 | 199758 | 200242 | 186.5 | 186.8 | -0.063 | -0.0333% | -1.23 | 25.56 (crop 12) | 1.44 | 1.55 | **t > 4.5** |
| sha256/len=55 | all message bytes | 128 | 200278 | 199722 | 163.1 | 163.4 | -0.211 | -0.1288% | -4.97 | 47.16 (crop 4) | 1.78 | 1.68 | **t > 4.5** |
| sha256/len=56 | all message bytes | 64 | 199812 | 200188 | 332.0 | 332.0 | -0.114 | -0.0338% | -1.14 | 38.14 (crop 10) | 1.72 | 1.01 | **t > 4.5** |
| sha256/len=64 | all message bytes | 64 | 200507 | 199493 | 308.6 | 308.6 | -0.161 | -0.0522% | -2.89 | 25.14 (crop 24) | 2.10 | 1.09 | **t > 4.5** |
| sha256/len=119 | all message bytes | 64 | 200222 | 199778 | 297.5 | 297.5 | -0.018 | -0.0060% | -0.56 | 20.95 (crop 20) | 0.97 | 1.34 | **t > 4.5** |
| sha256/len=120 | all message bytes | 64 | 200086 | 199914 | 451.2 | 451.8 | -0.209 | -0.0459% | -4.46 | 55.21 (crop 7) | 1.73 | 1.39 | **t > 4.5** |
| sha256/len=256 | all message bytes | 32 | 199720 | 200280 | 764.3 | 765.6 | -0.521 | -0.0675% | -2.60 | 24.23 (crop 6) | 1.38 | 1.62 | **t > 4.5** |
| sha256/len=560 | all message bytes | 16 | 199738 | 200262 | 1341.1 | 1341.1 | -0.465 | -0.0347% | -3.53 | 20.68 (crop 3) | 0.96 | 0.93 | **t > 4.5** |
| hmac_sha256/klen=16,mlen=32 | key and message bytes | 32 | 100037 | 99963 | 859.4 | 859.4 | +0.134 | +0.0154% | +1.18 | 1.61 (crop 25) | 1.55 | 1.51 | no leak detected |
| hmac_sha256/klen=16,mlen=150 | key and message bytes | 8 | 100246 | 99754 | 1192.7 | 1192.7 | -0.158 | -0.0131% | -1.88 | 4.89 (crop 21) | 0.73 | 1.33 | **t > 4.5** |
| hmac_sha256/klen=64,mlen=64 | key and message bytes | 32 | 100037 | 99963 | 1028.6 | 1028.6 | -0.736 | -0.0698% | +2.03 | 6.91 (crop 24) | 1.12 | 1.40 | **t > 4.5** |
| hmac_sha256/klen=32,mlen=1 | key and message bytes | 32 | 99718 | 100282 | 885.4 | 885.4 | +0.031 | +0.0034% | -0.19 | 3.76 (crop 14) | 1.19 | 1.55 | no leak detected |
| thash/len=16 | m (e.g. SK.seed / chain value / node values) | 64 | 199754 | 200246 | 375.7 | 376.3 | +0.153 | +0.0392% | +1.76 | 3.29 (crop 14) | 0.71 | 1.29 | no leak detected |
| thash/len=32 | m (e.g. SK.seed / chain value / node values) | 64 | 200044 | 199956 | 371.7 | 372.4 | -0.250 | -0.0644% | -0.96 | 7.58 (crop 12) | 1.20 | 1.26 | **t > 4.5** |
| thash/len=560 | m (e.g. SK.seed / chain value / node values) | 16 | 200036 | 199964 | 1755.2 | 1755.2 | +0.873 | +0.0493% | +1.16 | 2.84 (crop 30) | 0.94 | 1.40 | no leak detected |
| thash/len=224 | m (e.g. SK.seed / chain value / node values) | 32 | 200273 | 199727 | 809.9 | 809.9 | -0.038 | -0.0046% | -1.99 | 9.84 (crop 14) | 1.41 | 1.10 | **t > 4.5** |
| prf_msg/mlen=0 | SK.prf and opt_rand(addrnd) | 32 | 100034 | 99966 | 884.1 | 884.1 | -0.016 | -0.0018% | -0.43 | 2.50 (crop 6) | 0.92 | 0.59 | no leak detected |
| prf_msg/mlen=32 | SK.prf and opt_rand(addrnd) | 32 | 99542 | 100458 | 849.0 | 849.0 | -0.073 | -0.0085% | -0.96 | 1.49 (crop 15) | 0.95 | 1.50 | no leak detected |
| prf_msg/mlen=100 | SK.prf and opt_rand(addrnd) | 16 | 100080 | 99920 | 1000.0 | 1000.0 | -0.292 | -0.0286% | -0.74 | 4.04 (crop 16) | 1.24 | 1.85 | no leak detected |
| prf_msg/mlen=1000 | SK.prf and opt_rand(addrnd) | 8 | 99874 | 100126 | 3109.4 | 3109.4 | +0.019 | +0.0006% | -2.12 | 2.90 (crop 12) | 1.18 | 0.84 | no leak detected |
| chain/i=0,s=15 | start value x | 4 | 100153 | 99847 | 5197.9 | 5197.9 | -0.492 | -0.0094% | -0.95 | 2.55 (crop 0) | 1.71 | 1.86 | no leak detected |
| chain/i=0,s=1 | start value x | 64 | 100553 | 99447 | 358.7 | 358.7 | -0.004 | -0.0011% | -0.80 | 1.44 (crop 64) | 1.06 | 1.35 | no leak detected |
| chain/i=3,s=7 | start value x | 8 | 100033 | 99967 | 2432.3 | 2432.3 | -0.279 | -0.0113% | -0.31 | 2.62 (crop 28) | 1.19 | 1.89 | no leak detected |
| chain/i=15,s=0 | start value x | 8192 | 100283 | 99717 | 3.1 | 3.1 | +0.000 | +0.0019% | +0.47 | 0.81 (crop 1) | 1.78 | 2.38 | no leak detected |
| chain/i=0,s=0 | start value x | 8192 | 99782 | 100218 | 3.1 | 3.1 | +0.000 | +0.0048% | -0.36 | 2.16 (crop 2) | 1.49 | 2.04 | no leak detected |
| wots_pk_gen | SK.seed | 1 | 49952 | 50048 | 196541.7 | 196500.0 | +59.110 | +0.0299% | +0.94 | 2.15 (crop 28) | 2.00 | 1.41 | no leak detected |
| wots_sign | SK.seed (message m public, fixed) | 1 | 50105 | 49895 | 103000.0 | 103000.0 | +7.411 | +0.0071% | -0.55 | 2.01 (crop 0) | 1.48 | 1.10 | no leak detected |
| xmss_node/z=0 | SK.seed | 1 | 10005 | 9995 | 195083.3 | 195166.7 | -59.678 | -0.0305% | -1.76 | 2.10 (crop 47) | 2.05 | 1.70 | no leak detected |
| xmss_node/z=1 | SK.seed | 1 | 10033 | 9967 | 395083.3 | 394833.3 | +45.993 | +0.0116% | +0.44 | 2.14 (crop 1) | 1.36 | 1.35 | no leak detected |
| xmss_node/z=2 | SK.seed | 1 | 3040 | 2960 | 803750.0 | 803750.0 | -615.784 | -0.0762% | +0.21 | 2.10 (crop 0) | 2.40 | 2.19 | no leak detected |
| xmss_node/z=3 | SK.seed | 1 | 2947 | 3053 | 1581625.0 | 1581250.0 | +1225.936 | +0.0771% | -0.40 | 1.85 (crop 27) | 1.21 | 2.46 | no leak detected |
| xmss_node/z=4 | SK.seed | 1 | 2988 | 3012 | 3154958.3 | 3155208.3 | +197.999 | +0.0063% | -0.31 | 1.96 (crop 8) | 2.20 | 1.70 | no leak detected |
| xmss_sign | SK.seed (m, idx public, fixed) | 1 | 492 | 508 | 106918666.7 | 107354541.7 | -221015.145 | -0.2093% | -2.05 | 2.18 (crop 71) | 1.67 | 1.24 | no leak detected |
| fors_sk_gen | SK.seed | 64 | 200547 | 199453 | 373.7 | 374.3 | -0.248 | -0.0659% | -2.65 | 4.10 (crop 28) | 1.78 | 1.25 | no leak detected |
| fors_node/z=0 | SK.seed | 32 | 100088 | 99912 | 714.8 | 714.8 | +0.253 | +0.0343% | +0.16 | 1.97 (crop 19) | 2.37 | 2.89 | no leak detected |
| fors_node/z=1 | SK.seed | 16 | 99737 | 100263 | 1895.8 | 1895.8 | -0.215 | -0.0115% | -0.47 | 1.05 (crop 9) | 1.26 | 1.22 | no leak detected |
| fors_node/z=3 | SK.seed | 4 | 30094 | 29906 | 8218.8 | 8218.8 | -1.537 | -0.0186% | +1.31 | 2.24 (crop 2) | 1.21 | 1.92 | no leak detected |
| fors_node/z=6 | SK.seed | 1 | 5083 | 4917 | 68291.7 | 68333.3 | -43.622 | -0.0637% | -1.54 | 2.71 (crop 33) | 1.11 | 2.41 | no leak detected |
| fors_node/z=12 | SK.seed | 1 | 1985 | 2015 | 4477583.3 | 4475958.3 | +2111.909 | +0.0470% | -0.41 | 2.09 (crop 19) | 2.84 | 1.29 | no leak detected |
| fors_sign | SK.seed (md public, fixed) | 1 | 299 | 301 | 63818833.3 | 63901041.7 | +30177.487 | +0.0471% | -0.16 | 1.69 (crop 20) | 2.12 | 1.06 | no leak detected |
| slh_keygen_internal | SK.seed and SK.prf (PK.seed fixed) | 1 | 1027 | 973 | 103743000.0 | 103671333.3 | +152167.281 | +0.1461% | +1.54 | 2.13 (crop 4) | 1.80 | 1.54 | no leak detected |
| CONTROL leaky_cmp (early-exit compare of secret) | secret (leaky by construction) | 32 | 100383 | 99617 | 3380.2 | 208.3 | +3181.536 | +176.3402% | +3136.25 | 3312.59 (crop 21) | 1.61 | 1.53 | leak detected (expected: control) |
| CONTROL leaky_loop (secret-dependent iteration count) | secret byte (leaky by construction) | 32 | 99785 | 100215 | 1.3 | 683.6 | -616.934 | -198.8542% | -875.94 | 925.32 (crop 34) | 2.10 | 0.69 | leak detected (expected: control) |
