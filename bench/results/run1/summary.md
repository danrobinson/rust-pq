## Signature operations

Median time per operation over all samples of all 4 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 108.44 ms <sub>±2.9%</sub> | 789.23 ms <sub>±3.8%</sub> | 818.43 ms <sub>±3.5%</sub> | 824.03 µs <sub>±2.2%</sub> | 3.23 ms <sub>±2.1%</sub> |
| variant-A | 61.20 ms **1.8×** <sub>±4.1%</sub> | 467.64 ms **1.7×** <sub>±3.7%</sub> | 475.71 ms **1.7×** <sub>±3.9%</sub> | 477.39 µs **1.7×** <sub>±2.3%</sub> | 3.04 ms **1.1×** <sub>±2.3%</sub> |
| variant-B | 49.38 ms **2.2×** <sub>±3.1%</sub> | 374.89 ms **2.1×** <sub>±2.3%</sub> | 378.56 ms **2.2×** <sub>±0.7%</sub> | 386.79 µs **2.1×** <sub>±2.6%</sub> | 2.86 ms **1.1×** <sub>±2.6%</sub> |
| variant-C | 13.38 ms **8.1×** <sub>±2.6%</sub> | 103.86 ms **7.6×** <sub>±3.1%</sub> | 103.31 ms **7.9×** <sub>±1.7%</sub> | 104.13 µs **7.9×** <sub>±2.0%</sub> | 436.43 µs **7.4×** <sub>±3.4%</sub> |
| rustcrypto-slh-dsa | 8.43 ms **12.9×** <sub>±1.8%</sub> | 62.63 ms **12.6×** <sub>±3.2%</sub> | 64.33 ms **12.7×** <sub>±3.1%</sub> | 64.94 µs **12.7×** <sub>±2.5%</sub> | 371.47 µs **8.7×** <sub>±2.8%</sub> |
| fips205 | 64.55 ms **1.7×** <sub>±3.2%</sub> | 473.06 ms **1.7×** <sub>±3.3%</sub> | 486.17 ms **1.7×** <sub>±3.4%</sub> | 487.59 µs **1.7×** <sub>±0.8%</sub> | 2.21 ms **1.5×** <sub>±3.4%</sub> |
| openssl | 7.71 ms **14.1×** <sub>±2.6%</sub> | 55.89 ms **14.1×** <sub>±3.5%</sub> | 58.42 ms **14.0×** <sub>±3.0%</sub> | 59.54 µs **13.8×** <sub>±1.7%</sub> | 407.04 µs **7.9×** <sub>±3.5%</sub> |
| slhdsa-c | 29.63 ms **3.7×** <sub>±3.4%</sub> | 222.21 ms **3.6×** <sub>±3.3%</sub> | 225.95 ms **3.6×** <sub>±3.1%</sub> | 229.46 µs **3.6×** <sub>±3.3%</sub> | 1.90 ms **1.7×** <sub>±3.4%</sub> |
| pqclean-r3 | 36.85 ms **2.9×** <sub>±5.3%</sub> | 272.47 ms **2.9×** <sub>±1.7%</sub> | 275.28 ms **3.0×** <sub>±3.1%</sub> | 279.86 µs **2.9×** <sub>±3.6%</sub> | 1.96 ms **1.7×** <sub>±3.5%</sub> |

### config `soft`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 105.56 ms <sub>±3.1%</sub> | 808.68 ms <sub>±3.0%</sub> | 804.02 ms <sub>±2.4%</sub> | 814.43 µs <sub>±1.2%</sub> | 3.20 ms <sub>±1.9%</sub> |
| rustcrypto-slh-dsa | 30.35 ms **3.5×** <sub>±3.3%</sub> | 230.96 ms **3.5×** <sub>±3.2%</sub> | 233.62 ms **3.4×** <sub>±2.4%</sub> | 236.55 µs **3.4×** <sub>±2.3%</sub> | 1.82 ms **1.8×** <sub>±1.2%</sub> |
| fips205 | 62.37 ms **1.7×** <sub>±3.3%</sub> | 480.63 ms **1.7×** <sub>±3.2%</sub> | 481.70 ms **1.7×** <sub>±0.9%</sub> | 491.58 µs **1.7×** <sub>±3.0%</sub> | 2.20 ms **1.5×** <sub>±1.2%</sub> |

### config `tuned`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 109.93 ms <sub>±2.4%</sub> | 840.81 ms <sub>±2.8%</sub> | 837.63 ms <sub>±2.4%</sub> | 855.44 µs <sub>±2.5%</sub> | 3.34 ms <sub>±3.5%</sub> |
| variant-A | 61.42 ms **1.8×** <sub>±1.9%</sub> | 476.61 ms **1.8×** <sub>±2.7%</sub> | 469.84 ms **1.8×** <sub>±2.3%</sub> | 485.20 µs **1.8×** <sub>±2.3%</sub> | 2.98 ms **1.1×** <sub>±1.4%</sub> |
| variant-B | 48.62 ms **2.3×** <sub>±2.2%</sub> | 373.29 ms **2.3×** <sub>±3.3%</sub> | 375.10 ms **2.2×** <sub>±3.2%</sub> | 392.80 µs **2.2×** <sub>±3.6%</sub> | 2.83 ms **1.2×** <sub>±2.0%</sub> |
| variant-C | 13.34 ms **8.2×** <sub>±2.1%</sub> | 102.00 ms **8.2×** <sub>±2.9%</sub> | 100.98 ms **8.3×** <sub>±3.6%</sub> | 104.47 µs **8.2×** <sub>±2.9%</sub> | 431.96 µs **7.7×** <sub>±3.2%</sub> |
| rustcrypto-slh-dsa | 7.01 ms **15.7×** <sub>±3.3%</sub> | 52.94 ms **15.9×** <sub>±3.3%</sub> | 53.56 ms **15.6×** <sub>±3.2%</sub> | 57.34 µs **14.9×** <sub>±3.3%</sub> | 362.64 µs **9.2×** <sub>±3.1%</sub> |
| fips205 | 63.43 ms **1.7×** <sub>±3.0%</sub> | 488.36 ms **1.7×** <sub>±3.2%</sub> | 491.01 ms **1.7×** <sub>±3.1%</sub> | 492.94 µs **1.7×** <sub>±2.3%</sub> | 2.21 ms **1.5×** <sub>±3.3%</sub> |

### config `asm`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 105.08 ms <sub>±1.3%</sub> | 804.50 ms <sub>±2.2%</sub> | 811.47 ms <sub>±1.7%</sub> | 822.95 µs <sub>±2.9%</sub> | 3.21 ms <sub>±0.8%</sub> |
| fips205 | 11.48 ms **9.2×** <sub>±2.2%</sub> | 95.19 ms **8.5×** <sub>±2.2%</sub> | 95.87 ms **8.5×** <sub>±2.4%</sub> | 99.84 µs **8.2×** <sub>±3.0%</sub> | 407.24 µs **7.9×** <sub>±2.7%</sub> |

### tuned / default, same implementation

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 0.99× | 0.94× | 0.98× | 0.96× | 0.97× |
| variant-A | 1.00× | 0.98× | 1.01× | 0.98× | 1.02× |
| variant-B | 1.02× | 1.00× | 1.01× | 0.98× | 1.01× |
| variant-C | 1.00× | 1.02× | 1.02× | 1.00× | 1.01× |
| rustcrypto-slh-dsa | 1.20× | 1.18× | 1.20× | 1.13× | 1.02× |
| fips205 | 1.02× | 0.97× | 0.99× | 0.99× | 1.00× |

## SHA-256 one-shot (median per call; MB/s in parentheses)

### config `asm`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 35.4 ns (1807 MB/s) | 35.4 ns (2878 MB/s) | 310.4 ns (3299 MB/s) |
| sha2-0.10 | 30.8 ns (2080 MB/s) | 30.5 ns (3347 MB/s) | 304.7 ns (3361 MB/s) |
| sha2-0.11 | 33.4 ns (1916 MB/s) | 30.1 ns (3383 MB/s) | 305.7 ns (3350 MB/s) |
| variant-B-soft-streaming | 296.5 ns (216 MB/s) | 315.8 ns (323 MB/s) | 2.46 µs (416 MB/s) |
| variant-C-armv8 | 39.2 ns (1634 MB/s) | 57.0 ns (1789 MB/s) | 314.9 ns (3252 MB/s) |
| verified | 327.0 ns (196 MB/s) | 312.8 ns (326 MB/s) | 2.49 µs (410 MB/s) |

### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 35.4 ns (1805 MB/s) | 35.4 ns (2880 MB/s) | 311.9 ns (3283 MB/s) |
| sha2-0.10 | 207.1 ns (309 MB/s) | 207.1 ns (493 MB/s) | 1.77 µs (580 MB/s) |
| sha2-0.11 | 33.4 ns (1915 MB/s) | 30.0 ns (3400 MB/s) | 307.1 ns (3334 MB/s) |
| variant-B-soft-streaming | 287.6 ns (223 MB/s) | 308.9 ns (330 MB/s) | 2.43 µs (422 MB/s) |
| variant-C-armv8 | 38.4 ns (1667 MB/s) | 56.8 ns (1795 MB/s) | 314.5 ns (3256 MB/s) |
| verified | 317.2 ns (202 MB/s) | 311.2 ns (328 MB/s) | 2.49 µs (411 MB/s) |

### config `soft`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 36.5 ns (1751 MB/s) | 35.7 ns (2861 MB/s) | 313.6 ns (3265 MB/s) |
| sha2-0.10 | 207.5 ns (308 MB/s) | 207.5 ns (492 MB/s) | 1.76 µs (581 MB/s) |
| sha2-0.11 | 195.8 ns (327 MB/s) | 196.0 ns (520 MB/s) | 1.64 µs (625 MB/s) |
| variant-B-soft-streaming | 284.2 ns (225 MB/s) | 315.3 ns (324 MB/s) | 2.43 µs (421 MB/s) |
| variant-C-armv8 | 38.5 ns (1664 MB/s) | 57.1 ns (1788 MB/s) | 313.6 ns (3265 MB/s) |
| verified | 320.2 ns (200 MB/s) | 322.7 ns (316 MB/s) | 2.54 µs (403 MB/s) |
