## Signature operations

Median time per operation over all samples of all 4 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 42.88 ms <sub>±1.4%</sub> | 325.19 ms <sub>±0.8%</sub> | 332.85 ms <sub>±2.7%</sub> | 337.64 µs <sub>±1.4%</sub> | 2.79 ms <sub>±0.6%</sub> |
| verified-before | 102.50 ms **0.42×** <sub>±0.2%</sub> | 784.96 ms **0.41×** <sub>±1.4%</sub> | 788.48 ms **0.42×** <sub>±1.5%</sub> | 805.27 µs **0.42×** <sub>±1.3%</sub> | 3.17 ms **0.88×** <sub>±1.3%</sub> |
| variant-A | 58.94 ms **0.73×** <sub>±0.2%</sub> | 452.97 ms **0.72×** <sub>±2.9%</sub> | 459.80 ms **0.72×** <sub>±1.1%</sub> | 468.31 µs **0.72×** <sub>±1.0%</sub> | 2.94 ms **0.95×** <sub>±0.5%</sub> |
| variant-B | 48.46 ms **0.88×** <sub>±0.6%</sub> | 368.93 ms **0.88×** <sub>±4.3%</sub> | 380.65 ms **0.87×** <sub>±2.1%</sub> | 384.56 µs **0.88×** <sub>±0.4%</sub> | 2.80 ms **1.00×** <sub>±0.9%</sub> |
| variant-C | 13.20 ms **3.2×** <sub>±0.3%</sub> | 100.86 ms **3.2×** <sub>±3.5%</sub> | 101.63 ms **3.3×** <sub>±1.2%</sub> | 103.41 µs **3.3×** <sub>±0.7%</sub> | 428.97 µs **6.5×** <sub>±3.0%</sub> |
| variant-D | 11.44 ms **3.7×** <sub>±0.2%</sub> | 85.77 ms **3.8×** <sub>±6.4%</sub> | 86.27 ms **3.9×** <sub>±3.2%</sub> | 84.21 µs **4.0×** <sub>±3.1%</sub> | 449.09 µs **6.2×** <sub>±0.1%</sub> |
| rustcrypto-slh-dsa | 8.29 ms **5.2×** <sub>±0.8%</sub> | 62.55 ms **5.2×** <sub>±0.2%</sub> | 63.20 ms **5.3×** <sub>±1.0%</sub> | 63.72 µs **5.3×** <sub>±3.3%</sub> | 363.90 µs **7.7×** <sub>±0.1%</sub> |
| fips205 | 61.23 ms **0.70×** <sub>±0.3%</sub> | 471.76 ms **0.69×** <sub>±0.1%</sub> | 475.46 ms **0.70×** <sub>±1.3%</sub> | 483.26 µs **0.70×** <sub>±1.0%</sub> | 2.16 ms **1.3×** <sub>±0.2%</sub> |
| openssl | 7.39 ms **5.8×** <sub>±1.6%</sub> | 56.39 ms **5.8×** <sub>±1.6%</sub> | 56.51 ms **5.9×** <sub>±1.0%</sub> | 58.68 µs **5.8×** <sub>±0.9%</sub> | 405.13 µs **6.9×** <sub>±1.2%</sub> |
| slhdsa-c | 28.62 ms **1.5×** <sub>±0.1%</sub> | 218.79 ms **1.5×** <sub>±3.3%</sub> | 222.16 ms **1.5×** <sub>±1.0%</sub> | 225.61 µs **1.5×** <sub>±0.9%</sub> | 1.86 ms **1.5×** <sub>±0.1%</sub> |
| pqclean-r3 | 35.17 ms **1.2×** <sub>±0.1%</sub> | 267.25 ms **1.2×** <sub>±1.0%</sub> | 270.47 ms **1.2×** <sub>±0.9%</sub> | 263.14 µs **1.3×** <sub>±3.6%</sub> | 1.93 ms **1.4×** <sub>±1.7%</sub> |

### config `soft`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 42.89 ms <sub>±1.2%</sub> | 324.36 ms <sub>±0.5%</sub> | 329.54 ms <sub>±0.9%</sub> | 335.35 µs <sub>±0.4%</sub> | 2.80 ms <sub>±0.7%</sub> |
| verified-before | 102.54 ms **0.42×** <sub>±0.8%</sub> | 787.56 ms **0.41×** <sub>±1.3%</sub> | 784.05 ms **0.42×** <sub>±0.6%</sub> | 801.06 µs **0.42×** <sub>±0.5%</sub> | 3.17 ms **0.89×** <sub>±0.5%</sub> |
| rustcrypto-slh-dsa | 29.62 ms **1.4×** <sub>±0.6%</sub> | 225.80 ms **1.4×** <sub>±0.5%</sub> | 229.03 ms **1.4×** <sub>±0.7%</sub> | 231.18 µs **1.5×** <sub>±0.3%</sub> | 1.78 ms **1.6×** <sub>±1.1%</sub> |
| fips205 | 61.17 ms **0.70×** <sub>±0.1%</sub> | 471.62 ms **0.69×** <sub>±0.2%</sub> | 474.41 ms **0.69×** <sub>±0.1%</sub> | 481.13 µs **0.70×** <sub>±0.0%</sub> | 2.16 ms **1.3×** <sub>±0.1%</sub> |

### config `tuned`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 43.21 ms <sub>±1.0%</sub> | 327.95 ms <sub>±0.3%</sub> | 332.84 ms <sub>±0.4%</sub> | 342.65 µs <sub>±0.3%</sub> | 2.85 ms <sub>±0.3%</sub> |
| verified-before | 105.08 ms **0.41×** <sub>±0.2%</sub> | 802.82 ms **0.41×** <sub>±0.0%</sub> | 808.32 ms **0.41×** <sub>±0.5%</sub> | 820.42 µs **0.42×** <sub>±0.4%</sub> | 3.28 ms **0.87×** <sub>±0.5%</sub> |
| variant-A | 59.41 ms **0.73×** <sub>±0.2%</sub> | 454.95 ms **0.72×** <sub>±0.1%</sub> | 462.05 ms **0.72×** <sub>±0.0%</sub> | 472.32 µs **0.73×** <sub>±0.5%</sub> | 2.98 ms **0.96×** <sub>±1.3%</sub> |
| variant-B | 48.46 ms **0.89×** <sub>±0.3%</sub> | 371.37 ms **0.88×** <sub>±0.0%</sub> | 377.38 ms **0.88×** <sub>±1.8%</sub> | 381.78 µs **0.90×** <sub>±0.6%</sub> | 2.83 ms **1.0×** <sub>±0.2%</sub> |
| variant-C | 12.99 ms **3.3×** <sub>±0.7%</sub> | 100.16 ms **3.3×** <sub>±1.3%</sub> | 104.54 ms **3.2×** <sub>±2.4%</sub> | 104.52 µs **3.3×** <sub>±0.4%</sub> | 428.63 µs **6.7×** <sub>±0.9%</sub> |
| rustcrypto-slh-dsa | 6.89 ms **6.3×** <sub>±0.0%</sub> | 51.90 ms **6.3×** <sub>±0.1%</sub> | 52.50 ms **6.3×** <sub>±0.0%</sub> | 55.40 µs **6.2×** <sub>±0.0%</sub> | 355.14 µs **8.0×** <sub>±0.1%</sub> |
| fips205 | 62.23 ms **0.69×** <sub>±0.0%</sub> | 478.42 ms **0.69×** <sub>±0.0%</sub> | 482.02 ms **0.69×** <sub>±0.0%</sub> | 477.84 µs **0.72×** <sub>±0.8%</sub> | 2.15 ms **1.3×** <sub>±0.0%</sub> |

### config `asm`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 43.02 ms <sub>±0.4%</sub> | 326.28 ms <sub>±0.0%</sub> | 329.40 ms <sub>±0.1%</sub> | 337.92 µs <sub>±0.3%</sub> | 2.83 ms <sub>±0.6%</sub> |
| verified-before | 101.73 ms **0.42×** <sub>±0.1%</sub> | 785.42 ms **0.42×** <sub>±0.6%</sub> | 784.75 ms **0.42×** <sub>±0.1%</sub> | 806.55 µs **0.42×** <sub>±0.3%</sub> | 3.15 ms **0.90×** <sub>±0.1%</sub> |
| fips205 | 11.26 ms **3.8×** <sub>±0.1%</sub> | 93.30 ms **3.5×** <sub>±0.0%</sub> | 93.90 ms **3.5×** <sub>±0.0%</sub> | 99.54 µs **3.4×** <sub>±1.2%</sub> | 401.22 µs **7.1×** <sub>±0.9%</sub> |

### tuned / default, same implementation

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 0.99× | 0.99× | 1.00× | 0.99× | 0.98× |
| verified-before | 0.98× | 0.98× | 0.98× | 0.98× | 0.97× |
| variant-A | 0.99× | 1.00× | 1.00× | 0.99× | 0.99× |
| variant-B | 1.00× | 0.99× | 1.01× | 1.01× | 0.99× |
| variant-C | 1.02× | 1.01× | 0.97× | 0.99× | 1.00× |
| rustcrypto-slh-dsa | 1.20× | 1.21× | 1.20× | 1.15× | 1.02× |
| fips205 | 0.98× | 0.99× | 0.99× | 1.01× | 1.00× |

## SHA-256 one-shot (median per call; MB/s in parentheses)

### config `asm`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2937 MB/s) | 302.8 ns (3382 MB/s) |
| sha2-0.10 | 29.5 ns (2172 MB/s) | 29.5 ns (3462 MB/s) | 299.3 ns (3421 MB/s) |
| sha2-0.11 | 32.8 ns (1951 MB/s) | 29.4 ns (3470 MB/s) | 299.9 ns (3414 MB/s) |
| variant-B-soft-streaming | 280.7 ns (228 MB/s) | 301.4 ns (338 MB/s) | 2.38 µs (431 MB/s) |
| variant-C-armv8 | 37.8 ns (1695 MB/s) | 54.7 ns (1865 MB/s) | 307.9 ns (3326 MB/s) |
| verified | 323.5 ns (198 MB/s) | 311.2 ns (328 MB/s) | 2.53 µs (404 MB/s) |

### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2939 MB/s) | 302.7 ns (3383 MB/s) |
| sha2-0.10 | 203.1 ns (315 MB/s) | 203.3 ns (502 MB/s) | 1.73 µs (593 MB/s) |
| sha2-0.11 | 32.8 ns (1952 MB/s) | 29.4 ns (3468 MB/s) | 300.0 ns (3413 MB/s) |
| variant-B-soft-streaming | 280.1 ns (228 MB/s) | 303.4 ns (336 MB/s) | 2.40 µs (427 MB/s) |
| variant-C-armv8 | 37.8 ns (1691 MB/s) | 55.4 ns (1843 MB/s) | 308.2 ns (3323 MB/s) |
| verified | 317.4 ns (202 MB/s) | 316.2 ns (323 MB/s) | 2.56 µs (399 MB/s) |

### config `soft`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2937 MB/s) | 302.7 ns (3383 MB/s) |
| sha2-0.10 | 203.3 ns (315 MB/s) | 203.3 ns (502 MB/s) | 1.73 µs (594 MB/s) |
| sha2-0.11 | 191.1 ns (335 MB/s) | 191.5 ns (533 MB/s) | 1.60 µs (638 MB/s) |
| variant-B-soft-streaming | 278.1 ns (230 MB/s) | 298.7 ns (342 MB/s) | 2.45 µs (418 MB/s) |
| variant-C-armv8 | 37.8 ns (1695 MB/s) | 54.7 ns (1865 MB/s) | 308.1 ns (3323 MB/s) |
| verified | 321.5 ns (199 MB/s) | 314.3 ns (325 MB/s) | 2.55 µs (401 MB/s) |
