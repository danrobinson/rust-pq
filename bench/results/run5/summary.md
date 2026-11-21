## Signature operations

Median time per operation over all samples of all 2 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 39.86 ms <sub>±0.1%</sub> | 303.56 ms <sub>±0.1%</sub> | 309.12 ms <sub>±0.0%</sub> | 316.17 µs <sub>±0.2%</sub> | 2.67 ms <sub>±0.6%</sub> |
| verified-before | 101.67 ms **0.39×** <sub>±0.1%</sub> | 777.57 ms **0.39×** <sub>±0.1%</sub> | 782.93 ms **0.39×** <sub>±0.0%</sub> | 799.78 µs **0.40×** <sub>±0.2%</sub> | 3.12 ms **0.85×** <sub>±0.0%</sub> |
| variant-A | 58.97 ms **0.68×** <sub>±0.2%</sub> | 447.81 ms **0.68×** <sub>±0.1%</sub> | 452.89 ms **0.68×** <sub>±0.2%</sub> | 460.89 µs **0.69×** <sub>±0.3%</sub> | 2.94 ms **0.91×** <sub>±1.0%</sub> |
| variant-B | 48.58 ms **0.82×** <sub>±0.3%</sub> | 369.87 ms **0.82×** <sub>±0.4%</sub> | 376.70 ms **0.82×** <sub>±1.1%</sub> | 390.49 µs **0.81×** <sub>±0.4%</sub> | 2.81 ms **0.95×** <sub>±0.2%</sub> |
| variant-C | 13.15 ms **3.0×** <sub>±0.4%</sub> | 100.18 ms **3.0×** <sub>±0.4%</sub> | 100.86 ms **3.1×** <sub>±0.3%</sub> | 101.65 µs **3.1×** <sub>±0.2%</sub> | 422.33 µs **6.3×** <sub>±0.2%</sub> |
| variant-D | 11.73 ms **3.4×** <sub>±1.0%</sub> | 85.60 ms **3.5×** <sub>±2.6%</sub> | 85.35 ms **3.6×** <sub>±1.1%</sub> | 83.83 µs **3.8×** <sub>±1.0%</sub> | 447.71 µs **6.0×** <sub>±0.8%</sub> |
| rustcrypto-slh-dsa | 8.28 ms **4.8×** <sub>±0.0%</sub> | 62.50 ms **4.9×** <sub>±0.0%</sub> | 63.08 ms **4.9×** <sub>±0.0%</sub> | 63.82 µs **5.0×** <sub>±0.2%</sub> | 364.23 µs **7.3×** <sub>±0.1%</sub> |
| fips205 | 61.19 ms **0.65×** <sub>±0.0%</sub> | 471.43 ms **0.64×** <sub>±0.1%</sub> | 474.47 ms **0.65×** <sub>±0.1%</sub> | 478.79 µs **0.66×** <sub>±0.0%</sub> | 2.16 ms **1.2×** <sub>±0.1%</sub> |
| openssl | 7.30 ms **5.5×** <sub>±0.4%</sub> | 55.57 ms **5.5×** <sub>±0.2%</sub> | 56.19 ms **5.5×** <sub>±0.1%</sub> | 58.39 µs **5.4×** <sub>±0.0%</sub> | 404.96 µs **6.6×** <sub>±0.1%</sub> |
| slhdsa-c | 28.62 ms **1.4×** <sub>±0.0%</sub> | 218.33 ms **1.4×** <sub>±0.0%</sub> | 221.41 ms **1.4×** <sub>±0.0%</sub> | 225.18 µs **1.4×** <sub>±0.1%</sub> | 1.86 ms **1.4×** <sub>±0.1%</sub> |
| pqclean-r3 | 35.13 ms **1.1×** <sub>±0.0%</sub> | 266.45 ms **1.1×** <sub>±0.0%</sub> | 269.89 ms **1.1×** <sub>±0.0%</sub> | 260.19 µs **1.2×** <sub>±0.4%</sub> | 1.92 ms **1.4×** <sub>±0.0%</sub> |

### config `hw`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified+hw-sha2 | 3.91 ms <sub>±0.0%</sub> | 30.21 ms <sub>±0.0%</sub> | 30.86 ms <sub>±0.0%</sub> | 35.36 µs <sub>±0.0%</sub> | 351.77 µs <sub>±0.0%</sub> |
| verified-before | 103.11 ms **0.04×** <sub>±0.4%</sub> | 785.68 ms **0.04×** <sub>±0.1%</sub> | 791.50 ms **0.04×** <sub>±0.1%</sub> | 804.22 µs **0.04×** <sub>±0.7%</sub> | 3.16 ms **0.11×** <sub>±0.5%</sub> |
| rustcrypto-slh-dsa | 8.28 ms **0.47×** <sub>±0.0%</sub> | 62.55 ms **0.48×** <sub>±0.0%</sub> | 63.13 ms **0.49×** <sub>±0.0%</sub> | 63.75 µs **0.55×** <sub>±0.2%</sub> | 363.81 µs **0.97×** <sub>±0.0%</sub> |
| openssl | 7.30 ms **0.54×** <sub>±0.1%</sub> | 55.76 ms **0.54×** <sub>±0.3%</sub> | 56.38 ms **0.55×** <sub>±0.3%</sub> | 58.60 µs **0.60×** <sub>±0.2%</sub> | 404.57 µs **0.87×** <sub>±0.0%</sub> |
| slhdsa-c | 28.63 ms **0.14×** <sub>±0.0%</sub> | 218.34 ms **0.14×** <sub>±0.0%</sub> | 221.67 ms **0.14×** <sub>±0.0%</sub> | 224.90 µs **0.16×** <sub>±0.0%</sub> | 1.86 ms **0.19×** <sub>±0.1%</sub> |

## SHA-256 one-shot (median per call; MB/s in parentheses)

### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2938 MB/s) | 302.9 ns (3381 MB/s) |
| sha2-0.10 | 203.1 ns (315 MB/s) | 203.1 ns (502 MB/s) | 1.73 µs (594 MB/s) |
| sha2-0.11 | 32.8 ns (1953 MB/s) | 29.4 ns (3471 MB/s) | 299.7 ns (3416 MB/s) |
| variant-B-soft-streaming | 285.0 ns (225 MB/s) | 302.0 ns (338 MB/s) | 2.42 µs (423 MB/s) |
| variant-C-armv8 | 37.5 ns (1706 MB/s) | 55.4 ns (1840 MB/s) | 308.2 ns (3323 MB/s) |
| verified | 347.1 ns (184 MB/s) | 309.4 ns (330 MB/s) | 2.47 µs (415 MB/s) |
