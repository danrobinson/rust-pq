## Signature operations

Median time per operation over all samples of all 2 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 39.88 ms <sub>±0.1%</sub> | 305.36 ms <sub>±0.1%</sub> | 309.50 ms <sub>±0.1%</sub> | 315.55 µs <sub>±0.2%</sub> | 2.68 ms <sub>±0.2%</sub> |
| verified-api | 39.95 ms **1.00×** <sub>±0.0%</sub> | 305.41 ms **1.00×** <sub>±0.0%</sub> | 309.55 ms **1.00×** <sub>±0.5%</sub> | 316.34 µs **1.00×** <sub>±0.2%</sub> | 2.68 ms **1.00×** <sub>±0.2%</sub> |
| verified-before | 102.85 ms **0.39×** <sub>±0.2%</sub> | 781.12 ms **0.39×** <sub>±0.5%</sub> | 788.82 ms **0.39×** <sub>±0.1%</sub> | 807.08 µs **0.39×** <sub>±0.1%</sub> | 3.18 ms **0.84×** <sub>±0.2%</sub> |
| variant-A | 58.90 ms **0.68×** <sub>±0.2%</sub> | 448.47 ms **0.68×** <sub>±0.0%</sub> | 452.66 ms **0.68×** <sub>±0.0%</sub> | 463.41 µs **0.68×** <sub>±0.3%</sub> | 2.93 ms **0.91×** <sub>±0.2%</sub> |
| variant-B | 48.76 ms **0.82×** <sub>±0.7%</sub> | 372.97 ms **0.82×** <sub>±0.1%</sub> | 377.15 ms **0.82×** <sub>±0.2%</sub> | 389.55 µs **0.81×** <sub>±0.1%</sub> | 2.78 ms **0.96×** <sub>±0.3%</sub> |
| variant-C | 13.26 ms **3.0×** <sub>±0.1%</sub> | 100.46 ms **3.0×** <sub>±0.3%</sub> | 101.26 ms **3.1×** <sub>±0.0%</sub> | 103.23 µs **3.1×** <sub>±0.4%</sub> | 434.01 µs **6.2×** <sub>±1.9%</sub> |
| variant-D | 11.26 ms **3.5×** <sub>±2.0%</sub> | 82.29 ms **3.7×** <sub>±0.1%</sub> | 82.79 ms **3.7×** <sub>±0.3%</sub> | 84.25 µs **3.7×** <sub>±1.0%</sub> | 446.90 µs **6.0×** <sub>±0.7%</sub> |
| rustcrypto-slh-dsa | 8.29 ms **4.8×** <sub>±0.0%</sub> | 62.59 ms **4.9×** <sub>±0.0%</sub> | 63.17 ms **4.9×** <sub>±0.0%</sub> | 63.64 µs **5.0×** <sub>±0.0%</sub> | 363.84 µs **7.4×** <sub>±0.0%</sub> |
| fips205 | 61.23 ms **0.65×** <sub>±0.0%</sub> | 471.69 ms **0.65×** <sub>±0.0%</sub> | 474.82 ms **0.65×** <sub>±0.0%</sub> | 479.17 µs **0.66×** <sub>±0.0%</sub> | 2.15 ms **1.2×** <sub>±0.0%</sub> |
| openssl | 7.33 ms **5.4×** <sub>±0.2%</sub> | 55.71 ms **5.5×** <sub>±0.2%</sub> | 56.36 ms **5.5×** <sub>±0.2%</sub> | 58.45 µs **5.4×** <sub>±0.1%</sub> | 404.80 µs **6.6×** <sub>±0.0%</sub> |
| slhdsa-c | 28.66 ms **1.4×** <sub>±0.1%</sub> | 218.77 ms **1.4×** <sub>±0.1%</sub> | 222.17 ms **1.4×** <sub>±0.0%</sub> | 225.42 µs **1.4×** <sub>±0.0%</sub> | 1.86 ms **1.4×** <sub>±0.0%</sub> |
| pqclean-r3 | 35.17 ms **1.1×** <sub>±0.1%</sub> | 266.94 ms **1.1×** <sub>±0.1%</sub> | 270.32 ms **1.1×** <sub>±0.0%</sub> | 273.96 µs **1.2×** <sub>±0.0%</sub> | 1.91 ms **1.4×** <sub>±0.5%</sub> |

### config `hw`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified+hw-sha2 | 3.91 ms <sub>±0.0%</sub> | 30.20 ms <sub>±0.0%</sub> | 30.87 ms <sub>±0.1%</sub> | 35.35 µs <sub>±0.0%</sub> | 352.26 µs <sub>±0.2%</sub> |
| verified-api+hw-sha2 | 3.93 ms **1.00×** <sub>±0.0%</sub> | 30.21 ms **1.00×** <sub>±0.0%</sub> | 30.89 ms **1.00×** <sub>±0.0%</sub> | 35.46 µs **1.00×** <sub>±0.0%</sub> | 351.73 µs **1.0×** <sub>±0.0%</sub> |
| verified-before | 102.04 ms **0.04×** <sub>±0.0%</sub> | 775.09 ms **0.04×** <sub>±0.2%</sub> | 783.71 ms **0.04×** <sub>±0.1%</sub> | 797.31 µs **0.04×** <sub>±0.3%</sub> | 3.15 ms **0.11×** <sub>±0.5%</sub> |
| rustcrypto-slh-dsa | 8.27 ms **0.47×** <sub>±0.0%</sub> | 62.42 ms **0.48×** <sub>±0.0%</sub> | 63.00 ms **0.49×** <sub>±0.0%</sub> | 63.78 µs **0.55×** <sub>±0.0%</sub> | 363.84 µs **0.97×** <sub>±0.0%</sub> |
| openssl | 7.32 ms **0.53×** <sub>±0.1%</sub> | 55.84 ms **0.54×** <sub>±0.3%</sub> | 56.38 ms **0.55×** <sub>±0.1%</sub> | 58.45 µs **0.60×** <sub>±0.1%</sub> | 406.32 µs **0.87×** <sub>±0.2%</sub> |
| slhdsa-c | 28.61 ms **0.14×** <sub>±0.0%</sub> | 218.46 ms **0.14×** <sub>±0.0%</sub> | 221.52 ms **0.14×** <sub>±0.1%</sub> | 225.21 µs **0.16×** <sub>±0.0%</sub> | 1.86 ms **0.19×** <sub>±0.0%</sub> |

## SHA-256 one-shot (median per call; MB/s in parentheses)

### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2939 MB/s) | 303.0 ns (3379 MB/s) |
| sha2-0.10 | 203.1 ns (315 MB/s) | 203.2 ns (502 MB/s) | 1.73 µs (594 MB/s) |
| sha2-0.11 | 32.9 ns (1948 MB/s) | 29.4 ns (3470 MB/s) | 300.3 ns (3410 MB/s) |
| variant-B-soft-streaming | 278.0 ns (230 MB/s) | 303.0 ns (337 MB/s) | 2.42 µs (423 MB/s) |
| variant-C-armv8 | 37.8 ns (1693 MB/s) | 55.0 ns (1856 MB/s) | 308.1 ns (3324 MB/s) |
| verified | 342.2 ns (187 MB/s) | 313.0 ns (326 MB/s) | 2.48 µs (412 MB/s) |
