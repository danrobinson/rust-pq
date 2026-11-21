## Signature operations

Median time per operation over all samples of all 2 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 40.40 ms <sub>±0.6%</sub> | 305.24 ms <sub>±0.3%</sub> | 311.31 ms <sub>±0.6%</sub> | 323.90 µs <sub>±0.7%</sub> | 2.69 ms <sub>±0.4%</sub> |
| verified-before | 102.83 ms **0.39×** <sub>±1.1%</sub> | 779.34 ms **0.39×** <sub>±0.1%</sub> | 787.07 ms **0.40×** <sub>±0.1%</sub> | 804.03 µs **0.40×** <sub>±0.3%</sub> | 3.18 ms **0.84×** <sub>±1.1%</sub> |
| variant-A | 58.67 ms **0.69×** <sub>±0.7%</sub> | 448.97 ms **0.68×** <sub>±0.3%</sub> | 453.21 ms **0.69×** <sub>±0.5%</sub> | 474.84 µs **0.68×** <sub>±2.0%</sub> | 3.10 ms **0.87×** <sub>±4.7%</sub> |
| variant-B | 49.27 ms **0.82×** <sub>±0.1%</sub> | 368.06 ms **0.83×** <sub>±0.5%</sub> | 379.18 ms **0.82×** <sub>±1.1%</sub> | 381.31 µs **0.85×** <sub>±0.7%</sub> | 2.84 ms **0.94×** <sub>±1.6%</sub> |
| variant-C | 13.29 ms **3.0×** <sub>±1.4%</sub> | 101.07 ms **3.0×** <sub>±1.0%</sub> | 100.95 ms **3.1×** <sub>±0.1%</sub> | 102.36 µs **3.2×** <sub>±1.6%</sub> | 428.55 µs **6.3×** <sub>±0.2%</sub> |
| variant-D | 11.64 ms **3.5×** <sub>±0.8%</sub> | 82.44 ms **3.7×** <sub>±0.8%</sub> | 83.58 ms **3.7×** <sub>±2.0%</sub> | 84.82 µs **3.8×** <sub>±1.5%</sub> | 448.69 µs **6.0×** <sub>±0.1%</sub> |
| rustcrypto-slh-dsa | 8.30 ms **4.9×** <sub>±0.1%</sub> | 62.77 ms **4.9×** <sub>±0.3%</sub> | 63.27 ms **4.9×** <sub>±0.1%</sub> | 63.86 µs **5.1×** <sub>±0.2%</sub> | 364.21 µs **7.4×** <sub>±0.0%</sub> |
| fips205 | 61.23 ms **0.66×** <sub>±0.1%</sub> | 471.99 ms **0.65×** <sub>±0.1%</sub> | 475.06 ms **0.66×** <sub>±0.2%</sub> | 479.22 µs **0.68×** <sub>±0.1%</sub> | 2.18 ms **1.2×** <sub>±1.4%</sub> |
| openssl | 7.32 ms **5.5×** <sub>±1.1%</sub> | 55.96 ms **5.5×** <sub>±1.3%</sub> | 56.49 ms **5.5×** <sub>±0.2%</sub> | 58.95 µs **5.5×** <sub>±2.3%</sub> | 405.17 µs **6.6×** <sub>±0.0%</sub> |
| slhdsa-c | 28.64 ms **1.4×** <sub>±0.0%</sub> | 218.47 ms **1.4×** <sub>±0.0%</sub> | 226.56 ms **1.4×** <sub>±0.1%</sub> | 225.31 µs **1.4×** <sub>±0.0%</sub> | 1.86 ms **1.4×** <sub>±0.0%</sub> |
| pqclean-r3 | 35.17 ms **1.1×** <sub>±1.0%</sub> | 266.95 ms **1.1×** <sub>±0.0%</sub> | 279.19 ms **1.1×** <sub>±2.0%</sub> | 259.98 µs **1.2×** <sub>±0.4%</sub> | 1.93 ms **1.4×** <sub>±0.6%</sub> |

### config `hw`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified+hw-sha2 | 4.00 ms <sub>±0.3%</sub> | 30.22 ms <sub>±0.0%</sub> | 30.85 ms <sub>±0.0%</sub> | 35.40 µs <sub>±0.2%</sub> | 352.27 µs <sub>±0.1%</sub> |
| verified-before | 105.98 ms **0.04×** <sub>±1.5%</sub> | 790.03 ms **0.04×** <sub>±1.5%</sub> | 795.30 ms **0.04×** <sub>±2.0%</sub> | 828.35 µs **0.04×** <sub>±1.0%</sub> | 3.18 ms **0.11×** <sub>±0.1%</sub> |
| rustcrypto-slh-dsa | 8.30 ms **0.48×** <sub>±0.9%</sub> | 62.58 ms **0.48×** <sub>±0.6%</sub> | 63.19 ms **0.49×** <sub>±0.0%</sub> | 63.78 µs **0.56×** <sub>±0.2%</sub> | 364.87 µs **0.97×** <sub>±0.9%</sub> |
| openssl | 7.32 ms **0.55×** <sub>±1.8%</sub> | 56.00 ms **0.54×** <sub>±1.3%</sub> | 56.95 ms **0.54×** <sub>±1.4%</sub> | 58.86 µs **0.60×** <sub>±0.6%</sub> | 405.45 µs **0.87×** <sub>±1.0%</sub> |
| slhdsa-c | 29.27 ms **0.14×** <sub>±0.5%</sub> | 220.06 ms **0.14×** <sub>±0.6%</sub> | 223.14 ms **0.14×** <sub>±0.8%</sub> | 225.80 µs **0.16×** <sub>±0.7%</sub> | 1.87 ms **0.19×** <sub>±0.9%</sub> |

## SHA-256 one-shot (median per call; MB/s in parentheses)

### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.8 ns (1841 MB/s) | 34.7 ns (2935 MB/s) | 302.7 ns (3383 MB/s) |
| sha2-0.10 | 203.3 ns (315 MB/s) | 203.4 ns (502 MB/s) | 1.75 µs (587 MB/s) |
| sha2-0.11 | 32.9 ns (1943 MB/s) | 29.4 ns (3470 MB/s) | 300.1 ns (3412 MB/s) |
| variant-B-soft-streaming | 279.2 ns (229 MB/s) | 305.8 ns (334 MB/s) | 2.43 µs (422 MB/s) |
| variant-C-armv8 | 37.8 ns (1693 MB/s) | 55.8 ns (1828 MB/s) | 308.3 ns (3321 MB/s) |
| verified | 342.9 ns (187 MB/s) | 314.9 ns (324 MB/s) | 2.48 µs (412 MB/s) |
