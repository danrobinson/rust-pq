## Signature operations

Median time per operation over all samples of all 2 rounds; **bold** = speed-up over the verified crate
in the same build configuration (>1 = faster than verified); ±x% = half the range of the per-round medians.

### config `default`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified | 43.01 ms <sub>±0.9%</sub> | 324.52 ms <sub>±0.5%</sub> | 329.52 ms <sub>±0.3%</sub> | 335.79 µs <sub>±0.7%</sub> | 2.81 ms <sub>±0.5%</sub> |
| verified-before | 102.78 ms **0.42×** <sub>±0.4%</sub> | 780.23 ms **0.42×** <sub>±0.1%</sub> | 783.86 ms **0.42×** <sub>±0.2%</sub> | 802.45 µs **0.42×** <sub>±0.1%</sub> | 3.14 ms **0.89×** <sub>±0.0%</sub> |
| variant-A | 58.71 ms **0.73×** <sub>±0.3%</sub> | 450.06 ms **0.72×** <sub>±0.5%</sub> | 453.00 ms **0.73×** <sub>±0.2%</sub> | 465.74 µs **0.72×** <sub>±0.0%</sub> | 2.94 ms **0.95×** <sub>±0.1%</sub> |
| variant-B | 49.10 ms **0.88×** <sub>±0.8%</sub> | 369.88 ms **0.88×** <sub>±0.4%</sub> | 378.73 ms **0.87×** <sub>±0.7%</sub> | 384.63 µs **0.87×** <sub>±0.4%</sub> | 2.79 ms **1.0×** <sub>±0.8%</sub> |
| variant-C | 13.18 ms **3.3×** <sub>±0.3%</sub> | 100.22 ms **3.2×** <sub>±0.1%</sub> | 101.37 ms **3.3×** <sub>±0.2%</sub> | 101.21 µs **3.3×** <sub>±0.2%</sub> | 422.49 µs **6.6×** <sub>±0.1%</sub> |
| variant-D | 11.18 ms **3.8×** <sub>±0.3%</sub> | 82.23 ms **3.9×** <sub>±0.2%</sub> | 83.02 ms **4.0×** <sub>±0.7%</sub> | 83.39 µs **4.0×** <sub>±0.1%</sub> | 444.49 µs **6.3×** <sub>±0.1%</sub> |
| rustcrypto-slh-dsa | 8.29 ms **5.2×** <sub>±0.1%</sub> | 62.59 ms **5.2×** <sub>±0.1%</sub> | 63.22 ms **5.2×** <sub>±0.1%</sub> | 63.99 µs **5.2×** <sub>±0.0%</sub> | 363.99 µs **7.7×** <sub>±0.0%</sub> |
| fips205 | 61.17 ms **0.70×** <sub>±0.0%</sub> | 471.05 ms **0.69×** <sub>±0.0%</sub> | 474.35 ms **0.69×** <sub>±0.0%</sub> | 479.15 µs **0.70×** <sub>±0.0%</sub> | 2.15 ms **1.3×** <sub>±0.0%</sub> |
| openssl | 7.32 ms **5.9×** <sub>±0.4%</sub> | 55.75 ms **5.8×** <sub>±0.1%</sub> | 56.35 ms **5.8×** <sub>±0.1%</sub> | 58.42 µs **5.7×** <sub>±0.2%</sub> | 404.95 µs **6.9×** <sub>±1.2%</sub> |
| slhdsa-c | 28.62 ms **1.5×** <sub>±0.0%</sub> | 218.29 ms **1.5×** <sub>±0.1%</sub> | 221.55 ms **1.5×** <sub>±0.1%</sub> | 225.30 µs **1.5×** <sub>±0.0%</sub> | 1.86 ms **1.5×** <sub>±0.0%</sub> |
| pqclean-r3 | 35.15 ms **1.2×** <sub>±0.0%</sub> | 266.67 ms **1.2×** <sub>±0.0%</sub> | 270.03 ms **1.2×** <sub>±0.0%</sub> | 266.60 µs **1.3×** <sub>±2.0%</sub> | 1.91 ms **1.5×** <sub>±0.1%</sub> |

### config `hw`

| implementation | keygen | sign_32B | sign_1MiB | verify_32B | verify_1MiB |
|---|---|---|---|---|---|
| verified+hw-sha2 | 11.54 ms <sub>±0.1%</sub> | 83.65 ms <sub>±0.9%</sub> | 84.37 ms <sub>±1.7%</sub> | 85.34 µs <sub>±1.2%</sub> | 449.58 µs <sub>±0.7%</sub> |
| verified-before | 104.64 ms **0.11×** <sub>±2.5%</sub> | 792.76 ms **0.11×** <sub>±2.6%</sub> | 800.36 ms **0.11×** <sub>±2.5%</sub> | 818.37 µs **0.10×** <sub>±2.4%</sub> | 3.18 ms **0.14×** <sub>±0.6%</sub> |
| rustcrypto-slh-dsa | 8.28 ms **1.4×** <sub>±0.0%</sub> | 62.49 ms **1.3×** <sub>±0.0%</sub> | 63.12 ms **1.3×** <sub>±0.0%</sub> | 63.83 µs **1.3×** <sub>±0.2%</sub> | 364.05 µs **1.2×** <sub>±0.1%</sub> |
| openssl | 7.32 ms **1.6×** <sub>±0.1%</sub> | 55.80 ms **1.5×** <sub>±0.1%</sub> | 56.62 ms **1.5×** <sub>±0.4%</sub> | 58.54 µs **1.5×** <sub>±0.6%</sub> | 405.20 µs **1.1×** <sub>±0.1%</sub> |
| slhdsa-c | 28.75 ms **0.40×** <sub>±0.5%</sub> | 219.03 ms **0.38×** <sub>±0.3%</sub> | 222.81 ms **0.38×** <sub>±0.7%</sub> | 225.79 µs **0.38×** <sub>±0.8%</sub> | 1.87 ms **0.24×** <sub>±0.1%</sub> |

## SHA-256 one-shot (median per call; MB/s in parentheses)

### config `default`

| implementation | sha256_64B | sha256_102B | sha256_1024B |
|---|---|---|---|
| openssl | 34.7 ns (1845 MB/s) | 34.7 ns (2939 MB/s) | 302.8 ns (3382 MB/s) |
| sha2-0.10 | 203.0 ns (315 MB/s) | 203.3 ns (502 MB/s) | 1.73 µs (593 MB/s) |
| sha2-0.11 | 32.8 ns (1950 MB/s) | 29.4 ns (3471 MB/s) | 300.3 ns (3410 MB/s) |
| variant-B-soft-streaming | 280.4 ns (228 MB/s) | 304.8 ns (335 MB/s) | 2.40 µs (426 MB/s) |
| variant-C-armv8 | 37.8 ns (1692 MB/s) | 55.3 ns (1844 MB/s) | 308.0 ns (3325 MB/s) |
| verified | 320.9 ns (199 MB/s) | 311.0 ns (328 MB/s) | 2.55 µs (402 MB/s) |
