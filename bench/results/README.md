# Benchmark results

| Comparison | Coverage |
|---|---|
| [RustCrypto and OpenSSL](peers-optimized/README.md) | Seven processors, all twelve parameter sets, signing, verification, key operations and encodings |
| [Botan, Conduition and Fluhrer](optimized-competitors/README.md) | Seven processors, with parameter sets and thread counts reported per peer |
| [Parallel CPU signing](parallel/README.md) | Five processors, on workloads selected because a peer beat the single-threaded build |

The [performance summary](../../README.md#performance) reports speedups across workloads. Each linked report includes the measurements and reproduction method.
