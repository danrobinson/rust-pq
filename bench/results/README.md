# Benchmark results

The [main README](../../README.md#performance) summarizes the seven-processor comparison.
The two CSVs in `peers-optimized/` come from commit `735c74b`, which also contains the
benchmark drivers, per-round samples and host metadata. The measured sources were
`deb57d6` for x86, `4ceac15` for Graviton and `424109e` for Apple.

Running `./run.sh` from the benchmark directory writes a separate, local SHA2-128s
comparison under `results/<stamp>/`. The earlier single-set reports are in Git at
`be142b7:bench/RESULTS.md` and `be142b7:bench/results/`.
