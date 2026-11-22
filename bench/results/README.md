# Benchmark results

`run1` … `run6` were all measured on the **single-set crate** (SLH-DSA-SHA2-128s only; `rust/` and
`compat/` as of git commit `26aa3d8` or earlier), before it was replaced by the six-set crate on
2026-11-22. In them `verified`, `verified+hw-sha2` and `verified-api` are that crate and its
adapter, and "current rust/" in `compressions.md` means that crate. `../RESULTS.md` describes
runs 1–6. New runs of `../run.sh` go into new directories here
and measure the six-set crate's 128s functions under the same names.
