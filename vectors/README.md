NIST ACVP test vectors for SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}, extracted from
https://github.com/usnistgov/ACVP-Server (gen-val/json-files/SLH-DSA-{keyGen,sigGen,sigVer}-FIPS205/internalProjection.json)
by `scripts/extract_vectors.py`. One file per parameter set; only the SHA-2 groups are kept, and the
pre-hash (HashSLH-DSA) groups are dropped. Each file has 10 keyGen, 28 sigGen and 28 sigVer cases.
They are read by `rust/tests/acvp.rs` and by the Lean specification test (`lean/SpecTest.lean`).

`arm-wrappers.txt`: the record of the twenty-eight intrinsic wrappers of the `hw-sha2` backends
(`rust/src/sha256.rs` and `rust/src/sha512.rs`, modules `hw::arm`) on one processor (Apple M5),
2,961 calls with their results (the first 1,745 for the eighteen SHA-256 wrappers, then 1,216
for the ten SHA-512 wrappers, added on 2026-11-22). `cargo test --release --features hw-sha2` in `rust/` checks the processor it runs on
against it (`ARM_VECTORS_WRITE=1` rewrites it instead); `lean-hw/ArmTest.lean` runs the Lean
model of the wrappers on the same file.
