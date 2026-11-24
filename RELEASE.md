# rust-pq 0.2.0 source release

The source distribution contains the `slhdsa` Rust core, the `slhdsa-compat` adapter, the Lean proofs and toolchain manifests, the FIPS 205 test vectors, and the benchmark reports, drivers and tracked measurements. The two Cargo packages share the version 0.2.0. Use the adapter as a path dependency in the extracted tree. [Installation and feature selection](README.md#use-the-020-source-release) · [API examples](compat/README.md) · [Security claim](reports/Post-quantum%20security%20claim.md)

## Verify and use the archive

Place the archive and its companion checksum in the same directory. The following commands use the macOS or Linux `shasum` utility.

```sh
shasum -a 256 -c rust-pq-0.2.0.tar.gz.sha256
tar -xzf rust-pq-0.2.0.tar.gz
cd rust-pq-0.2.0
cargo test --manifest-path rust/Cargo.toml --release --locked
cargo test --manifest-path compat/Cargo.toml --release --locked
```

Run each test command with `--all-features` to exercise the accelerated and parallel paths supported by the host. Cargo downloads the locked Rust dependencies on first use. The portable build works without Lean. The source distribution preserves symbolic links used by the proof workspaces.

## Rebuild the release

From a Git checkout, run `python3 scripts/package-release.py` with Python 3.11 or newer. It archives the committed HEAD with a versioned directory prefix and writes the tarball and SHA-256 checksum to `dist/`. Use `--output DIR` for a separate destination. Git records the source commit in the tar header. Recover it with `gzip -dc rust-pq-0.2.0.tar.gz | git get-tar-commit-id`. The checksum detects changes to the archive. Publisher authentication requires a trusted distribution channel or a separately authenticated checksum.

The release uses the existing per-workspace Lean toolchain and Lake manifests. Proof replay needs the external tool checkouts and build dependencies. The audited Aeneas checkout is `2e3d4488280bb8a95411db81019a7854a784861f`, and the security workspace pins VCVio at `a10530a59390442437f3c69db11015c4dd437839`. See the check scripts for platform-specific prerequisites. [Proof replay](README.md#reproducing) · [Security dependencies](security/README.md) · [Aeneas source](https://github.com/AeneasVerif/aeneas/tree/2e3d4488280bb8a95411db81019a7854a784861f)

## Third-party material

The project's original contributions are dual-licensed `MIT OR Apache-2.0`. The RustCrypto-derived code and tests retain the notices supplied in the core and adapter. The vendored slhdsa-c benchmark retains its ISC license. The test-vector directory documents the provenance of the NIST fixtures. External tools and dependencies are distributed under their respective licenses. [Project MIT license](LICENSE-MIT) · [Project Apache license](LICENSE-APACHE) · [Core RustCrypto notice](rust/LICENSE-MIT-RustCrypto) · [Adapter MIT notice](compat/LICENSE-MIT-RustCrypto) · [Adapter Apache notice](compat/LICENSE-APACHE-RustCrypto) · [slhdsa-c license](bench/vendor/slhdsa-c/LICENSE) · [Vector provenance](vectors/README.md)
