# multi/security-hw

The security theorems of `../security` (SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}), compiled
against the translation of `multi/rust` built with `hw-sha2` (`../lean-hw`) instead of the
portable build's (`../lean`). The counterpart, for the six-set tree, of the main tree's
`security-hw/`.

There are no proof sources here: `lakefile.toml` compiles in place, unmodified,

- `MLink`, `MReduction`, `ME2E` and the shims from `../security`;
- `Link.Security`, `Reduction.*` (the same module list as `../security`) and
  `E2E.{GuardedRom,CodedRom}` (`E2ERom`) from `../../security`;
- `Spec` from `../lean`; `Arm` (the instruction model) from `../../lean-hw`;
- `Slhdsa` from `../lean-hw`: the `hw-sha2` translation and its refinement proofs. Its headline
  files are links to `../lean`'s, so the Rust-function theorems `ME2E` builds on are the same
  statements, here about the `hw-sha2` functions.

So the 252 headlines of `../security` (Rust functions = scheme cores, standard-model bounds, `api`
forms, checked = plain signer, the context-string random-oracle theorem; all six sets) hold,
under the same names and statements, of the `hw-sha2` build.

## Run

    scripts/check.sh          # or: scripts/check.sh clean   (from scratch: own copies of every library)

It checks that the libraries are `../security`'s (only `Slhdsa`'s source and the extra `Arm`
differ), builds `MLink MReduction ME2E E2ERom`, scans every source file the build compiled
(links resolved) for `sorry` / `axiom` / `native_decide` / `bv_decide`, checks that the
environment contains the `hw-sha2` chain kernel `slhdsa.sha256.hw.chain_all`, prints the axioms
of the 252 headlines (expected: `propext`, `Classical.choice`, `Quot.sound`; the list is written
to `status/axioms.txt`) and checks that they are the names of `../security/status/axioms.txt`.
`lake build` alone builds the default targets `MLink MReduction ME2E`.

## Covers / does not cover

- Covers: the same theorems as `../security`, about the `hw-sha2` translation. What they
  mean, and their hypotheses, are described in `../security/STATUS.md`.
- Trusted in addition, as for `../lean-hw`: the instruction model of `../../lean-hw/Arm.lean`
  and `../../lean-hw/Slhdsa/FunsExternal.lean` (the eighteen `sha256::hw::arm` wrappers,
  transcribed from the Arm ARM and tested against one processor by `ArmTest`, not proved).
- Not covered: constant time of the `hw-sha2` build (a separate effort in `../lean-hw`), the
  experimental `hw-sha512` feature (not translated), and everything `../security/STATUS.md`
  lists as not covered for the portable build.
