# multi/security-hw

The security theorems of `../security` (SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f}), compiled
against the translation of `multi/rust` built with `hw-sha2` (`../lean-hw`) instead of the
portable build's (`../lean`). The counterpart, for the six-set tree, of the main tree's
`security-hw/`.

There are no proof sources here: `lakefile.toml` compiles in place, unmodified,

- `MLink`, `MReduction`, `ME2E`, `MIdeal` and the shims (including `Link.Sha256`) from
  `../security`;
- `Link.Security`, `Reduction.*` (the same module list as `../security`),
  `E2E.{GuardedRom,CodedRom}` (`E2ERom`), `Reduction.Open.*` (`ReductionOpen`) and `Ideal.*`
  except `Ideal/Rust*.lean` (`Ideal`, 154 modules) from `../../security`;
- `Spec` from `../lean`; `Arm` (the instruction model) from `../../lean-hw`;
- `Slhdsa` from `../lean-hw`: the `hw-sha2` translation and its refinement proofs. Its headline
  files are links to `../lean`'s, so the Rust-function theorems `ME2E` builds on are the same
  statements, here about the `hw-sha2` functions.

So the 257 headlines of `../security` (Rust functions = scheme cores, standard-model bounds, `api`
forms, checked = plain signer, the context-string random-oracle theorem, all six sets; and the
closed ideal-compression bound, SLH-DSA-SHA2-128s only) hold, under the same names and
statements, of the `hw-sha2` build. In particular, verbatim as in `../security/STATUS.md` §5
(`../security/MIdeal/Sha2_128s.lean`, lines 158, 222, 274),
`MIdeal.sha2_128s.rust_ideal_security_closed_tight8`, `rust_ideal_security_closed_pure_tight8` and
`api_ideal_security_closed_pure_tight8` hold of the `hw-sha2` translation's
`slhdsa.sets.sha2_128s.{slh_keygen_internal, slh_sign_internal, slh_verify_internal, slh_sign,
slh_verify, keygen, sign, sign_deterministic, verify}`: each says (1) these functions never panic
and are pointwise the byte-level cores of `Reduction.bytesAlg` / `pureBytesAlg` at
`Sha2Set.s128s`, (2) that scheme is the ideal-model game's scheme at the table of the real SHA-256
compression function, (3) the ideal-model SUF/EUF-CMA advantage of every forger with `qf`
compression and `qs` signing queries on messages of at most `ℓ` bytes is at most
`epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ + QlinT8 qf qs ℓ / 2 ^ 128 +
polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) / 2 ^ 256` (when `QcAll qf qs ℓ ≤ 2 ^ 126`), and at
most `2^-77 + 2^-132 + 2^-63` (`qf ≤ 2^60`, `qs ≤ 2^20`), `2^-63 + 2^-94 + 2^-59` (`qf ≤ 2^64`,
`qs ≤ 2^40`), `2^-45 + 2^-46 + 2^-39` (`qf ≤ 2^64`, `qs ≤ 2^64`), `ℓ ≤ 2^26` (external
interface: `ℓ + 257` in place of `ℓ`). Conjunct 3 is about the ideal-model scheme only.

## Run

    scripts/check.sh          # or: scripts/check.sh clean   (from scratch: own copies of every library)

It checks that the libraries are `../security`'s (only `Slhdsa`'s source and the extra `Arm`
differ), builds `MLink MReduction ME2E E2ERom MIdeal`, scans every source file the build compiled
(links resolved) for `sorry` / `axiom` / `native_decide` / `bv_decide`, checks that the
environments of `ME2E` and `MIdeal` contain the `hw-sha2` chain kernel
`slhdsa.sha256.hw.chain_all`, prints the axioms of the 257 headlines (expected: `propext`, `Classical.choice`, `Quot.sound`; the list is written
to `status/axioms.txt`) and checks that they are the names of `../security/status/axioms.txt`.
Last run (2026-11-22, first build of `Ideal`/`ReductionOpen`/`MIdeal` here): "Build completed
successfully (8162 jobs)", build step 191 s, 257 / 257 headlines within `[propext,
Classical.choice, Quot.sound]`, "CHECK PASSED".
`lake build` alone builds the default targets `MLink MReduction ME2E`; `MIdeal` (with the
in-place `Ideal`, `ReductionOpen`) is not a default target, as in `../security`: `lake build
MIdeal`.

## Covers / does not cover

- Covers: the same theorems as `../security`, about the `hw-sha2` translation. What they
  mean, and their hypotheses, are described in `../security/STATUS.md`.
- Trusted in addition, as for `../lean-hw`: the instruction model of `../../lean-hw/Arm.lean`
  and `../../lean-hw/Slhdsa/FunsExternal.lean` (the eighteen `sha256::hw::arm` wrappers,
  transcribed from the Arm ARM and tested against one processor by `ArmTest`, not proved).
- Not covered: constant time of the `hw-sha2` build (a separate effort in `../lean-hw`), the
  experimental `hw-sha512` feature (not translated), and everything `../security/STATUS.md`
  lists as not covered for the portable build — in particular the ideal-compression bound is for
  SLH-DSA-SHA2-128s only (the ideal-model analysis of `security/Ideal` is of SHA-256 with 16-byte
  outputs; the other five sets would need it re-instantiated at their parameters, and for
  n = 24, 32 an ideal SHA-512 compression function as well; `../security/STATUS.md` §5), and it
  says nothing about the real compression function.
