# security

Machine-checked security results for SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f} (Lean 4.36.0, Mathlib
v4.36.0), attached to the verified Rust crate `../rust` (portable build; `../security-hw` compiles the
same files against the `hw-sha2` build). One Lake project; every library is a default target, so
`lake build` builds all of it (about 4 minutes from scratch on a 36-core machine, dependencies prebuilt).

- `MLink`: the parameterised FIPS 205 transcription (`../lean/Spec`) equals VCVio's executable scheme at
  `approvedPrimitives` for each set (keygen, sign, verify; internal and pure; byte level; SHA-256/SHA-512,
  HMAC, MGF1), plus the random-oracle bound and conformance.
- `MReduction`: the standard-model reduction of `Reduction` instantiated at the six sets: SUF/EUF
  headlines, linear forms, deterministic/hedged corollaries, resources with numerals, audit of which SHA
  function each game is about.
- `ME2E`: the verified Rust functions `sets.sha2_<set>.slh_*` are the byte-level scheme cores;
  `ME2E.sha2_<set>.rust_security` etc.; the interface functions `sets.sha2_<set>.{keygen, sign,
  sign_deterministic, verify}` likewise, with the checked signers equal to the plain ones on well-formed
  keys (`ME2E.sha2_<set>.api_pure_security`, `api_sign_checked_eq_sign`, …); the random-oracle theorem for
  the context-string interface (`ME2E.sha2_<set>.pure_rom_security`, `rust_pure_rom_security_bytes`,
  `api_pure_rom_security(_bytes)`); for 128s also the forms for forgers over a general sampling
  spec (`ME2E.sha2_128s.rust_securityG`, …, `api_pure_securityG`; `STATUS.md` §5b).
- `MIdeal` (SLH-DSA-SHA2-128s only): the closed ideal-compression bound of `Ideal` attached to
  `sets.sha2_128s.*`: `MIdeal.sha2_128s.rust_ideal_security_closed_tight8` (`slh_*_internal`),
  `rust_ideal_security_closed_pure_tight8` (`slh_keygen_internal`, `slh_sign`, `slh_verify`),
  `api_ideal_security_closed_pure_tight8` (`keygen`, `sign`, `sign_deterministic`, `verify`). Each is the
  single-set tree's `Ideal.*_tight8` statement with the Rust names renamed and the real scheme spelled at
  `Sha2Set.s128s` (textual check `scripts/check_ideal128s.py`); the bound is the same proved bound, about
  the ideal-model scheme only. `STATUS.md` §5.
- Generic libraries, which the four above build on (they import nothing of `Spec` or `Slhdsa`):
  - `Reduction` (`Reduction/**`): the standard-model SUF-CMA / EUF-CMA reduction for SLH-DSA (no random
    oracle) for any parameter set and primitive bundle, with its SHA2-128s instances at `Link.vp`,
    `Link.prims`; `Reduction/Open` (open-program forms of the adversaries) and `Reduction/Gen` (forgers over
    a general sampling spec). Games, adversaries, resources: `REDUCTION_STATUS.md`, `status/FINAL3.md`.
  - `Ideal` (`Ideal/**`): the ideal-compression-function analysis of SLH-DSA-SHA2-128s: with SHA-256's
    compression function a random table, each of the twelve assumptions of the reduction bounded in the
    adversary's own queries, and the composed bounds `suf/euf_ideal_closed(_tight8)`, `…_pure_…`.
    `IDEAL_STATUS.md`, `status/TIGHT.md`.
  - `Link` (`Link/{Basic,Hash,Verify,Sha256,Security}.lean`): the SHA2-128s vocabulary they are stated
    in (`Link.vp`, `Link.prims`, decoders, word packing) and VCVio's random-oracle bound at 128s.
  - `E2E` (`E2E/{GuardedRom,CodedRom}.lean`): a scheme behind a partial message encoding / seen through
    encodings, over any oracle interface; used by `ME2E/PureRom.lean`.

Read `STATUS.md` (statements, the stand-ins that replaced the single-set `Link` files, what was deleted
when the single-set tree was removed on 2026-11-22). `REDUCTION_STATUS.md`, `IDEAL_STATUS.md` and
`status/` are the single-set development's documents (`status/README.md`).

## Dependencies

- VCVio: upstream `https://github.com/Verified-zkEVM/VCVio`, commit
  `a10530a59390442437f3c69db11015c4dd437839`, checked out at `../.tools/VCVio-upstream` (path
  dependency). `packagesDir` in `lakefile.toml` points at that clone's `.lake/packages`, so its Mathlib
  checkout and cache are shared.
- Aeneas Lean backend: `../.tools/aeneas/backends/lean`, already built by the `../lean` project.
- Both pin Mathlib `v4.36.0` (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`). `lake-manifest.json` is checked
  in; if it is regenerated with `lake update`, make sure the Mathlib revision stays at `v4.36.0`.

## Reproduction

```sh
export PATH=$HOME/.elan/bin:$PATH
cd <repo>/.tools
git clone https://github.com/Verified-zkEVM/VCVio VCVio-upstream
git -C VCVio-upstream checkout a10530a59390442437f3c69db11015c4dd437839
(cd VCVio-upstream && lake exe cache get)      # Mathlib cache
cd ../security
lake build                                     # everything
scripts/check.sh                               # generators, build, placeholder grep, 263 axiom reports
```

`scripts/check.sh` reads the single-set tree's statements from git commit `26aa3d8` (the templates of the
ME2E generators and of the MIdeal textual check), so it needs the repository's history.
