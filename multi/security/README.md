# multi/security

Machine-checked security results for SLH-DSA-SHA2-{128s,128f,192s,192f,256s,256f} (Lean 4.36.0):

- `MLink`: the parameterised FIPS 205 transcription (`multi/lean/Spec`) equals VCVio's executable
  scheme at `approvedPrimitives` for each set (keygen, sign, verify; internal and pure; byte level;
  SHA-256/SHA-512, HMAC, MGF1), plus the random-oracle bound and conformance.
- `MReduction`: the standard-model reduction of `security/Reduction` (compiled in place,
  unmodified) instantiated at the six sets: SUF/EUF headlines, linear forms, deterministic/hedged
  corollaries, resources with numerals, audit of which SHA function each game is about.
- `ME2E`: the verified Rust functions `sets.sha2_<set>.slh_*` are the byte-level scheme cores;
  `ME2E.sha2_<set>.rust_security` etc.; the interface functions `sets.sha2_<set>.{keygen, sign,
  sign_deterministic, verify}` likewise, with the checked signers equal to the plain ones on
  well-formed keys (`ME2E.sha2_<set>.api_pure_security`, `api_sign_checked_eq_sign`, …); the
  random-oracle theorem for the context-string interface (`ME2E.sha2_<set>.pure_rom_security`,
  `rust_pure_rom_security_bytes`, `api_pure_rom_security(_bytes)`).
- `MIdeal` (SLH-DSA-SHA2-128s only; not a default target, `lake build MIdeal`): the closed
  ideal-compression bound of `security/Ideal` (which is compiled here in place, unmodified, except
  its single-set Rust corollaries `Ideal/Rust*.lean`; one more Spec-free stand-in,
  `shim/Link/Sha256.lean`) attached to `sets.sha2_128s.*`:
  `MIdeal.sha2_128s.rust_ideal_security_closed_tight8` (`slh_*_internal`),
  `rust_ideal_security_closed_pure_tight8` (`slh_keygen_internal`, `slh_sign`, `slh_verify`),
  `api_ideal_security_closed_pure_tight8` (`keygen`, `sign`, `sign_deterministic`, `verify`). Each
  is the single-set `Ideal.*_tight8` statement with the Rust names renamed and the real scheme
  spelled at `Sha2Set.s128s` (textual check `scripts/check_ideal128s.py`); the bound is the same
  proved bound, about the ideal-model scheme only. STATUS.md §5.

Read `STATUS.md`. Check: `scripts/check.sh` (or `scripts/check.sh clean`).
