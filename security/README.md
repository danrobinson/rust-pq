# security — linking the Rust SLH-DSA-SHA2-128s code to VCVio's security theorem

One Lake workspace (Lean 4.36.0, Mathlib v4.36.0) containing six libraries:

| Library | Sources | Content |
|---|---|---|
| `Spec` | `../lean/Spec` (compiled in place) | our FIPS 205 transcription |
| `Slhdsa` | `../lean/Slhdsa` (compiled in place) | Aeneas extraction of the Rust code and its refinement proofs |
| `Link` | `Link/` | `Spec` = VCVio's executable SLH-DSA-SHA2-128s (keygen, sign, verify), and the security bridge |
| `E2E` | `E2E/` | Rust functions = VCVio's functions; summary theorem `E2E.end_to_end` |
| `Reduction` | `Reduction/` | standard-model SUF-CMA / EUF-CMA reduction for SLH-DSA (no random oracle); `E2E/Headline.lean` attaches it to the Rust code (`E2E/Reduction.lean`: superseded phase-1 attachment) |
| `Ideal` | `Ideal/` | separate package (imports `Reduction`; not a default target; not described here) |

Nothing is copied from `../lean`; nothing there or under `../.tools/aeneas` is modified.

## Dependencies

- VCVio: upstream `https://github.com/Verified-zkEVM/VCVio`, commit
  `a10530a59390442437f3c69db11015c4dd437839`, checked out at `../.tools/VCVio-upstream`
  (path dependency). `packagesDir` in `lakefile.toml` points at that clone's `.lake/packages`,
  so its Mathlib checkout and cache are shared.
- Aeneas Lean backend: `../.tools/aeneas/backends/lean` (aeneas commit
  `2e3d4488280bb8a95411db81019a7854a784861f`), already built by the `../lean` project.
- Both pin Mathlib `v4.36.0` (`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`).

## Reproduction

```sh
export PATH=$HOME/.elan/bin:$PATH
cd <repo>/.tools
git clone https://github.com/Verified-zkEVM/VCVio VCVio-upstream
git -C VCVio-upstream checkout a10530a59390442437f3c69db11015c4dd437839
(cd VCVio-upstream && lake exe cache get)      # Mathlib cache, ~1-2 min
cd ../security
lake build                                     # builds Link, E2E and Reduction
```

The first `lake build` compiles the VCVio modules that are needed (about 1.5 minutes on a
36-core machine) and `Slhdsa` (about 25 s); `Link` + `E2E` alone rebuild in about 20 s. The
Aeneas library is reused as built by `../lean` (same Mathlib revision, so no rebuild). With all
dependencies built, `Link`, `E2E` and `Reduction` (90 modules; 7702 jobs in total) compile from
scratch in roughly 45–75 s wall on a 36-core machine (figures and how they were measured:
`status/FINAL3.md`, section 8).

`lake-manifest.json` is checked in and lists `VCVio` and `aeneas` as path packages; if it is
regenerated with `lake update`, make sure the Mathlib revision stays at `v4.36.0`.

## Main statements

- `Link.verify_eq`, `Link.slhVerify_eq` (`Link/Verify.lean`), `Link.keygen_eq`
  (`Link/Keygen.lean`), `Link.sign_eq` (`Link/Sign.lean`): `Spec` = VCVio.
- `Link.security_128s`, `Link.romScheme_map_romAnswer_128s`, `Link.not_hprf`
  (`Link/Security.lean`), `Link.romScheme_verify_eq_spec` (`Link/Main.lean`).
- `E2E.rust_verify_internal`, `E2E.rust_verify`, `E2E.rust_keygen`, `E2E.rust_sign_internal`,
  `E2E.rust_sign`, `E2E.end_to_end`, `E2E.end_to_end_verify` (`E2E/Main.lean`).
- `E2E.rust_security`, `E2E.rust_pure_security`, `E2E.rust_security_linear`,
  `E2E.rust_pure_security_linear` (`E2E/Headline.lean`);
  `Reduction.slhdsa_bytes_suf_cma_final`, `Reduction.slhdsa_bytes_euf_cma_final`,
  `Reduction.slhdsa_pure_bytes_suf_cma_final`, `Reduction.slhdsa_pure_bytes_euf_cma_final`
  (`Reduction/HeadlineFinal.lean`) (see "Standard-model reduction" below).

Every file ends with `#print axioms` lines; all report only `propext`, `Classical.choice`,
`Quot.sound`. There is no `sorry`, `axiom`, `native_decide` or `bv_decide`.

## Standard-model reduction

`Reduction/` proves strong and existential unforgeability of SLH-DSA without a random oracle
(final state, games, adversaries, resources: `REDUCTION_STATUS.md`; summary with the verbatim
statements: `status/FINAL3.md`). Final theorems, `Reduction/HeadlineFinal.lean`:

- `Reduction.slhdsa_bytes_suf_cma_final`: for every parameter set and primitive bundle satisfying
  the non-cryptographic side conditions `Structural`, every wire codec, every `opt_rand` source,
  every `PK.seed` distribution and every strong forger `S` against the **byte-level** scheme
  `bytesAlg vp prims codec optRand pkSeedDist` (FIPS 205 Alg. 18–20 on byte strings: the forger
  gets public-key bytes and a signing oracle from message bytes to signature bytes), with
  `A = bytesToTyped S` the typed forger built from it,

  `Adv^SUF-CMA(S) ≤ Adv^PRF_PRF(bPrfWC sufCheck A) + Adv^PRF_PRFmsg(bPrfMsgWL sufCheck A)
  + Adv^ITSR_Hmsg(bItsrL A) + Adv^SM-DSPR_F(toDspr (bOpenPreS A)) + 3·Adv^SM-TCR_F(toTcr (bOpenPreS A))
  + Adv^SM-TCR_F(bTcrArM 1 A) + Adv^SM-TCR_H(bTcrArM 2 A) + Adv^SM-TCR_T_len(bTcrArM len A)
  + Adv^SM-TCR_T_k(bTcrArM k A) + (w−2)·Adv^SM-UD_F(rUd (bWotsS A)) + Adv^SM-PRE_F(rPre (bWotsS A))
  + Adv^SM-TCR_F(rTcrT (bWotsS A))`.

  The four middle terms are SM-TCR games on `Thash` restricted to inputs of 1, 2, `len`, `k`
  blocks (`Reduction.thashArityProblemT`), each capped at the exact number of calls of that
  function in the key structure; the `H` term covers FORS-tree and XMSS-tree nodes together.
  The last game (`Reduction.wotsTcrProblemT`) is capped at `#inst·len·(w−1)`.

- `Reduction.slhdsa_bytes_euf_cma_final`: the same bound for EUF-CMA, with the PRF distinguishers
  `bPrfC A`, `bPrfMsgL A`.
- `Reduction.slhdsa_pure_bytes_suf_cma_final`, `Reduction.slhdsa_pure_bytes_euf_cma_final`: the
  same bounds for the external pure interface with context strings on byte strings
  (`Reduction.pureBytesAlg`, FIPS 205 Alg. 21/22/24; a signature is `Option (List Byte)` as
  returned by the Rust `slh_sign`), at the internal forger `toInternal (pureBytesToTyped A)`.
- Typed keys and signatures (`internalAlg`, `externalAlg`):
  `Reduction.slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_memo` (`Reduction/TcrMemoHeadline.lean`).
- Linear form (no absolute values, no truncated subtraction; real-world probabilities on the
  right, ideal-world probabilities next to the advantage on the left):
  `Reduction.slhdsa_{suf,euf}_cma_final_linear`, `Reduction.slhdsa_pure_{suf,euf}_cma_final_linear`
  (`Reduction/Linear.lean`), `Reduction.slhdsa_{bytes,pure_bytes}_{suf,euf}_cma_linear`
  (`Reduction/LinearBytes.lean`).
- Uniform `PK.seed` and the two FIPS choices of `opt_rand` (the general theorems hold for an
  arbitrary seed distribution; for a degenerate one they speak about games with a known seed):
  `Reduction.slhdsa_{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}` and the SHA2-128s
  instances `Reduction.slhdsa_sha2_128s_…_{deterministic,hedged}`.
- `Reduction.final_resources_final`, `Reduction.final_resources_final_128s`
  (`Reduction/ResourcesFinal.lean`): for every adversary of the bound, oracle queries before the
  seed is revealed, own hash evaluations after it, and fresh samples; the file header marks
  which numbers are theorems and which are counting arguments. Earlier bundles
  (`Reduction.final_resources`, `Reduction.Resources2.final_resources_direct`,
  `Reduction.final_memo_resources`) remain.
- `Reduction.slhdsa_sha2_128s_{bytes,pure_bytes}_{suf,euf}_cma_final`: the instances at `Link.vp`,
  `Link.prims`, `Reduction.codec128s` (SLH-DSA-SHA2-128s, `w − 2 = 14`), with `Structural` proved.
- `E2E.rust_security`, `E2E.rust_pure_security` (`E2E/Headline.lean`): the Aeneas-extracted Rust
  `slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal`, resp. `slh_sign`,
  `slh_verify`, are pointwise equal to the deterministic cores `byteKeygen`, `byteSign`,
  `byteVerify` (`byteSignPure`, `byteVerifyPure`) of the byte-level scheme in the game, together
  with the SUF-CMA and EUF-CMA bounds for that scheme, written out term by term;
  `E2E.rust_security_linear`, `E2E.rust_pure_security_linear`; `E2E.rust_security_deterministic`,
  `_hedged`; `E2E.rust_security_resources`. The doc comment of `E2E.rust_security` lists the
  exact remaining gap between the scheme in the game and the Rust functions (sampling, `Room`
  bounds, fixed-length arrays, byte representations, the public key in signing).
- Earlier forms remain proved: typed games with loose caps and structure-recomputing class
  adversaries (`Reduction/HeadlineSplit.lean`, `E2E/FinalSplit.lean`, `E2E/Bytes.lean`), tight
  caps (`Reduction/TightCapsHeadline.lean`), one cross-arity SM-TCR term
  (`Reduction/Headline.lean`, `E2E/Final.lean`).

The PRF game is on the secret-key address domain of the parameter set (`Reduction.skPrfC`); the
other games are VCVio's definitions of the notions of Hülsing–Kudinov (ePrint 2022/346) and
Barbosa et al. (ePrint 2024/910). The EasyCrypt artefact of the latter (formosa-slhdsa, cloned at
`../.tools/formosa-slhdsa`, commit `d2d4d032f4660525bc41e45e06f1aef44cd3a827`) was used read-only
as a blueprint for the game sequence; nothing is imported from it.

The reduction adversaries are black-box and straight-line, run the forger once, and use neither
a choice principle nor an eager table (`scratch/Final/FinalCheck.lean`). The PRF, PRF_msg and
ITSR adversaries are polynomial in the number of signing queries (proved counts of game queries;
of samples and hash evaluations for the PRF_msg and ITSR adversaries; the local hashing of the
PRF distinguisher is not counted). The nine adversaries of the SM games are not: they walk the whole
key structure and register `≈ 2^63`–`2^79` targets at SHA2-128s, as in the paper's reduction,
because those games register all targets before `PK.seed` is revealed. After the seed is revealed their own hashing is polynomial in the number of signing queries
(formal upper bounds on hash evaluations, e.g. `≤ 269824 + qs·2007385 + 7857` for each per-arity
TCR adversary `bTcrArM` at SHA2-128s; the superseded `bTcrArS` recomputed the whole key
structure there, `≈ 2^79.81` evaluations); they still carry structure-size state. **No
running-time claim is made** (VCVio has no cost model for local computation; list work is not
counted). Further limits: the twelve advantages
are assumptions about SHA-256-based functions and are not bounded; the TCR terms are split by
arity, not by address type (one `H` term for both tree kinds, and an `F` term that the paper's
bound does not have at that place); single key; pure mode only for the external interface.

The phase-1 theorems (`Reduction.slhdsa_euf_cma`, `Reduction.slhdsa_sha2_128s_euf_cma`,
`E2E.standard_model_security`, `E2E.pure_standard_model_security`) remain proved but are
superseded: their PRF game ranges over all address values and is false for the SHA-2 bundle
(`Reduction.skPrf_broken_128s`), and five of their adversaries sample a `2^256`-cell table.

Forgers over a general sampling spec (`Reduction/Gen/`, `E2E/HeadlineGen.lean`; report
`status/GEN.md`): the same headlines for forgers whose private randomness is `ds + unifSpec`,
`ds` any oracle spec with an `AnswerMeasure` and finite answer types (real probabilities), e.g.
`Reduction.Gen.slhdsa_bytes_suf_cmaG : sufAdvG ds A ≤ betaSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main`
and its linear form `slhdsa_bytes_suf_cma_linearG`; `E2E.rust_securityG`, `E2E.rust_pure_securityG`.
The right-hand advantages are in wrapper games (VCVio's experiments, adversaries over
`ds + unifSpec`; equal to VCVio's games on classical adversaries). Proved from the linear
headline by derandomising the `ds`-coins (`Reduction.Gen.IsLin.derand`); the existing theorems are
recovered as instances (`Reduction/Gen/Recover.lean`, `slhdsa_*_viaG`).

## What is and is not established

The security bound (`security_128s`) is for the scheme in which the tweakable hash, `H_msg` and
`PRF_msg` are three independent random oracles. The Rust code is related to that scheme by
identities of programs after the oracles are answered by the SHA-2 functions of FIPS 205 §11.2.1.
No theorem transfers that random-oracle bound to the SHA-256 instantiation; the standard-model
theorems above are separate results about the SHA-256 instantiation itself (SUF-CMA and
EUF-CMA, internal and external pure interface, under the listed hash assumptions). The Rust-level
statements assume the `Room` length bounds of `../lean/Slhdsa/Theorems.lean`, take seeds and
`addrnd` as inputs (sampling is the caller's obligation), and trust the Rust compiler and the
Aeneas extraction.
