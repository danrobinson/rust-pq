# Standard-model EUF-CMA reduction for SLH-DSA — final summary (phase 1)

**Superseded by `status/FINAL2.md`** (phase 2: PRF game on secret-key addresses — the game `skPrf` below is false at SHA2-128s —, table-free adversaries, FORS term DSPR + 3·TCR, SUF-CMA, external interface; per-function SM-TCR terms, twelve advantages). The theorems below are unchanged and still proved. Limitations 3, 4, 5, 6 and 8 below describe phase 1 only: they are lifted by `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_split` (`Reduction/HeadlineSplit.lean`).

Lean 4.36.0, project `security/`. Everything below is proved; no `sorry`, `axiom`, `native_decide`, `bv_decide`. Details: `REDUCTION_STATUS.md`; audits: `status/AUDIT.md`, `status/AUDIT2.md`.

## Theorems (verbatim)

Generic, `Reduction/Final.lean` (`vp : ValidatedParams`, `prims : Primitives vp.params`; `optRand : PublicKeyCore prims.core → ProbComp prims.Y` and `pkSeedDist : ProbComp prims.PkSeed` arbitrary; classes: `SampleableType` on `SkSeed`, `SkPrf`, `Y`; `DecidableEq` on `Y`, `PkSeed`, `AdrsKey`; `Inhabited Y`):

```lean
theorem slhdsa_euf_cma (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))
```

SLH-DSA-SHA2-128s, `Reduction/Instance128s.lean` (no hypothesis except the forger; `structural_128s` is proved):

```lean
theorem slhdsa_sha2_128s_euf_cma
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))
```

Attached to the Rust code, `E2E/Reduction.lean` (`vp`, `prims` are `Link.vp`, `Link.prims`; `bound` written out):

```lean
theorem standard_model_security (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    EndToEnd optRand pkSeedDist ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        (Reduction.skPrf vp prims).prfAdvantage (bPrf A) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsg A) +
        KeyedHash.ITSRAdvantage (bItsr A) +
        TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) +
        TweakableHash.SM_DT_TCR_Advantage (bTcr A) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) *
          TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
        TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
        TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A))
```

The right-hand side is `bound` (`Reduction/Steps.lean`) unfolded; `w - 2 = 14` at 128s (`E2E.w_sub_two`). `Forger vp prims optRand pkSeedDist = SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)`: any adaptive chosen-message adversary, no query or time bound. `EndToEnd` (`E2E/Main.lean`): the Rust `slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal` never panic and compute the deterministic cores of the same scheme `internalAlg vp prims optRand pkSeedDist` on FIPS encodings (under the `Room` length bound). `E2E.scheme_eq` (`rfl`) records that both libraries use the same scheme term.

Corollaries: `Reduction.slhdsa_euf_cma_uniform_seed` (`pkSeedDist := $ᵗ PkSeed`); `Reduction.slhdsa_euf_cma_resources`, `E2E.standard_model_resources` (query bounds below for a forger with at most `qs` signing queries).

## Games (problem instances in `Reduction/Basic.lean`, experiments are VCVio definitions)

- EUF-CMA: `SignatureAlg.unforgeableExperiment` at `internalAlg` (VCVio `SignatureAlg.lean:222`). Keygen, forger with logging signing oracle, verify, message never queried. Paper: EUF-CMA of SPHINCS+.
- PRF: `skPrf`; `PRFScheme.prfAdvantage` (`PRF.lean:130`). Distinguish `PRF(PK.seed, k, ADRS)`, `k` uniform, from a lazy random function. EC `SKG_PRF`.
- PRF_msg: `msgPrf`; same experiment for `PRF_msg(k, opt_rand, M)`. EC `MKG_PRF`.
- ITSR: `itsrProblem`; `KeyedHash.ITSRAdvantage` (`KeyedHash/ITSR.lean:109`). Target oracle returns a fresh uniform randomizer per input; win = non-target `(R*, x*)` whose `k` FORS leaf indices are all covered by targets. HK22 Def. 9, EC `MCO_ITSR`.
- SM-DT-OpenPRE(F): `forsOpenPreProblem`; `SM_DT_OpenPRE_SourceFinalValidity.advantage` (`TweakableHash/SMDTOpenPREFinalValidity.lean:161`). Commit distinct tweaks, one uniform hidden input each, images and seed revealed, opening oracle; win = preimage of an unopened image. Cap `2^h·k·2^a`. BDHMS Fig. 10/11, EC `FP_OpenPRE`.
- SM-TCR(Thash): `tcrProblem`; `SM_DT_TCR_Advantage` (`TweakableHash/SMDTTCR.lean:133`). Adaptive `(tweak, msg)` targets with distinct tweaks while the seed is hidden; win = different message, same hash, at a target tweak. Cap = all hash calls of the key structure. HK22 Def. 2/7; merges four EC TCR games.
- SM-UD(F): `wotsUdProblem`; `SM_DT_UD_Advantage` (`TweakableHash/SMDTUD.lean:230`). `F(t, x)` for uniform `x` versus uniform output; collection oracle `Thash`. Cap `#inst·len`. HK22 Def. 4/7, EC `FC_UD`.
- SM-PRE(F): `wotsPreProblem`; `SM_DT_PRE_Advantage` (`TweakableHash/SMDTPRE.lean:158`). Challenges `F(t, x)`, `x` uniform; win = a preimage of some target. Cap `#inst·len`. HK22 Def. 3/7, EC `FC_PRE`.
- SM-TCR(F): `wotsTcrProblem`; `SM_DT_TCR_Advantage`. As SM-TCR, on `F`, with collection. Cap `#inst·len·w`. EC `FC_TCR`.

All games draw the seed from `pkSeedDist`. Every game can be lost and, on a toy bundle, won (`Reduction/NonVacuity.lean`, now including `prfMsgTester_adv`/`toy_prfMsg` and `wotsTcrCollider_adv_one`/`toy_wotsTcr`).

## Reduction adversaries (each runs the forger exactly once; `qs` = signing queries of `A`)

- `bPrf A` (`PRFHop.lean`): PRF. Samples `PK.seed`, `SK.prf`, `opt_rand`. At most `2^h'·len + qs·(k·2^a + d·2^h'·len)` oracle queries (`17920 + qs·182784` at 128s): `bPrf_queryBound_exact`.
- `bPrfMsg A` (`PRFMsgHop.lean`): PRF_msg. Samples `PK.seed`, table, `opt_rand`. At most `qs` queries: `bPrfMsg_queryBound`.
- `bItsr A` (`ITSR.lean`): ITSR. Samples `PK.seed`, table, `opt_rand`. At most `qs` targets: `bItsr_queryBound`.
- `bOpenPre A` (`OpenPRE.lean`): SM-DT-OpenPRE(F). Samples table, `opt_rand`, lazy `R`. Commits exactly the `2^h·k·2^a` FORS leaf tweaks (`14·2^75 ≈ 2^78.81` at 128s), distinct: `forsLeafKeys_nodup_length`; no opening refused: `op_initSt_initial`, `op_sign_run`.
- `bTcr A` (`TCR.lean`): SM-TCR(Thash). Samples table, `opt_rand`, lazy `R`. Exactly `tcrTargets` targets (`≈ 2^79.81` at 128s) with distinct tweaks: `honestCalls_nodup_length`; none refused: `bTcr_choose_run`.
- `bWots A` (`WotsEmbed.lean`): internal WOTS game (not in the statement). Signs each WOTS+ instance once: `chooseBody_run`.
- `rUd (bWots A)` (`WotsUD.lean`): SM-UD(F). Samples hybrid index and some chain starts. At most `#inst·len` challenges: `Resources.rUd_challenges_le`, `rUd_challenges_le_cap` (per run, any `W`); collection queries and uniform samples are not bounded without a bound on `W`.
- `rPre (bWots A)` (`WotsFinal.lean`): SM-PRE(F). At most `#inst·len` challenges: `Resources.rPre_challenges_le`, `rPre_challenges_le_cap`.
- `rTcr (bWots A)` (`WotsFinal.lean`): SM-TCR(F). At most `#inst·len·(w−1)` targets: `Resources.rTcr_targets_le`, `rTcr_targets_le_cap`.

Choice-freeness (audit M1): no choice principle occurs in the definition of any adversary. This is weaker than explicit/efficient: `sampleTable` draws `2^256` values and `structureVia` iterates over `2^63` bottom positions and `≈ 2^54` XMSS trees. Checked by `scratch/ChoiceCheck.lean` (follows definition bodies, never proofs): all nine adversaries, `sampleTable`, `structureVia` are choice-free; the old `Fintype.mPi` is flagged.

## Unconditional

The theorems have no cryptographic hypothesis: the inequality holds for every forger. `Structural` (injective encodings, address widths) is proved at 128s. The reductions are choice-free, black-box, straight-line, single-run, with proved target caps (exponential in `h`: `2^68`–`2^80` at 128s), and the bound is tight in advantage (coefficient 1 except `w − 2` on SM-UD); no claim on running time.

## Limitations

1. The eight right-hand advantages are not bounded. That they are small for the SHA-256-based `PRF`, `PRF_msg`, `H_msg`, `Thash` is an unproven assumption.
2. No running-time claim. As written five adversaries sample an eager `2^256` table; `Reduction/Lazy/` removes it (lazy for `bPrfMsg`, `bItsr`; sparse for the SM adversaries). The five SM adversaries still evaluate the whole key structure (`≈ 2^79.81` `Thash` evaluations at 128s), which is inherent in games whose targets are fixed before the seed is revealed.
3. One SM-TCR assumption on the variable-arity `Thash` (cross-arity collisions count, cap = all hash calls), stronger than the paper's four per-function games.
4. SM-DT-OpenPRE on `F` is assumed, not reduced to SM-TCR + SM-DSPR.
5. EUF-CMA, not SUF-CMA; single key.
6. Internal algorithms (FIPS 205 Alg. 18–20, messages `M'`). No security theorem for the external pure/pre-hash interfaces; `E2E.rust_sign`/`rust_verify` only show the Rust pure interface is that wrapper.
7. Sampling of `SK.seed`, `SK.prf`, `PK.seed`, `opt_rand` is the caller's obligation; `pkSeedDist` must be near uniform for the assumptions to be plausible. Rust compiler, Aeneas extraction, side channels are outside.
8. `qs` is not in the bound; no `≤ k·qs` lemma for the openings of `bOpenPre`; no lemma that the left side can be positive.

## Build

```
cd security && export PATH=$HOME/.elan/bin:$PATH && lake build
```

Default targets are now `Link`, `E2E`, `Reduction` (7600 jobs). With dependencies (Mathlib, VCVio, Aeneas, `Spec`, `Slhdsa`) built, rebuilding the three libraries from scratch took 29 s wall (84 s CPU) on a 36-core machine.

`#print axioms` output from that build:

```
'Reduction.slhdsa_euf_cma' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_euf_cma_uniform_seed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_euf_cma_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.structural_128s' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_sha2_128s_euf_cma' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.standard_model_security' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.standard_model_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Comparison with the paper

HK22 Thm 1 (recalled from `status/AUDIT2.md`, not re-read) and EasyCrypt `EUFCMA_SPHINCS_PLUS` (ePrint 2024/910; `../.tools/formosa-slhdsa`, commit `d2d4d032f4660525bc41e45e06f1aef44cd3a827`, `proofs/SPHINCS_PLUS.ec:4339`, read-only): PRF + PRF_msg + ITSR + max(0, DSPR − SPprob) + 3·TCR(F, FORS) + TCR(FORS tree) + TCR(FORS roots) + (w−2)·UD(F) + TCR(F, chains) + PRE(F) + TCR(WOTS pk) + TCR(XMSS tree).

- Same: PRF, PRF_msg, ITSR, and the WOTS+ terms (w−2)·UD + PRE + TCR on `F` with the same coefficients; whole-structure target counts; EUF-CMA; standard model; black-box straight-line reductions.
- Weaker here: the FORS-leaf term is SM-DT-OpenPRE (not DSPR + 3·TCR); the four tree/compression TCR terms are one cross-arity TCR term; no running-time statement (the paper's reductions cost about one key-structure evaluation: `1062560399506556770327551 ≈ 2^79.81` `Thash` calls and `≈ 2^78.81` secret values at 128s, `Resources.structHashEvals_128s`, `structPrfEvals_128s`; counts of the closed form, not of a program).
- Stronger here: the scheme is FIPS 205 Alg. 18–20 with the SHA2-128s bundle, tied to Rust code; arbitrary `pkSeedDist` and `optRand` (deterministic and hedged signing); `qs`-exact PRF query count.
