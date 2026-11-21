# Standard-model security of SLH-DSA — final summary, phase 2

> Superseded by `status/FINAL3.md` (phase 3: byte-level schemes, tight caps, class adversaries without structure recomputation, linear form, uniform-seed corollaries). Everything below remains proved; module counts and build figures below are those of phase 2.

Lean 4.36.0, project `security/`. Everything below is proved and in the default `lake build` (targets `Link`, `E2E`, `Reduction`); no `sorry`, `axiom`, `native_decide`, `bv_decide`. Nothing is pending: the per-arity split of the `Thash` TCR term is closed (unconditional, lazy/sparse adversaries, SUF and EUF, internal and external) and is the headline. Phase-1 summary: `status/FINAL.md` (superseded, statements still proved). Details: `REDUCTION_STATUS.md`.

## Theorems (verbatim; `Reduction/HeadlineSplit.lean`)

Context: `vp : ValidatedParams`, `prims : Primitives vp.params`; `optRand : PublicKeyCore prims.core → ProbComp prims.Y`, `pkSeedDist : ProbComp prims.PkSeed` arbitrary; classes `SampleableType` on `SkSeed`, `SkPrf`, `Y`; `DecidableEq` on `Y`, `PkSeed`, `AdrsKey`; `Inhabited Y`; `Fintype Y` (only to state SM-DSPR). `Structural vp prims` is non-cryptographic (injective encodings, address widths), proved at SHA2-128s (`structural_128s`). `Forger … = SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)`; `realAlg` is an `abbrev` of `internalAlg` (same term, `E2E.scheme_eq : … := rfl`).

```lean
noncomputable def boundFinalSplit pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈ : ℝ≥0∞ :=
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ + KeyedHash.ITSRAdvantage B₃ +
    (SM_DT_DSPR_SourceFinalValidity.advantage D + 3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
    (SM_DT_TCR_Advantage C₁ + SM_DT_TCR_Advantage C₂ + SM_DT_TCR_Advantage C₃ + SM_DT_TCR_Advantage C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ + SM_DT_PRE_Advantage B₇ + SM_DT_TCR_Advantage B₈
  -- Cᵢ : SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist n), n = 1, 2, vp.params.len, vp.params.k

theorem slhdsa_suf_cma_final_split (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalSplit pkSeedDist (bPrfWC sufCheck S.toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck S.toUnforgeableAdversary) (Lazy.bItsrL S.toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS S.toUnforgeableAdversary)) (toTcr (Lazy.bOpenPreS S.toUnforgeableAdversary))
        (bTcrArS 1 S.toUnforgeableAdversary) (bTcrArS 2 S.toUnforgeableAdversary)
        (bTcrArS vp.params.len S.toUnforgeableAdversary) (bTcrArS vp.params.k S.toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary)) (rTcr pkSeedDist (Lazy.bWotsS S.toUnforgeableAdversary))

theorem slhdsa_euf_cma_final_split (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalSplit pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
        (bTcrArS 1 A) (bTcrArS 2 A) (bTcrArS vp.params.len A) (bTcrArS vp.params.k A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A)) (rTcr pkSeedDist (Lazy.bWotsS A))

-- external pure interface (FIPS 205 Alg. 21/22/24); ExtForger / ExtStrongForger = (Strong)UnforgeableAdversary (externalAlg …)
theorem slhdsa_pure_euf_cma_final_split (hS) (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalSplit pkSeedDist (bPrfC (toInternal A)) (Lazy.bPrfMsgL (toInternal A)) …   -- as slhdsa_euf_cma_final_split at toInternal A
theorem slhdsa_pure_suf_cma_final_split (hS) (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalSplit pkSeedDist (bPrfWC sufCheck (toInternal S.toUnforgeableAdversary)) …  -- as slhdsa_suf_cma_final_split's bound at toInternal S.toUnforgeableAdversary
```

Also: `∀`-forms `slhdsa_{suf,euf}_cma_final_split'` (`betaSufFinalSplit`, `betaEufFinalSplit`); `final_split_resources`; 128s instances without hypothesis `slhdsa_sha2_128s_{suf,euf,pure_euf,pure_suf}_cma_final_split`. The unsplit theorems `slhdsa_{suf,euf,pure_euf,pure_suf}_cma_final` (`Reduction/Headline.lean`; bound `boundFinal` = the above with the four `Cᵢ` terms replaced by one cross-arity `SM_DT_TCR_Advantage (Lazy.bTcrS A)` on `tcrProblem`), `slhdsa_euf_cma_final_of_suf`, `E2E/Final.lean` remain proved. Neither bound implies the other term by term.

Attached to the Rust code (`E2E/FinalSplit.lean`; `vp`, `prims` = `Link.vp`, `Link.prims`; names opened from `Reduction`, `Reduction.Lazy`, `TweakableHash`; `w − 2 = 14`, `len = 35`, `k = 14`):

```lean
theorem standard_model_security_split optRand pkSeedDist :
    EndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
        (Reduction.skPrfC vp prims).prfAdvantage (bPrfWC sufCheck S.toUnforgeableAdversary) +
        (Reduction.msgPrf vp prims).prfAdvantage (bPrfMsgWL sufCheck S.toUnforgeableAdversary) +
        KeyedHash.ITSRAdvantage (bItsrL S.toUnforgeableAdversary) +
        (SM_DT_DSPR_SourceFinalValidity.advantage (toDspr (bOpenPreS S.toUnforgeableAdversary)) +
          3 * SM_DT_TCR_SourceFinalValidity.advantage (toTcr (bOpenPreS S.toUnforgeableAdversary))) +
        (SM_DT_TCR_Advantage (bTcrArS 1 S.toUnforgeableAdversary) + SM_DT_TCR_Advantage (bTcrArS 2 S.toUnforgeableAdversary) +
          SM_DT_TCR_Advantage (bTcrArS 35 S.toUnforgeableAdversary) + SM_DT_TCR_Advantage (bTcrArS 14 S.toUnforgeableAdversary)) +
        ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage (rUd pkSeedDist (bWotsS S.toUnforgeableAdversary)) +
        SM_DT_PRE_Advantage (rPre pkSeedDist (bWotsS S.toUnforgeableAdversary)) +
        SM_DT_TCR_Advantage (rTcr pkSeedDist (bWotsS S.toUnforgeableAdversary))) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ <the same twelve terms with bPrfC A, bPrfMsgL A, and A for S.toUnforgeableAdversary>

theorem pure_standard_model_security_split optRand pkSeedDist :
    PureEndToEnd optRand pkSeedDist ∧
    (∀ S : SignatureAlg.StrongUnforgeableAdversary (externalAlg vp prims optRand pkSeedDist), strongUnforgeableAdvantage … S ≤
        <the twelve SUF terms at toInternal S.toUnforgeableAdversary>) ∧
    ∀ A : SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist), unforgeableAdvantage … A ≤
        <the twelve EUF terms at toInternal A>

theorem tcr_split_targets_128s optRand pkSeedDist A :   -- choose run of bTcrArS n A; target counts 533756792467910173399552, 528785142244921151848447, 9241421688590303744, 9223372036854775808
theorem standard_model_resources_final optRand pkSeedDist A qs (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    Reduction.FinalResources A qs (Reduction.counts128s qs)
theorem pure_standard_model_resources_final … :   -- toInternal A makes ≤ qs queries ∧ FinalResources (toInternal A) qs (counts128s qs); both in E2E/Final.lean
```

`EndToEnd` (`E2E/Main.lean`): the Rust `slh_keygen_internal`, `slh_sign_internal`, `slh_verify_internal` never panic and compute the deterministic cores of `internalAlg …` on FIPS encodings. `PureEndToEnd` (`E2E/External.lean`): the same for `slh_sign`, `slh_verify` and `externalAlg …` (signing returns `none` exactly when the context exceeds 255 bytes). In the files every term is written out; the `<…>` above abbreviate only this summary.

## Games (experiments are VCVio definitions under `VCVio/CryptoFoundations/`; all draw `PK.seed` from `pkSeedDist`)

- SUF-CMA / EUF-CMA: `SignatureAlg.strongUnforgeableExperiment` / `unforgeableExperiment` (`SignatureAlg.lean:338,222`) at `internalAlg` or `externalAlg`. Keygen; forger with logging signing oracle; verify; SUF: the output pair was never returned; EUF: the message was never queried. External: messages are `(message, context)` pairs, signatures `Except External.Error Sig`; an error value (over-long context) is never accepted (`externalAlg_verify_error`), so it is never a forgery.
- **PRF on secret-key addresses (new)**: `skPrfC` (`Reduction/PrfDomain.lean`), `PRFScheme.prfAdvantage`. Distinguish `(PK.seed, a) ↦ PRF(PK.seed, k, a)`, `k` uniform, from a lazy random function, with `a : SkAdrs vp = {a // isCanonical ∧ type ∈ {WOTS_PRF, FORS_PRF} ∧ layer < d ∧ tree < 2^((d−1)h')}`. HK22 PRF, EC `SKG_PRF`. The phase-1 game `skPrf` (all of `Adrs`) is false at 128s: `skPrf_broken_128s` (advantage `1 − 1/|Y|`, SHA-2 PRF is `0^n` outside the checked ADRSc domain). Non-vacuity: `prfC_const_adv_zero`, `toy_prfC`; on `SkAdrs` the 128s PRF is the genuine SHA-256 expression (`sha2PRFChecked_ok_128s`).
- PRF_msg: `msgPrf` (`Basic.lean`), same experiment for `PRF_msg(k, opt_rand, M)`. EC `MKG_PRF`.
- ITSR: `itsrProblem`, `KeyedHash.ITSRAdvantage` (`KeyedHash/ITSR.lean`). Target oracle returns a fresh uniform randomizer per input; win = non-target `(R*, x*)` whose `k` FORS indices are all covered. HK22 Def. 9, EC `MCO_ITSR`.
- **SM-DSPR(F) (new)**: `forsDsprProblem` (`ForsTightFinal.lean`), `SM_DT_DSPR_SourceFinalValidity.advantage` (`TweakableHash/SMDTDSPRFinalValidity.lean:127–167`). Seed hidden: select ≤ `2^h·k·2^a` `(tweak, input)` targets with distinct tweaks; seed revealed: output `(j, b)`; win iff `b = [target j has a second preimage under F]`. Advantage `= max 0 (Pr[DSPR] − Pr[SPprob])`, `SPprob` = same adversary, accept iff the selected target has a second preimage. HK22 Def. 5/7, EC `SMDTDSPR`. Non-vacuity `forsDspr_trivial_adv_zero`, `forsDsprGuesser_adv_one`, `toyInj_forsDspr`.
- **SM-TCR(F) at FORS leaves (new)**: `forsTcrProblem`, `SM_DT_TCR_SourceFinalValidity.advantage` (`SMDTTCRFinalValidity.lean:99–110`). Same selection; win = `m ≠ xⱼ` with equal `F` at tweak `j`. EC `SMDTTCR`. Non-vacuity `forsTcr_trivial_adv_zero`, `forsTcrCollider_adv_one`.
- **SM-TCR(F), SM-TCR(H), SM-TCR(T_len), SM-TCR(T_k) (new)**: `thashArityProblem vp prims pkSeedDist n`, `n = 1, 2, len, k` (`TcrSplitFinal.lean`), `SM_DT_TCR_Advantage` (`SMDTTCR.lean`, the experiment of the chain term below). Adaptive `(tweak, input)` targets with distinct tweaks, seed hidden; then seed revealed; win = a second input **of the same length `n`** colliding at a target tweak. The target function is `Thash` on inputs of exactly `n` blocks (type `{xs // xs.length = n}`), i.e. FIPS `F`, `H`, `T_len`, `T_k`: each is a genuine SM-TCR game on that function (at SHA2-128s all four are `Trunc(SHA-256(PK.seed ‖ pad ‖ ADRSc ‖ M))`, `M` of 1, 2, 35, 14 blocks). Collection oracle: all of `Thash` at non-target tweaks (EC `SM_DT_TCR_C`); cap `tcrTargets` for every class (the adversaries register fewer, see below; tight-cap games `thashArityProblemT`, W2). Non-vacuity `thashArity_trivial_adv_zero`, `thashArityCollider_adv_one`, `toy_thashArity`. Relation to the paper's four terms TCR(FORS tree), TCR(FORS roots), TCR(WOTS pk), TCR(XMSS tree): the split is by arity, so class 2 holds FORS-tree and XMSS-tree nodes together (one `H` term for the paper's two), class `len` = TCR(WOTS pk), class `k` = TCR(FORS roots), and class 1 is an extra `F` term absent from the paper at this place (targets: FORS leaves and chain steps). If two of `1, 2, len, k` coincide the same advantage is counted twice (not at 128s, `arities_injective_128s`).
- SM-UD(F) `wotsUdProblem` (`SMDTUD.lean`): `F(t, x)`, `x` uniform, versus uniform; cap `#inst·len`; EC `FC_UD`. SM-PRE(F) `wotsPreProblem` (`SMDTPRE.lean`): preimage of some target; EC `FC_PRE`. SM-TCR(F) `wotsTcrProblem`: cap `#inst·len·w`; EC `FC_TCR`. Non-vacuity of these and the phase-1 games: `Reduction/NonVacuity.lean`.

## Adversaries and resources (`qs` = signing queries of the forger `A`; `#inst = Σ_{j<d} 2^(h−j·h')`)

`Reduction.final_resources hS A qs hA : FinalResources A qs (counts vp qs)` and `final_resources_128s … : FinalResources A qs (counts128s qs)` gather the lemmas below (fields in brackets; its `tcr_*` fields describe `bTcrS A`, the program every `bTcrArS n A` runs); `final_split_resources` adds the `bTcrArS` row.

| adversary | game | proved count, closed form | 128s | source lemmas |
|---|---|---|---|---|
| `bPrfC A`, `bPrfWC sufCheck A` | PRF/SkAdrs | [prf, prfSuf] queries ≤ `2^h'·len + qs·(k·2^a + d·2^h'·len)`; no secret samples | `17920 + qs·182784` | `bPrfC_queryBound_exact`, `bPrfWC_queryBound_exact` |
| `Lazy.bPrfMsgL A`, `Lazy.bPrfMsgWL sufCheck A` | PRF_msg | [msg*, msgSuf*] queries ≤ `qs`; fresh draws ≤ same as PRF count; hash evals (keygen+sign) ≤ `keygenHashes + qs·signHashes` | `qs`; `17920 + qs·182784`; `269824 + qs·2007385` | `Lazy.bPrfMsgL_queryBound/_draws/_hashes`, `Lazy.bPrfMsgWL_*` |
| `Lazy.bItsrL A` | ITSR | [itsr*] targets ≤ `qs`; draws, hashes as above | same | `Lazy.bItsrL_queryBound/_draws/_hashes` |
| `Lazy.bOpenPreS A` (inside `toDspr`/`toTcr`) | — | [open_*] commits exactly the `2^h·k·2^a` FORS-leaf tweaks, distinct; 0 collection queries; openings ≤ `qs·k`; samples `#inst·len` | `528905046081400263933952 = 14·2^75 ≈ 2^78.81`; `14·qs`; `≈ 2^68.13` | `Lazy.bOpenPreS_targets/_pick_queryBound/_find_queryBound`, `Lazy.wotsSkIdx_length` |
| `toDspr B`, `toTcr B` (B = `bOpenPreS A`) | SM-DSPR(F), SM-TCR(F) | [dspr_targets, tcrF_targets] ≤ one target per committed tweak, ≤ `2^h·k·2^a` (any `B`); run `B.pick`, `B.find` once | `≤ 14·2^75` (reached) | `toDspr_targets`, `toTcr_targets`, `toTcr_choose_run`, `toTcr_forge`, `toDspr_guess` |
| `bTcrArS n A` = `TcrSplit.restrict (·.length = n) _ (Lazy.bTcrS A)` | SM-TCR on `F`/`H`/`T_len`/`T_k` | runs `bTcrS A` once (one sparse table, `2^h·k·2^a + #inst·len` samples; the forger once); after the seed reveal recomputes the whole key structure (exactly `tcrTargets` own hash evaluations); targets = exactly the arity-`n` hash calls of the key structure, `arityTargets vp n` = `2^h·(k·(2^a·[n=1] + (2^a−1)·[n=2]) + [n=k]) + #trees·(2^h'·(len·(w−1)·[n=1] + [n=len]) + (2^h'−1)·[n=2])`, distinct tweaks, none refused; the other `tcrTargets − arityTargets n` calls are collection queries; forwards `bTcrS`'s collision iff both inputs have arity `n` | `F`: `533756792467910173399552 ≈ 2^78.82`; `H`: `528785142244921151848447 ≈ 2^78.81`; `T_len`: `9241421688590303744 ≈ 2^63.003`; `T_k`: `2^63`; sum `= tcrTargets ≈ 2^79.81` | `bTcrArS_choose_run`, `bTcrArS_targets`, `honestCalls_countP`, `arityTargets_128s`, `E2E.tcr_split_targets_128s` |
| `Lazy.bWotsS A` | WOTS game (internal) | [wots_*] each instance signed at most once, all in `wotsInsts`; samples `2^h·k·2^a` | `9241421688590303744 ≈ 2^63.003` | `Lazy.bWotsS_choose_signed`, `bWotsS_sampleCount`, `Resources.wotsInsts_length_128s` |
| `rUd W`, `rPre W` (W = `bWotsS A`) | SM-UD(F), SM-PRE(F) | [ud, pre] challenges ≤ `#inst·len` in every run (any `W`) | `323449759100660631040 ≈ 2^68.13` | `Resources.rUd_challenges_le`, `rPre_challenges_le` |
| `rTcr W` | SM-TCR(F) | [tcrW] targets ≤ `#inst·len·(w−1)` | `4851746386509909465600 ≈ 2^72.04` | `Resources.rTcr_targets_le` |
| `toInternal A`, `toInternalS S` | external → internal | signing queries ≤ those of the external forger; no sampling | `≤ qs` | `toInternal_queryBound`, `toInternalS_queryBound` |

Poly(`qs`): PRF (game queries; its local hashing is not counted), PRF_msg, ITSR (queries, samples, hash evaluations). Not poly(`qs`): the nine SM adversaries; they walk the whole key structure and register `≈ 2^63`–`2^79` targets at 128s regardless of `qs`, because every SM game registers targets before `PK.seed` is revealed while the forger needs `PK.seed` first — the paper's reduction. VCVio has no cost model for local computation: counts are of oracle queries and samples, and of hash evaluations only for the three lazy adversaries (hashing modelled as queries). No running-time statement. Own hashing of the SM adversaries after the seed reveal (`Reduction/Resources2*.lean`, `status/W3.md`): each `bTcrArS n A` recomputes the whole key structure, exactly `tcrTargets ≈ 2^79.81` hash evaluations at 128s (`tcr_structure_exact`) — not small and not poly(`qs`); `toDspr/toTcr (bOpenPreS A)` `≤ 269839 + qs·1950028`; `rUd/rPre/rTcr (bWotsS A)` `≤ qs·121857 + {525, 560, 16800}` plus an argued tail. (Phase 3, `status/FINAL3.md`: the class adversaries `bTcrArM n A` of the final theorems do not recompute the structure.)

Definition-level check (`scratch/Final/FinalCheck.lean`, not in the build; follows definition bodies, never proofs; output `scratch/Final/FinalCheck.out`): `bPrfC`, `bPrfWC`, `sufCheck`, `Lazy.bPrfMsgL`, `Lazy.bPrfMsgWL`, `Lazy.bItsrL`, `Lazy.bOpenPreS`, `toDspr`, `toTcr`, `Lazy.bTcrS`, `bTcrArS`, `TcrSplit.restrict`, `TcrSplit.route`, `Lazy.bWotsS`, `rUd`, `rPre`, `rTcr`, `toInternal`, `toInternalS`, `Guarded.reduce`, `Guarded.reduceS`, `pureEncode` reach none of `Classical.choice`, `Classical.indefiniteDescription`, `Exists.choose`, `Classical.propDecidable`, `Fintype.equivFin`, `sampleTable`, `Tables.uniformTable`, `UniformSampler.sample`, `Fin.mOfFn`, `Fintype.mPi` ("flagged: []"). Controls: `bPrfMsg`, `bPrfMsgW`, `bTcr`, `bTcrAr` (phase-1, eager) are flagged `[sampleTable, Fin.mOfFn]`; `betaSufFinal`, `betaSufFinalSplit` (measures) are flagged for choice. The check is on the generic definitions; instance arguments are parameters.

## What was achieved

- **A** (`status/A*.md`). Canonical-domain PRF game `skPrfC` with exact advantage transfer (`prfAdvantageC_eq`; generic form `prfAdvantageC_eq_of`, new); lazy `bPrfMsgL`, `bItsrL` (equal advantage) and sparse-table `bOpenPreS`, `bTcrS`, `bWotsS`; `slhdsa_euf_cma_v2`; `Reduction/Resources.lean`. Stretch goal (poly(`qs`) SM reductions) not reachable: in VCVio's SM-TCR/PRE/UD/OpenPRE adversary types the target-registering phase has no access to `PK.seed`, the forger needs it, so all targets precede the forger's run (or one loses a `2^-h` guess); matches HK22/EC. This is read off the definitions, not a theorem.
- **B** (`status/B.md`). `forsOpenPre_le : OpenPRE(B) ≤ DSPR(toDspr B) + 3·TCR(toTcr B)` for every OpenPRE adversary, unconditional; used in all final theorems. **TCR split: closed** (`status/B.md`, `ARITY.md`; `TcrSplit.lean`, `TcrSplitFinal.lean`, `VerifyArity.lean`, `TcrSplitClosed.lean`, `HeadlineSplit.lean`). `verifyAritySound` (from `Structural` alone): a hash call made while verifying an arbitrary signature and an honest call at the same tweak have the same arity ∈ {1, 2, len, k}. Hence the collision event of `G2` is covered by the four class games: `brS_coll_split : Pr[G2WithS, evColl] ≤ Σ_n Adv(bTcrArS n A)`, used for SUF (`g2W_le_split`) and EUF (`stepTCR_split_sparse`). Exact: `Adv(bTcrArS n A) = Pr[bTcrS A wins by an arity-n collision]` (`bTcrArS_advantage_eq`). Not achieved: separate `H` terms for FORS and XMSS trees; removal of the extra `F` term; (per-class caps: done later, `TightCaps.lean`); `Adv(bTcrS A) ≤ Σ_n` as an inequality between advantages (false in general because of `bTcrS`'s fallback output; the split is at the event level, which is all the proof uses). Phase-1-level versions (`stepTCR_split'`, `slhdsa_euf_cma_fors_tight_tcr_split'`, eager `bTcrAr`) stay proved.
- **C** (`status/C1.md`, `C2.md`). External pure interface: `externalAlg`, `toInternal`, tight transfer; new here: SUF-CMA transfer `Guarded.strongUnforgeableAdvantage_le`, `toInternalS` (`ExternalSuf.lean`). SUF-CMA: `slhdsa_suf_cma` ported to the v2 games/adversaries: `bPrfWC` (`SufPrfV2.lean`), `Lazy.bPrfMsgWL` (`Lazy/SufMsgLazy.lean`, equal advantage), and the four `G2` branches redone at the table-free adversaries (`SufSparse.lean`: `g2W_le_g2BoundS`). No extra assumption for SUF.
- Integration: all modules in the roots (52 `Reduction` modules, `E2E.External`, `E2E.Final`, `E2E.FinalSplit`), no name clash; doc fixes of `A-docfixes.md` applied (comments only); phase-1 theorems marked superseded.

## Limitations

1. The twelve right-hand advantages are not bounded; smallness for the SHA-256-based functions is an unproven assumption. `SPprob` enters only through the truncated difference in the DSPR term.
2. No running-time claim; nine of twelve adversaries are infeasible (above). `bOpenPreS`/`bTcrS`/`bWotsS` read their sparse table by linear list lookup (list work not formalised). Own hash evaluations after the seed reveal are formal (W3): `≈ 2^79.81` for each class TCR adversary, poly(`qs`) for the others; the collection-query and own-sample counts of `rUd/rPre/rTcr` are counting arguments only. Hash counts of the lazy adversaries exclude the final verification and list work.
3. TCR terms are per arity, not per address type: one `H` term for FORS and XMSS trees, one extra `F` term (see Games); the class-game caps are `tcrTargets` and the chain SM-TCR(F) cap is `#inst·len·w` in these theorems; `slhdsa_*_cma_final_tight` (`Reduction/TightCapsHeadline.lean`, `status/W2.md`) restate them in games capped at `arityTargets vp n` and `#inst·len·(w−1)` with equal advantages. The four class adversaries each re-run the whole collision finder and each recompute the key structure after the reveal (two structure evaluations per class adversary).
4. SUF and EUF bounds use different PRF/PRF_msg distinguishers (first two summands not comparable term by term). No lemma that the left sides can be positive.
5. Single key. External: pure mode only (no pre-hash, no mixed use of one key); game of these theorems on typed keys/signatures (byte-string games and their Rust attachment: `Reduction/Bytes.lean`, `E2E/Bytes.lean`, `status/W1.md`); the external transfer is `≤`, not `=`.
6. Sampling of `SK.seed`, `SK.prf`, `PK.seed`, `opt_rand` is the caller's obligation; `pkSeedDist` must be near uniform for the assumptions to be plausible. Rust compiler, Aeneas extraction, side channels are outside. `Room` length bounds on the Rust statements.
7. `skPrfC`'s domain is a superset of the honest addresses (key-pair/chain/index words unconstrained beyond 4 bytes). SHA-256 is modelled past the 2^64-bit length limit (`A-prf.md`).

## Build

`cd security && export PATH=$HOME/.elan/bin:$PATH && lake build` — 7672 jobs, success. Wall time: 43.9 s (148 s user CPU; a second run gave 44.3 s) for a from-scratch rebuild of our three libraries (`.lake/build/lib/lean/{Link,E2E,Reduction}*` and the matching `ir` directories deleted; 75 modules: 16 `Link`, 6 `E2E`, 53 `Reduction` including roots; dependencies Mathlib/VCVio/Aeneas/`Spec`/`Slhdsa` prebuilt; a 36-core machine). Source check: no `sorry`, `axiom `, `native_decide`, `bv_decide` in `Link/`, `E2E/`, `Reduction/` outside three comments that say "no `native_decide`" (`Link/Security.lean:136`, `Reduction/Resources.lean:13`, `Reduction/TightCaps.lean:28`). Check script: `lake env lean scratch/Final/FinalCheck.lean` (`scratch/` contains only that file, its output, and package A's earlier `scratch/A/EagerCheck.lean`).

```
'Reduction.slhdsa_suf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_euf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_pure_euf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_pure_suf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.final_resources' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_sha2_128s_suf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_sha2_128s_euf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_sha2_128s_pure_euf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Reduction.slhdsa_sha2_128s_pure_suf_cma_final_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.standard_model_security_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.pure_standard_model_security_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'E2E.tcr_split_targets_128s' depends on axioms: [propext, Classical.choice, Quot.sound]
```
(Every other theorem named here — `verifyAritySound`, `brS_coll_split`, `bTcrArS_choose_run`, `bTcrArS_targets`, `arityTargets_128s`, `final_split_resources`, the unsplit `*_final` theorems, `final_resources_128s`, `E2E.*_final` — prints the same three axioms.)

## Comparison with Hülsing–Kudinov / EasyCrypt

HK22 Thm 1 (as recalled in `status/AUDIT2.md`, not re-read) and EC `EUFCMA_SPHINCS_PLUS` (ePrint 2024/910, `../.tools/formosa-slhdsa`, commit `d2d4d032…`, `proofs/SPHINCS_PLUS.ec:4339`): PRF + PRF_msg + ITSR + max(0, DSPR − SPprob) + 3·TCR(F, FORS) + TCR(FORS tree) + TCR(FORS roots) + (w−2)·UD(F) + TCR(F, chains) + PRE(F) + TCR(WOTS pk) + TCR(XMSS tree).

- Same now: PRF, PRF_msg, ITSR; the FORS-leaf term `max(0, DSPR − SPprob) + 3·TCR(F)` with the same coefficients; (w−2)·UD + PRE + TCR on `F` for WOTS+; whole-structure target counts; black-box straight-line reductions; standard model.
- Same up to grouping: the tree/compression TCR terms are per function (`H`, `T_k`, `T_len`), but FORS-tree and XMSS-tree `H` are one term, not two.
- Still weaker here: an extra SM-TCR(`F`) term (class 1) in the collision branch; no running-time statement, and the four class TCR adversaries each cost two key-structure evaluations (one through oracle queries, one locally after the reveal; the paper: about one, `≈ 2^79.81` `Thash` calls at 128s).
- Stronger here: SUF-CMA (the paper and EC prove EUF-CMA) with no extra assumption; the external pure interface with context strings; the scheme is FIPS 205 Alg. 18–20 and 21/22/24 with the concrete SHA2-128s bundle, tied to Rust code; the PRF assumption is stated on the address domain where the concrete function is the real one; arbitrary `pkSeedDist`, `optRand` (deterministic and hedged); `qs`-explicit counts for the PRF (queries) and PRF_msg/ITSR adversaries (queries, samples, hash evaluations) and `≤ k·qs` openings.
