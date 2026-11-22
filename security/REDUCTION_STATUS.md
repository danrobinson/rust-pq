> **Note, 2026-11-22 (layout).** This document describes the single-set development as it stood in
> git commit `26aa3d8`. Since then the single-set `Link` files other than the Spec-free stand-ins of
> `Link/{Basic,Hash,Verify,Sha256}.lean` and `Link/Security.lean`, the `E2E` files other than
> `GuardedRom`/`CodedRom`, and `Ideal/Rust*.lean` are deleted; the six-set libraries `MLink`, `MReduction`,
> `ME2E`, `MIdeal` attach these results to the six-set Rust crate. `STATUS.md` is the current status;
> build commands below that name the deleted libraries are those of that commit (now: `lake build`).

# Standard-model reduction for SLH-DSA — final state (phase 3)

State: **complete; nothing pending.** `lake build Link E2E Reduction` (the default targets;
7702 jobs, 90 modules) succeeds. No `sorry`, `axiom`, `native_decide`, `bv_decide`.
`#print axioms` of every final theorem: `[propext, Classical.choice, Quot.sound]`.
Short summary for relaying, with the verbatim statements: `status/FINAL3.md`.

## 0. Final state after phase 3 (sections 1–10 below describe phases 1–2 and remain accurate for the theorems they name)

Final headline: `Reduction/HeadlineFinal.lean`, `E2E/Headline.lean`. It composes

| phase-3 package | content | files | report |
|---|---|---|---|
| W1 | byte-level schemes `bytesAlg`, `pureBytesAlg` (keys, messages, signatures are byte strings; cores `byteKeygen`, `byteSign`, `byteVerify`, `byteSignPure`, `byteVerifyPure`), generic transfer `Coded.View`/`reduce`, Rust functions pointwise equal to the cores | `Reduction/Bytes.lean`, `E2E/Bytes.lean` | `status/W1.md` |
| W2 | tight caps: `thashArityProblemT` (cap `arityTargets vp n`), `wotsTcrProblemT` (cap `#inst·len·(w−1)`), re-typed adversaries with equal experiments, `boundFinalTight` | `Reduction/TightCaps.lean`, `TightCapsHeadline.lean` | `status/W2.md` |
| W3 | direct resource lemmas at the headline terms, phase 1 / phase 2 separated, own hash evaluations after the seed reveal as hash queries of open programs; `FinalResourcesDirect` | `Reduction/Resources2*.lean` | `status/W3.md` |
| W5 | class adversaries `bTcrArM n A`: phase 1 of `bTcrArS n A`, phase 2 looks the collision up in the stored target list instead of recomputing the key structure; equal experiment; `≤ keygenHashes + qs·signHashes + 1 + 2·verifyHashes` own hashes | `Reduction/TcrMemo.lean`, `TcrMemoHeadline.lean` | `status/W5.md` |
| W6 | documentation sweep (comments/markdown) | — | `status/W6.md` |
| W7 | linear (signed-pair) form: named real/ideal probabilities, hop equalities, UD telescoping identity, untruncated DSPR step | `Reduction/Linear.lean`, `LinearBytes.lean` | `status/W7.md` |
| integration | byte level × tight caps × `bTcrArM`; uniform-seed deterministic/hedged corollaries; final resource bundle; Rust summaries | `Reduction/HeadlineFinal.lean`, `ResourcesFinal.lean`, `E2E/Headline.lean` | `status/FINAL3.md` |

Final theorems (statements verbatim in `status/FINAL3.md`):

- absolute-value form, bound `boundFinalTight` (twelve advantages) at the final adversaries
  `bPrfWC sufCheck`/`bPrfC`, `Lazy.bPrfMsgWL sufCheck`/`Lazy.bPrfMsgL`, `Lazy.bItsrL`,
  `toDspr`/`toTcr (Lazy.bOpenPreS ·)`, `bTcrArM 1/2/len/k`, `rUd`/`rPre`/`rTcrT pkSeedDist (Lazy.bWotsS ·)`:
  byte level `slhdsa_bytes_{suf,euf}_cma_final`, `slhdsa_pure_bytes_{suf,euf}_cma_final`
  (at `bytesToTyped(S)`, `toInternal (pureBytesToTyped ·)`); typed
  `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_memo`; the bound is equal to the phase-2 bound
  (`betaSufFinalMemo_eq_split`, `betaEufFinalMemo_eq_split`);
- linear form: `slhdsa_{suf,euf}_cma_final_linear(_explicit)`, `slhdsa_pure_{suf,euf}_cma_final_linear`,
  `slhdsa_{bytes,pure_bytes}_{suf,euf}_cma_linear`; it implies the absolute-value form
  (`boundFinalTight_of_linear`);
- uniform `PK.seed`, deterministic (`opt_rand = toY PK.seed`) and hedged (`opt_rand` uniform):
  `slhdsa_{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}`, and
  `slhdsa_sha2_128s_…` (at 128s `toY = SLHDSA.Concrete.sha2RandomizerOfPkSeed`, the identity);
- SHA2-128s: `slhdsa_sha2_128s_{bytes,pure_bytes}_{suf,euf}_cma_final`;
- Rust: `E2E.rust_security`, `E2E.rust_pure_security` (pointwise equalities ∧ SUF bound ∧ EUF
  bound, terms written out), `…_linear`, `…_deterministic`, `…_hedged`, `…_resources`; the doc
  comment of `E2E.rust_security` states the exact remaining gap (i)–(vi) between the scheme in
  the game and the Rust functions;
- resources: `final_resources_final`, `final_resources_final_external`,
  `final_resources_final_128s` (`FinalResourcesFinal`; table with formal/argued flags in the
  header of `Reduction/ResourcesFinal.lean`).

Caps old → final (128s): class games `tcrTargets = 1062560399506556770327551` →
`533756792467910173399552` (`F`), `528785142244921151848447` (`H`), `9241421688590303744`
(`T_len`), `9223372036854775808` (`T_k`); chain SM-TCR(F) `5175196145610570096640` →
`4851746386509909465600`; the FORS-leaf, UD and PRE caps were already equal to the proved usage.

What phase 3 changes in the limitations of section 7: 2 (own hashing after the seed reveal is
now counted, and is poly(`qs`) for every adversary of the final bound; argued-only items are
listed in `status/FINAL3.md` §7), 3 (caps are the per-class counts; the class adversaries no
longer recompute the structure, but still hash the forger's signatures locally because they
store `(tweak, input)` pairs, not hash values), 5 (the game is on byte strings). Not done:
answer-storing class adversaries; fixed-index SM-UD adversaries; linear forms of the older
headlines; per-address-type TCR split.

References: HK22 = Hülsing–Kudinov, ePrint 2022/346. BDHMS = Barbosa, Dupressoir, Hülsing,
Meijers, Strub, ePrint 2024/910; EC = its EasyCrypt artefact, clone at `../.tools/formosa-slhdsa`,
commit `d2d4d032f4660525bc41e45e06f1aef44cd3a827`, read-only blueprint (final lemma
`EUFCMA_SPHINCS_PLUS`, `proofs/SPHINCS_PLUS.ec:4339`). VCVio = `../.tools/VCVio-upstream`, commit
`a10530a`. Audits of phase 1: `status/AUDIT.md`, `status/AUDIT2.md`. Package reports:
`status/P0.md`–`P9.md` (phase 1), `status/A*.md`, `B.md`, `C1.md`, `C2.md`, `ARITY.md` (phase 2); `W1.md`–`W7.md` (phase 3).

## 1. History

Phase 1 (`Reduction/Final.lean`, `status/FINAL.md`): EUF-CMA of the internal algorithms,
`slhdsa_euf_cma`, bound `PRF + PRF_msg + ITSR + OpenPRE(F) + TCR(Thash) + (w−2)·UD + PRE + TCR(F)`.
Its defects, all repaired in phase 2:

| defect of phase 1 | repair | where |
|---|---|---|
| PRF game `skPrf` has oracle domain all of `Adrs`; false at SHA2-128s (`skPrf_broken_128s`, advantage `1 − 1/|Y|`) | game `skPrfC` on secret-key addresses `SkAdrs vp`; wrapper preserves the advantage exactly | `PrfDomain.lean`, `PrfDomainNonVacuity.lean`, `SufPrfV2.lean` |
| five adversaries sample an eager `2^256`-cell table | lazy (`bPrfMsgL`, `bItsrL`) and sparse (`bOpenPreS`, `bTcrS`, `bWotsS`) variants | `Lazy/*.lean` |
| no resource statements beyond three query bounds | closed forms, per-run counts, numerals at 128s | `Resources.lean`, `Headline.lean` (`final_resources`) |
| FORS leaves: SM-DT-OpenPRE assumed | `OpenPRE ≤ DSPR + 3·TCR` on `F`, unconditional | `ForsTight.lean`, `ForsTightFinal.lean` |
| EUF-CMA only | SUF-CMA, no extra assumption | `Suf*.lean`, `SufSparse.lean`, `Lazy/SufMsgLazy.lean` |
| internal algorithms only | external pure interface with context strings, EUF and SUF | `External.lean`, `ExternalSuf.lean` |
| overclaiming doc comments ("explicit", "tight") | corrected, comments only | `status/A-docfixes.md` |

The phase-1 theorems are unchanged, still proved, and marked superseded in their doc comments.

## 2. Final statements (`Reduction/Headline.lean`; headline with split TCR terms: section 8)

`vp : ValidatedParams`, `prims : Primitives vp.params`; `optRand`, `pkSeedDist` arbitrary; classes
`SampleableType` on `SkSeed`, `SkPrf`, `Y`; `DecidableEq` on `Y`, `PkSeed`, `AdrsKey`;
`Inhabited Y`; `Fintype Y` (to state SM-DSPR). `Structural vp prims` (`Basic.lean`): `ByteLaws`,
`KeyInjective`, `CanonicalAddressBounds`; non-cryptographic; `structural_128s` proves it at
`Link.vp`, `Link.prims`.

```lean
boundFinal pkSeedDist B₁ B₂ B₃ D T B₅ B₆ B₇ B₈ =
  (skPrfC vp prims).prfAdvantage B₁ + (msgPrf vp prims).prfAdvantage B₂ + KeyedHash.ITSRAdvantage B₃ +
  (SM_DT_DSPR_SourceFinalValidity.advantage D + 3 * SM_DT_TCR_SourceFinalValidity.advantage T) +
  SM_DT_TCR_Advantage B₅ + ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_Advantage B₆ +
  SM_DT_PRE_Advantage B₇ + SM_DT_TCR_Advantage B₈

theorem slhdsa_suf_cma_final (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinal pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A)) (Lazy.bTcrS A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A))          -- with A := S.toUnforgeableAdversary written out

theorem slhdsa_euf_cma_final (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinal pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A)
        (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A)) (Lazy.bTcrS A)
        (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A))
        (rTcr pkSeedDist (Lazy.bWotsS A))

theorem slhdsa_pure_euf_cma_final (hS) (A : ExtForger vp prims optRand pkSeedDist) :
    unforgeableAdvantage … A ≤ boundFinal … at toInternal A
theorem slhdsa_pure_suf_cma_final (hS) (S : ExtStrongForger vp prims optRand pkSeedDist) :
    strongUnforgeableAdvantage … S ≤ boundFinal … (SUF distinguishers) at toInternal S.toUnforgeableAdversary
theorem final_resources (hS) (A : Forger …) (qs) (hA : ∀ pk, IsQueryBoundP (A.main pk) (·.isRight = true) qs) :
    FinalResources A qs (counts vp qs)
```

Further: `slhdsa_euf_cma_final_of_suf`, `slhdsa_suf_cma_final'`, `slhdsa_euf_cma_final'`
(`∀`-forms with `betaSufFinal`, `betaEufFinal`), `slhdsa_suf_cma_final_resources`,
`slhdsa_pure_{euf,suf}_cma_final_resources`; at SHA2-128s without hypothesis:
`slhdsa_sha2_128s_{suf,euf,pure_euf,pure_suf}_cma_final`, `final_resources_128s`
(`counts128s`). `realAlg` is an `abbrev` for `internalAlg` (the SUF package states its theorems
with `realAlg`; same term).

Rust attachment (`E2E/Final.lean`, bounds written out term by term):
`E2E.standard_model_security_final` = `EndToEnd` ∧ SUF bound ∧ EUF bound for `internalAlg`;
`E2E.pure_standard_model_security_final` = `PureEndToEnd` ∧ SUF bound ∧ EUF bound for
`externalAlg`; `E2E.standard_model_resources_final`, `E2E.pure_standard_model_resources_final`.

## 3. Games

Left sides: VCVio `SignatureAlg.unforgeableExperiment` / `strongUnforgeableExperiment`
(`VCVio/CryptoFoundations/SignatureAlg.lean:222,338`) at `internalAlg`
(`HashSig/SLHDSA/Security/RomConformance.lean`) or `externalAlg` (`Reduction/External.lean`,
`= Guarded.scheme internalAlg pureEncode`; messages `(message, context)`, signatures
`Except External.Error Sig`, error values never verify).

| term | problem | experiment (VCVio) | in words | cap | paper |
|---|---|---|---|---|---|
| PRF | `skPrfC` (`PrfDomain.lean`) | `PRF.lean` `prfAdvantage` | distinguish `PRF(PK.seed, k, a)`, `k` uniform, from a lazy random function; `a : SkAdrs vp` (canonical, type WOTS_PRF/FORS_PRF, `layer < d`, `tree < 2^((d−1)h')`) | – | HK22 PRF, EC `SKG_PRF` |
| PRF_msg | `msgPrf` (`Basic.lean`) | same | same for `PRF_msg(k, opt_rand, M)` | – | EC `MKG_PRF` |
| ITSR | `itsrProblem` | `KeyedHash/ITSR.lean` | fresh uniform randomizer per target input; win = non-target `(R*, x*)` whose `k` FORS indices are covered | – | HK22 Def. 9, EC `MCO_ITSR` |
| SM-DSPR(F) | `forsDsprProblem` (`ForsTightFinal.lean`) | `TweakableHash/SMDTDSPRFinalValidity.lean` | select `(tweak, input)` targets (distinct tweaks) with seed hidden; guess whether target `j` has a second preimage; advantage `max 0 (Pr[DSPR] − Pr[SPprob])` | `2^h·k·2^a` | HK22 Def. 5/7, EC `SMDTDSPR` |
| SM-TCR(F), FORS | `forsTcrProblem` | `SMDTTCRFinalValidity.lean` | same selection; win = `m ≠ xⱼ`, equal `F` at tweak `j` | `2^h·k·2^a` | EC `SMDTTCR` |
| SM-TCR(Thash) (unsplit theorems only) | `tcrProblem` | `SMDTTCR.lean` | adaptive targets, distinct tweaks, seed hidden; win = collision at a target tweak | `tcrTargets` | HK22 Def. 2/7; merges four EC TCR games |
| SM-TCR(F), (H), (T_len), (T_k) (headline) | `thashArityProblem … n`, `n = 1, 2, len, k` (`TcrSplitFinal.lean`) | `SMDTTCR.lean` | same game on `Thash` restricted to inputs of exactly `n` blocks; win = second input of the same length; collection oracle = all of `Thash` at non-target tweaks | `tcrTargets` (tight: `arityTargets vp n`, `thashArityProblemT`, `TightCaps.lean`, equal advantage) | EC `SM_DT_TCR_C`; classes by arity: `H` = FORS-tree + XMSS-tree, `T_len` = WOTS pk, `T_k` = FORS roots, `F` extra |
| SM-UD(F) | `wotsUdProblem` | `SMDTUD.lean` | `F(t, x)`, `x` uniform, vs uniform; collection oracle `Thash` | `#inst·len` | HK22 Def. 4/7, EC `FC_UD` |
| SM-PRE(F) | `wotsPreProblem` | `SMDTPRE.lean` | preimage of some target `F(t, x)` | `#inst·len` | HK22 Def. 3/7, EC `FC_PRE` |
| SM-TCR(F), chains | `wotsTcrProblem` | `SMDTTCR.lean` | as SM-TCR, on `F`, with collection | `#inst·len·w` (tight: `#inst·len·(w−1)`, `wotsTcrProblemT`, equal advantage) | EC `FC_TCR` |

All games draw the seed from `pkSeedDist`. Non-vacuity (each game can be lost and, on a toy
bundle, won): `NonVacuity.lean`, `PrfDomainNonVacuity.lean`, `ForsTightNonVacuity.lean`.
Other seven games audited for out-of-domain artefacts: none (`status/A-prf.md`).
Intermediate, not in the statements: `g0`, `g1`, `g2`, `g2Class`, `expW`, `g2W`, `g2With`,
`g2WithS`, `WotsGame.hyb`, SM-DT-OpenPRE (`forsOpenPreProblem`).

## 4. Game sequence

```
real game, final check w (EUF: fresh message; SUF: pair never returned)
 │  PRF hop       ≤ Adv_PRF/SkAdrs(bPrfC A | bPrfWC w A)      secrets ← uniform table
 │  PRF_msg hop   ≤ Adv_PRF_msg(bPrfMsgL A | bPrfMsgWL w A)   R ← lazy random function of (opt_rand, M)
G2 (table = sparse table of the key structure; equal to the eager one)
 │  EUF: classify the forgery.  SUF: pair-fresh ⇒ classify; same randomizer ⇒ WOTS+ event or
 │       collision with an honest hash call (sameRandomizer_collision, deterministic)
 ├─ itsr     ≤ Adv_ITSR(bItsrL A)
 ├─ openpre  ≤ Adv_OpenPRE(bOpenPreS A) ≤ Adv_DSPR(toDspr ·) + 3·Adv_TCR(toTcr ·)
 ├─ tcr      ≤ Adv_TCR(bTcrS A)        [headline: collision event ≤ Σ_{n ∈ {1,2,len,k}} Adv_TCR_n(bTcrArS n A)]
 └─ wots     ≤ Pr[Hyb_0(bWotsS A)] ≤ (w−2)·Adv_UD(rUd W) + Adv_PRE(rPre W) + Adv_TCR(rTcr W)
```

EUF: `final_of_steps` at the lazy/sparse step lemmas (`FinalV2.lean`), then `forsOpenPre_le`.
SUF: `suf_le_prf_add_g2` (`Suf.lean`), `prfAdvantageC_bPrfWC`, `Lazy.prfAdvantage_bPrfMsgWL`,
`g2W_le_g2BoundS` (`SufSparse.lean`), `forsOpenPre_le`. External: `Guarded.unforgeableAdvantage_le`
/ `Guarded.strongUnforgeableAdvantage_le` (injectivity of `(ctx, M) ↦ 0x00 ‖ |ctx| ‖ ctx ‖ M`).

## 5. Adversaries and resources

`qs` = signing queries of the forger; `#inst = Σ_{j<d} 2^(h−j·h')`. All are black-box,
straight-line, run the forger once. `FinalResources A qs (counts vp qs)` (`final_resources`)
collects the counts; `counts128s` has the numerals.

| adversary (file) | game | proved counts | at 128s |
|---|---|---|---|
| `bPrfC`, `bPrfWC sufCheck` (`PrfDomain`, `SufPrfV2`) | PRF | queries ≤ `2^h'·len + qs·(k·2^a + d·2^h'·len)` | `17920 + qs·182784` |
| `Lazy.bPrfMsgL`, `Lazy.bPrfMsgWL sufCheck` (`Lazy/MsgLazy`, `Lazy/SufMsgLazy`) | PRF_msg | queries ≤ `qs`; draws ≤ PRF count; hashes ≤ `keygenHashes + qs·signHashes` | `qs`; `269824 + qs·2007385` |
| `Lazy.bItsrL` (`Lazy/ItsrLazy`) | ITSR | targets ≤ `qs`; draws, hashes as above | same |
| `toDspr`, `toTcr` of `Lazy.bOpenPreS` (`ForsTightFinal`, `Lazy/OpenPreSparse`) | SM-DSPR(F), SM-TCR(F) | commitments = `2^h·k·2^a` distinct tweaks = targets; openings ≤ `qs·k`; samples `#inst·len` (+ one input per target) | `14·2^75 ≈ 2^78.81`; `14·qs` |
| `Lazy.bTcrS` (`Lazy/TcrSparse`) | SM-TCR(Thash) | exactly `tcrTargets` targets, distinct, none refused; samples `2^h·k·2^a + #inst·len`; `forge` recomputes `honestCalls` (the whole key structure, exactly `tcrTargets` own hash evaluations) | `≈ 2^79.81`; `≈ 2^78.81` |
| `bTcrArS n` (`HeadlineSplit`) | SM-TCR on `F`/`H`/`T_len`/`T_k` | runs `bTcrS A` once; targets = the arity-`n` hash calls of the structure, `arityTargets vp n` (closed form), the others are collection queries; after the seed reveal it recomputes the whole key structure: exactly `tcrTargets` own hash evaluations (`Resources2.tcr_structure_exact`); the final theorems use `bTcrArM n` instead (same phase 1, no recomputation) | `≈ 2^78.82`, `≈ 2^78.81`, `≈ 2^63.003`, `2^63`; own hashes `≈ 2^79.81` each (`bTcrArM`: `≤ 269824 + qs·2007385 + 7857`) |
| `Lazy.bWotsS` (`Lazy/WotsSparse`) | WOTS game | each instance signed at most once; samples `2^h·k·2^a` | `#inst ≈ 2^63.003` |
| `rUd`, `rPre` (`WotsUD`, `WotsFinal`) | SM-UD(F), SM-PRE(F) | challenges ≤ `#inst·len` per run, any `W` | `≈ 2^68.13` |
| `rTcr` (`WotsFinal`) | SM-TCR(F) | targets ≤ `#inst·len·(w−1)` per run | `≈ 2^72.04` |
| `toInternal`, `toInternalS` (`External`, `ExternalSuf`) | wrapper | signing queries ≤ those of the external forger | `≤ qs` |

Polynomial in `qs`: the PRF, PRF_msg and ITSR adversaries (queries, samples and — for the lazy
ones, where hashing is modelled as oracle queries — hash evaluations of key generation and
signing). Not polynomial in `qs`: the SM adversaries (six in the unsplit bound, nine in the headline). They register all targets before
`PK.seed` is revealed (the SM games give the seed only to the second phase), the forger needs the
seed, hence the targets cover the whole key structure; this is the reduction of HK22/EC. VCVio
has no cost model for local computation, so there is no running-time statement. Own hash evaluations of the SM adversaries after the seed
reveal are counted in `Resources2*.lean` (`status/W3.md`) and `TcrMemo.lean` (`status/W5.md`):
`bTcrS`/`bTcrArS n` recompute the whole key structure (exactly `tcrTargets`, `≈ 2^79.81` at 128s —
not poly(`qs`)); the final class adversaries `bTcrArM n` do not (`≤ 269824 + qs·2007385 + 7857`);
FORS-leaf adversaries `≤ 269839 + qs·1950028`; chain adversaries `≤ qs·121857 + {525, 560, 16800}`
plus an argued tail. List work (sparse tables read by list lookup) and the size of the carried
state are not formalised; phase-1 "own hashing = 0" is by inspection, not a theorem. Bundle:
`final_resources_final` (`ResourcesFinal.lean`).

Definition-level check: `scratch/Final/FinalCheck.lean` (not in the build; follows definition
bodies, never proofs; output in `scratch/Final/FinalCheck.out`). All adversaries above and the
wrappers reach no choice principle and no eager object; the phase-1 `bPrfMsg`, `bPrfMsgW`, `bTcr`
are flagged for `sampleTable`/`Fin.mOfFn` (control); `bTcrArS`, `TcrSplit.restrict`, `TcrSplit.route`
are checked and clean, the eager `bTcrAr` is flagged (control). `scratch/A/EagerCheck.lean` is package A's
earlier version.

## 6. Files (`Reduction/` unless noted)

| file | content |
|---|---|
| `Basic`, `Games`, `WotsGame`, `Steps`, `Main`, `Harness`, `Tables` | problems and caps; `g0`–`g2`, `sampleTable`, `classify`; step statements, `bound`, `final_of_steps`; forger harness; uniform-table calculus |
| `PRFHop`, `PRFMsgHop`, `ITSR`, `OpenPRE`, `TCR`, `WotsSim`, `WotsEmbed`, `WotsUD`, `WotsFinal` | phase-1 adversaries `bPrf`, `bPrfMsg`, `bItsr`, `bOpenPre`, `bTcr`, `bWots`, `rUd`, `rPre`, `rTcr` and step lemmas `stepPRF` … `stepWotsFinal` |
| `Final`, `Instance128s`, `NonVacuity`, `E2E/Reduction` | phase-1 theorems `slhdsa_euf_cma`, `structural_128s`, `slhdsa_sha2_128s_euf_cma`; non-vacuity of the phase-1 games; `E2E.standard_model_security` (superseded) |
| `PrfDomain`, `PrfDomainNonVacuity` | `SkDom`, `SkAdrs`, `skPrfC`, `Restrict.restrictImpl`, `bPrfC`, `prfAdvantageC_eq`; `skPrf_broken_128s`, `sha2PRFChecked_ok_128s`, non-vacuity |
| `Lazy/Core`, `Lazy/Open` | open programs, lazy cache, lazy = eager, kind counting |
| `Lazy/MsgLazy`, `Lazy/ItsrLazy`, `Lazy/SufMsgLazy` | `bPrfMsgL`, `bItsrL`, `bPrfMsgWL`; advantage equalities; query/draw/hash bounds |
| `Lazy/Sparse`, `Lazy/OpenPreSparse`, `Lazy/TcrSparse`, `Lazy/WotsSparse` | `sparseOn`, `restrictTo`; `bOpenPreS`, `bTcrS`, `bWotsS`; sparse step lemmas; resources |
| `Resources` | closed forms, numerals at 128s, `rUd/rPre/rTcr` per-run counts |
| `FinalV2`, `Instance128sV2` | `slhdsa_euf_cma_v2` (intermediate) |
| `ForsTight`, `ForsTightFinal`, `ForsTightNonVacuity` | `openPRE_le_dspr_add_three_tcr`, `forsOpenPre_le`, `toDspr`, `toTcr`, resource lemmas, non-vacuity |
| `TcrSplit`, `TcrSplitFinal` | generic per-class TCR split (`restrict`, `choose_coupling`, `prEvent_le_sum_restrict`); `thashArityProblem`, eager `bTcrAr`, `stepTCR_split` etc. stated with the hypothesis `VerifyAritySound` |
| `VerifyArity`, `TcrSplitClosed` | `arityOf`, `honestCalls_map_arity`, `verifyCalls_arity`, `verifyAritySound` (the hypothesis, proved from `Structural`); unconditional phase-1-level split theorems |
| `HeadlineSplit` | `bTcrArS`, `brS_coll_split`, `stepTCR_split_sparse`, `g2W_le_split`, `boundFinalSplit`, the four `*_final_split` theorems and 128s instances, `arityTargets`, `bTcrArS_choose_run`, `bTcrArS_targets`, `arityTargets_128s`, `final_split_resources` |
| `SufCollision`, `SufHarness`, `SufHopPrf`, `SufHopMsg`, `Suf`, `SufInstance128s` | `sameRandomizer_collision`, hops for an arbitrary final check, `slhdsa_suf_cma` (phase-1 games) |
| `SufPrfV2`, `SufSparse` | `prfAdvantageC_eq_of`, `bPrfWC`; `g2WithS`, `brS_*`, `g2W_le_g2BoundS` |
| `External`, `ExternalSuf` | `Guarded.scheme/reduce/reduceS`, `externalAlg`, `toInternal(S)`, advantage transfers |
| `Headline` | `boundFinal`, the final theorems, `Counts`, `FinalResources`, `final_resources` |
| `E2E/External`, `E2E/Final`, `E2E/FinalSplit` | `PureEndToEnd`; final attachments to the Rust code (unsplit; headline with split TCR terms and `tcr_split_targets_128s`) |

## 7. Limitations

1. The right-hand advantages (twelve in the headline, nine unsplit) are not bounded; that they are small for the SHA-256-based
   functions is an unproven assumption.
2. No running-time statement; all SM adversaries are infeasible (section 5). The four
   class TCR adversaries `bTcrArS` also do `≈ 2^79.81` own hash evaluations each (section 5); the
   final ones (`bTcrArM`) do not. Not formal: collection queries and own samples of
   `rUd/rPre/rTcr` (counting arguments), the pure tail `wotsAnswer`, hash counts of
   `bPrfC`/`bPrfWC`, list work, the final verification of the lazy adversaries, `pkSeedDist`,
   `optRand`.
3. The TCR split is by arity, not by address type: one `H` term covers FORS-tree and XMSS-tree
   nodes, and an `F` term (FORS leaves, chain steps) appears that the paper does not have at this
   place; class-game caps are `tcrTargets` in `HeadlineSplit.lean` and the exact per-class counts in
   `TightCapsHeadline.lean` and the final theorems (equal advantages); each of the four class
   adversaries re-runs the whole forger simulation, and `bTcrArS` (not `bTcrArM`) recomputes the
   whole key structure after the seed reveal (section 8).
4. The SUF and EUF bounds use different PRF/PRF_msg distinguishers. No lemma that a left side
   can be positive.
5. Single key. External interface: pure mode only (no pre-hash, no mixed use of a key); the game
   of the theorems above is on typed signatures and keys (byte-string games:
   `Reduction/Bytes.lean`, `Reduction/HeadlineFinal.lean`, `E2E/Headline.lean`); the transfer is an inequality.
6. `skPrfC`'s domain is a superset of the honest secret-key addresses. For a degenerate
   `pkSeedDist` the theorems are true inequalities whose SM assumptions are false.
7. Sampling of seeds and `opt_rand` is the caller's obligation; Rust compiler, Aeneas
   extraction, side channels are outside; Rust statements under the `Room` length bounds.
8. `Tables.writeBlock` uses `Exists.choose`; it occurs only in lemmas, not in any adversary.

## 8. Headline: per-function TCR terms (`Reduction/HeadlineSplit.lean`, `E2E/FinalSplit.lean`)

```lean
boundFinalSplit pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈ =
  boundFinal with `SM_DT_TCR_Advantage B₅` replaced by
  (SM_DT_TCR_Advantage C₁ + SM_DT_TCR_Advantage C₂ + SM_DT_TCR_Advantage C₃ + SM_DT_TCR_Advantage C₄)
  -- Cᵢ : SM_DT_TCR_Adversary (thashArityProblem vp prims pkSeedDist n), n = 1, 2, len, k

theorem slhdsa_suf_cma_final_split (hS) (S) : strongUnforgeableAdvantage … S ≤
  boundFinalSplit pkSeedDist (bPrfWC sufCheck A) (Lazy.bPrfMsgWL sufCheck A) (Lazy.bItsrL A)
    (toDspr (Lazy.bOpenPreS A)) (toTcr (Lazy.bOpenPreS A))
    (bTcrArS 1 A) (bTcrArS 2 A) (bTcrArS vp.params.len A) (bTcrArS vp.params.k A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A)) (rTcr pkSeedDist (Lazy.bWotsS A))
    -- A := S.toUnforgeableAdversary
theorem slhdsa_euf_cma_final_split (hS) (A) : … ≤ boundFinalSplit … (bPrfC A) (Lazy.bPrfMsgL A) …
theorem slhdsa_pure_euf_cma_final_split, slhdsa_pure_suf_cma_final_split   -- at toInternal ·
theorem slhdsa_sha2_128s_{suf,euf,pure_euf,pure_suf}_cma_final_split      -- no hypothesis
theorem E2E.standard_model_security_split, E2E.pure_standard_model_security_split, E2E.tcr_split_targets_128s
```

How it is proved. `verifyAritySound` (`VerifyArity.lean`, from `Structural`): a hash call of the
verification of an arbitrary signature and an honest call at the same tweak have the same arity,
one of `1, 2, len, k` (arity is a function `arityOf` of the address; tweak encoding injective on
the ledger). `TcrSplit.restrict P d B` turns any SM-TCR adversary `B` on `Thash` into one for the
class `P`: it runs `B.choose` once, sends accepted class-`P` targets to the challenge oracle and
the others to the collection oracle, runs `B.forge` once and forwards the answer iff both inputs
are in `P`; `restrict_advantage_eq`: its advantage equals `Pr[B wins by a class-P collision]`.
`bTcrArS n A := restrict (·.length = n) _ (Lazy.bTcrS A)`. `brS_coll_split`: the collision event
`evColl` of `G2` (sparse table) has probability `≤ Σ_n Adv(bTcrArS n A)`; this replaces `brS_coll`
in the SUF union bound (`g2W_le_split`) and, with `g2Class_tcr_le_coll`, `stepTCR_sparse` in the
EUF composition (`final_of_steps_tcr`). The inequality `Adv(bTcrS A) ≤ Σ_n Adv(bTcrArS n A)` is
not claimed (the fallback answer `(0, [])` of `bTcrS` could win across arities); the split is at
the event level, which is all the theorems use.

Class games (`thashArityProblem`, VCVio `SM_DT_TCR_Problem`/`SM_DT_TCR_Experiment`): each is a
genuine SM-TCR game on `Thash` restricted to inputs of exactly `n` blocks — FIPS `F` (`n = 1`),
`H` (`2`), `T_len`, `T_k` — with a collection oracle for all of `Thash` at non-target tweaks and
cap `tcrTargets`. Relation to the paper's four terms: `H` covers FORS-tree and XMSS-tree nodes
together (the paper has two `H` terms); `T_len` = TCR(WOTS pk); `T_k` = TCR(FORS roots); the `F`
class (FORS leaves and chain steps as targets) has no counterpart at this place in the paper. If
two of `1, 2, len, k` coincide the same advantage is counted twice (not at 128s).

Resources: `bTcrArS_choose_run` (one run of `bTcrS A`'s `choose`; final class-game state =
`gState` of the honest calls), `bTcrArS_targets` + `honestCalls_countP` (targets = exactly the
arity-`n` calls, `arityTargets vp n`; others are collection queries; total `tcrTargets`),
`arityTargets_128s`: `533756792467910173399552`, `528785142244921151848447`,
`9241421688590303744`, `9223372036854775808`, sum `= tcrTargets`. `final_split_resources`.

Phase-1-level versions (eager `bTcrAr`; `TcrSplitFinal.lean`, `TcrSplitClosed.lean`) stay proved.

## 9. Comparison

HK22 Theorem 1 (as recalled in `status/AUDIT2.md` §5) and EC `EUFCMA_SPHINCS_PLUS`: PRF + PRF_msg
+ ITSR + max(0, DSPR − SPprob) + 3·TCR(F, FORS leaves) + TCR(FORS tree hash) + TCR(FORS root
compression) + (w−2)·UD(F) + TCR(F, chains) + PRE(F) + TCR(WOTS pk compression) + TCR(XMSS tree).

| aspect | HK22 / EC | here |
|---|---|---|
| FORS leaves | DSPR + 3·TCR on `F` | same terms, same coefficients |
| WOTS chains | (w−2)·UD + TCR + PRE on `F` | same |
| tree / compression hashes | four SM-TCR terms: FORS tree, FORS roots, WOTS pk, XMSS tree | four SM-TCR terms by arity: `H` (FORS + XMSS trees together), `T_k`, `T_len`, and an extra `F` term |
| PRF | on the scheme's addresses | on `SkAdrs vp` (superset of honest addresses) |
| notion | EUF-CMA | SUF-CMA and EUF-CMA |
| interface | abstract SPHINCS+ | FIPS 205 internal (Alg. 18–20) and external pure (Alg. 21/22/24) |
| instance | abstract tweakable hashes | SHA2-128s bundle, `Structural` proved, tied to Rust code |
| seed / randomizer | uniform `PK.seed` | arbitrary `pkSeedDist`, `optRand` |
| target counts | whole key structure | same (exact counts proved) |
| reduction cost | ≈ forger + one key-structure evaluation | query/target/sample counts and post-seed hash-evaluation bounds proved; the class TCR adversaries evaluate the key structure once through their oracles (`bTcrArS` a second time locally; `bTcrArM` not); no running-time statement |
| proof assistant | EasyCrypt | Lean 4.36 + Mathlib + VCVio; axioms `propext, Classical.choice, Quot.sound` |

## 10. How to check

```
cd security && export PATH=$HOME/.elan/bin:$PATH
lake build                                   # Link, E2E, Reduction
lake env lean scratch/Final/FinalCheck.lean  # definition-level check of the adversaries
```

Modules: 16 `Link`, 8 `E2E`, 66 `Reduction` (roots included); 7702 jobs. Build times on a
36-core machine and how they were measured: `status/FINAL3.md` §8 (45.4 s for the integration
build of 44 modules; 72.7 s wall for an isolated from-scratch compile of all 90 modules under
concurrent load). Phase 2 figure: 43.9 s for a from-scratch rebuild of the then 75 modules.
`#print axioms` lines are at the end of `Reduction/HeadlineFinal.lean`, `E2E/Headline.lean`, `Reduction/HeadlineSplit.lean`, `E2E/FinalSplit.lean`,
`Reduction/Headline.lean`, `E2E/Final.lean` (and of every package file).

## 11. Forgers over a general sampling spec (package GEN; `Reduction/Gen/`, `E2E/HeadlineGen.lean`)

Added after phase 3; nothing above is changed (only imports were appended to `Reduction.lean`,
`E2E.lean`). Full report with verbatim statements: `status/GEN.md`; interface for `quantum/`:
`status/GEN-interface.md`.

- **What.** The final headlines (SUF and EUF; typed and byte-level; internal and external pure;
  linear and absolute-value; tight caps, memoising adversaries; E2E forms) for forgers whose private
  randomness is `ds + unifSpec`, `ds` any oracle spec with an `AnswerMeasure` and finite answer
  types (e.g. quantum's `distSpec`, real probabilities). Forger type: VCVio's
  `(Strong)UnforgeableAdversary (liftAlg ds alg)`; advantage `eufAdvG`/`sufAdvG` =
  `𝒟[VCVio's experiment] {true}`. Theorems `Reduction.Gen.slhdsa_{,pure_}{,bytes_}{euf,suf}_cmaG`,
  `…_cma_linearG`, `slhdsa_sha2_128s_*G`, `E2E.rust_securityG`, `rust_pure_securityG`, `…_linearG`.
- **Right-hand side.** The twelve advantages in WRAPPER games (`Gen/Game{Prf,Itsr,Tcr,Wots,FV}.lean`:
  VCVio's experiments with adversaries over `ds + unifSpec`; coincidence with VCVio's games on
  classical adversaries and non-vacuity proved for each) of the reduction adversaries around the
  forger (`bPrfCG`, `bPrfWCG`, `bPrfMsgLG`, `bPrfMsgWLG`, `bItsrLG`, `toDsprG`, `toTcrG`, `bTcrArMG`,
  `rUdG`, `rPreG`, `rTcrTG`: the classical code, the forger's `ds`-queries forwarded).
- **Proof.** No hop is re-proved. Every term of the linear headline is a linear functional of the
  forger's program ("classical prefix; one run against a classical stateful handler; classical
  suffix", `IsLin`), and a linear inequality that holds for all forgers without `ds`-queries holds
  for all forgers (`IsLin.derand`, `Gen/Derand.lean`: fix an answer at every `ds`-query so as to
  minimise right minus left). So the general theorems are corollaries of
  `slhdsa_*_cma_final_linear`.
- **Recovery.** On embedded classical forgers both sides are the existing ones; sixteen theorems
  `slhdsa_*_viaG` (`Gen/Recover.lean`) have literally the types of the existing headline theorems.
- **Resources.** `final_resourcesG`, `final_resourcesG_128s` (`Gen/Resources*.lean`): the classical
  numerals for the general adversaries (pre-seed phases are the classical programs; post-seed hash
  bounds; query bounds), for a forger with at most `qs` signing queries.
- **Also.** `slhdsa_{euf,suf}_cma_resolved`: the general advantage is at most the EXISTING bound
  (VCVio's games) at a classical forger obtained by fixing the `ds`-coins (non-constructive).
- **Check.** `lake env lean scratch/Gen/GenCheck.lean` (76 definitions, no choice / eager tables);
  build: 7750 jobs. Not done: `ds` with infinite answer types; see `status/GEN.md` §9.

## Work package OPEN — hash evaluations as oracle queries (names for the quantum and ideal leads)

Request: `../quantum/STATUS.md` §0, R1–R7. Full report: `status/OPEN.md` (deviations, table, numerals; per-package
`status/OPEN-O*.md`). New files only, `Reduction/Open/*.lean`, namespace `Reduction.Open`; nothing existing changed.
`hA` = forger makes ≤ `qs` signing queries. Axioms: `[propext, Classical.choice, Quot.sound]` throughout.
Integrated: all `Reduction/Open/*.lean` are imported by `Reduction.lean`; `lake build Link E2E Reduction` green (7788 jobs).
Helper renames applied in the new files: `MsgV` `hashEmbR`/`embR`, `Tcr` `TcrForgerProg`, `Phase1Wots` `wotsTcrPhase1`.

- **R1 PRF distinguishers** (`HSpec.lean`, `Prf.lean`): `HSpec`, `PSpec`, `closeImpl`, `restrictO`; `bPrfOpen`,
  `bPrfWOpen wO`, `bPrfCOpen`, `bPrfWCOpen wO`, `sufCheckOpen`; `bPrfOpen_close`, `bPrfCOpen_close`,
  `bPrfWOpen_close` (hyp. `hw`), `bPrfWCOpen_close_suf` (`simulateQ (closeImpl …) (open) = bPrf/bPrfC/bPrfW/bPrfWC`);
  `bPrfCOpen_hashes`, `bPrfWCOpen_suf_hashes` (`keygenHashes + qs·signHashes + (1 + verifyHashes)`), `*_prfmsg`
  (`≤ qs`), `*_game`; `bPrfCOpen_hashes_128s`, `bPrfWCOpen_suf_hashes_128s` (`269824 + qs·2007385 + 3929`).
- **R2 `PRF_msg` distinguishers, ITSR** (`MsgV.lean`): `msgOpenV`, `msgOpenWV wO`, `sufCheckO`; `lazyRun_msgOpenV`
  (`= bPrfMsgL A`), `lazyRun_msgOpenWV_sufCheck` (`= bPrfMsgWL sufCheck A`), `lazyRun_msgOpenWV_of_eval`;
  `msgOpenV_hashes`, `msgOpenWV_suf_hashes`, `_game`, `_sec`, `lazyRes_…`; `msgOpenV_hashes_128s`;
  `bPrfMsgL_castForger`, `bPrfMsgWL_castForger`, `itsrOpen_castForger`, `bItsrL_castForger_main`.
- **R3 second phases** — FORS (`Fors.lean`): `forsFindOpen`, `forsRun`, `forsTcrPost`, `forsDsprPost`;
  `forsTcr_phase2_open_eq`, `forsDspr_phase2_open_eq`, `…_open_hashes(_128s)` (`269839 + qs·1950028`),
  `forsFindOpen_withTH`, `forsTcr/forsDspr_phase2_open_eq_withTH`. Class TCR (`Tcr.lean`): `tcrMOpen`,
  `tcrM_phase2_open_eq`, `tcrM_phase2_open_hashes(_128s)` (`269824 + qs·2007385 + 7857`), `classOut_withTH`,
  `tcrMOpen_withTH`, `tcrM_phase2_open_uniform`, `bTcrArM_phase2_open_uniform`. WOTS (`Wots.lean`):
  `wotsAnswerOpen` (`wotsAnswerOpen_tbl`, `wotsAnswerHashes_128s = 129714`), `wotsUdOpenAll`, `wotsPreOpenAll`,
  `wotsTcrOpenAll`; `wotsUd/wotsPre/wotsTcrT_phase2_open_eq`, `…_open_hashes(_128s)` (`qs·121857 + 130239 / 130274 /
  146514`), `wotsUd/Pre/TcrOpenAll_hashfree`.
- **R4 first phases** (`Phase1Fors.lean`, `Phase1Tcr.lean`, `Phase1Wots.lean`): `forsDspr/forsTcr_phase1_hashfree`,
  `tcrM_phase1_hashfree`, `wotsUd/wotsPre/wotsTcr/wotsTcrT_phase1_hashfree` (`withTH`, `castForger`); all four
  components, arbitrary forger: `forsDspr/forsTcr_phase1_withHash`, `tcrM_phase1_withHash`,
  `wots*_phase1_hashfree_all`; forger-free programs `forsPhase1`, `tcrPhase1`, `wotsTcrPhase1`, `udPhase1`, `prePhase1` with
  `toDspr_choose_eq`, `bTcrArM_choose_eq`, `wots*_phase1_q1_zero`, `forsDspr/forsTcr/tcrM_phase1_q1`. Caveat: the
  class-TCR and WOTS first phases query the game's collection oracle (the game's hashing, not the adversary's).
- **R5 wrappers** (`Wrappers.lean`): `toInternal_open`, `toInternalS_open`, `bytesToTyped(S)_open`,
  `pureBytesToTyped(S)_open`, `headline_bytes_open`, `headline_pureBytes_open`; programs `extProg`, `bytesProg`,
  `pureBytesProg` (`toInternal_main`, `bytesToTyped_main`, `pureBytesToTyped_main`, `headline_*_main`).
- **R6 bundle** (`Bundle.lean`): `FinalResourcesOpen A qs`, `final_resources_final_open A qs hA`,
  `final_resources_final_open_external`, `final_resources_final_open_bytes`, `FinalResourcesOpen128s`,
  `final_resources_final_open_128s`; `itsrOpen_hashes/_game/_sec` (`keygenHashes + qs·signHashes`;
  128s `269824 + qs·2007385`).
- **R7**: program-generic lemmas (`ForgerProg`, `TcrForgerProg`): `forsFindOpen_tbl`, `forsFindOpen_kindBound`, `tcrMForge_eq`,
  `wots*_phase2_open_eq_main`, `wotsForgeOpen_eq_main`; defined phases `forsTcrPhase2`, `forsDsprPhase2`, `tcrMForge`.
- **Counts now theorems** (`WotsCounts.lean`, `WotsCountsSM.lean`, `WotsCountsSamples.lean`): `rUd/rPre/rTcr/
  rTcrT_collection_le(_128s)`, `bWotsS_collection_le`, `wotsQc_closed`, `wotsQc_128s`,
  `rUd/rPre/rTcr/rTcrT_wrapper_samples_le`, `wrapper_samples_128s`. The three collection numerals are 1023 smaller
  than the argued ones of `status/FINAL3.md`/`W3.md` (`wotsQc = 1057708653120046860861951`; UD/PRE
  `1062560399506556770327551`; TCR `1058032102879147521492991`).
- **Answer-storing class adversaries** (`TcrStore.lean`, `TcrStoreHeadline.lean`, `TcrStoreCount.lean`,
  `TcrStoreCover.lean`; hypothesis `Structural`): `bTcrArA n A`, `bTcrArA_experiment_eq`, `bTcrArA_advantage_eq`,
  `slhdsa_{suf,euf}_cma_final_store` (+ pure, bytes, 128s), `storeForgeOpen`, `bTcrArA_forge_open`,
  `storeForgeOpen_hashes` (`≤ qs + (1 + verifyHashes)`; 128s `qs + 3929`) — for the PINNED program
  `simulateQ (pinImpl tbl) (storeForgeOpen …)` (`pinImpl_tbl`), not under arbitrary oracle answers.
- **Deviations to know**: verification costs `1 + verifyHashes`; SUF checks are the open forms `sufCheckOpen` /
  `sufCheckO`; "no hashing" = invariance under `Open.withTH` (`Thash`, `H_msg`), `PRF`/`PRFmsg` only for first
  phases (`withHash`); `Tcr.lean`/`TcrStoreCount.lean` use a kernel-checked `Eq.refl` tactic (no axiom).
