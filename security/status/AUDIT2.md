# Second independent audit of `Reduction` — final (fully proven) state

(Note added by the W6 documentation sweep) Historical: "final" here is the end of phase 1 (`slhdsa_euf_cma`, eight terms, PRF game `skPrf` on all of `Adrs` — false at SHA2-128s —, EUF-CMA, internal interface). Findings of this audit were addressed in phase 2; the current theorems (`slhdsa_*_cma_final_split`, twelve terms, `skPrfC`, SUF-CMA, external interface) and limitations are in `status/FINAL2.md`. File/line references are to the sources of that time.

Read-only audit. No existing file was edited. Scratch files under `security/scratch/audit2/`
were type-checked with `lake env lean` and deleted. `lake build` was not run.

Scope: `Reduction/*.lean` (11 562 lines), `status/AUDIT.md`, `status/P0–P9.md`, `status/BRIEF.md`,
the VCVio games the library instantiates (`.tools/VCVio-upstream`, commit `a10530a`, clean tree),
and the EasyCrypt final lemma (`.tools/formosa-slhdsa/proofs/SPHINCS_PLUS.ec:4339-4364`).

## 0. What was checked mechanically

| check | result |
|---|---|
| every `Reduction/*.olean` is newer than its source | yes (so the scratch checks ran against the current sources) |
| `#print axioms Reduction.slhdsa_euf_cma` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms Reduction.slhdsa_sha2_128s_euf_cma` | `[propext, Classical.choice, Quot.sound]` |
| `#print axioms Reduction.structural_128s` | `[propext, Classical.choice, Quot.sound]` |
| `grep sorry/axiom/admit/native_decide/bv_decide/implemented_by/unsafe` in `Reduction/` | only one stale docstring mention of `sorry` (`Final.lean:15`) |
| the statement with `bound` unfolded by hand (section 1) is accepted by Lean as an `example` proved by `slhdsa_sha2_128s_euf_cma optRand pkSeedDist A` | yes |
| `Link.vp.params`: `w = 16, len = 35, k = 14, a = 12, h = 63, h' = 9, d = 7` (`by decide`) | yes |
| definition-level choice analysis of the nine adversaries (section 2) | two uses, both an enumeration order of a public finite type |

Definition-level choice analysis. `#print axioms` follows proof terms, so it cannot tell whether
a *definition* computes with choice. I wrote a metaprogram that, starting from a constant, follows
only the values and types of definitions (never the proof of a theorem), and reports every edge
from project code (`Reduction`, `VCVio`, `HashSig`, `ToMathlib`, `PolyFun`, `Cslib`, `ToCslib`,
`Link`) into a Mathlib/core definition that reaches `Classical.choice` the same way. Sanity
check: on `Reduction.Tables.writeBlock` it reports `writeBlock --> Exists.choose`, as expected.

## 1. The final theorems

### Verbatim

`Reduction/Final.lean:43-51` (section variables: `{vp : ValidatedParams} {prims : Primitives vp.params}`,
`[SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]`,
`[DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]`,
`{optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}`):

```lean
theorem slhdsa_euf_cma (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))
```

`Reduction/Instance128s.lean:33-40`:

```lean
theorem slhdsa_sha2_128s_euf_cma
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : Forger Link.vp Link.prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf A) (bPrfMsg A) (bItsr A) (bOpenPre A) (bTcr A)
        (rUd pkSeedDist (bWots A)) (rPre pkSeedDist (bWots A)) (rTcr pkSeedDist (bWots A))
```

### With `bound` (`Steps.lean:91-106`) and `Forger` (`Games.lean:79-86`) unfolded

This form was type-checked (128s instance; the generic one is identical with `vp prims` and the
hypothesis `Structural vp prims`):

```lean
example (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : SignatureAlg.UnforgeableAdversary (internalAlg Link.vp Link.prims optRand pkSeedDist)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      (skPrf Link.vp Link.prims).prfAdvantage (bPrf A) +
      (msgPrf Link.vp Link.prims).prfAdvantage (bPrfMsg A) +
      KeyedHash.ITSRAdvantage (bItsr A) +
      TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (bOpenPre A) +
      TweakableHash.SM_DT_TCR_Advantage (bTcr A) +
      ((Link.vp.params.w - 2 : ℕ) : ℝ≥0∞) *
        TweakableHash.SM_DT_UD_Advantage (rUd pkSeedDist (bWots A)) +
      TweakableHash.SM_DT_PRE_Advantage (rPre pkSeedDist (bWots A)) +
      TweakableHash.SM_DT_TCR_Advantage (rTcr pkSeedDist (bWots A)) :=
  slhdsa_sha2_128s_euf_cma optRand pkSeedDist A
```

The problem each advantage refers to is fixed by the adversary's type: `itsrProblem vp prims`,
`forsOpenPreProblem vp prims pkSeedDist`, `tcrProblem …`, `wotsUdProblem …`, `wotsPreProblem …`,
`wotsTcrProblem …` (`Basic.lean:107-169`).

### Term by term

| term | game (VCVio) | instantiated at | genuine? |
|---|---|---|---|
| left side | `SignatureAlg.unforgeableExperiment`: keygen, run `A.main pk` with a logging signing oracle, verify, require the message was never queried | `internalAlg vp prims optRand pkSeedDist` (`RomConformance.lean:57-70`): `PK.seed ← pkSeedDist`, `SK.seed, SK.prf` uniform, `GeneralScheme.keygenInternal / signInternal / verifyInternal` with `opt_rand ← optRand pk` | yes; `unforgeableAdvantage_eq_prTrue_g0` (`Main.lean:25`) is proved |
| `prfAdvantage (bPrf A)` | `|Pr[real] − Pr[ideal]|`, real = `prims.PRF d.1 k d.2` with `k` uniform, ideal = lazy random function (`PRF.lean:116-133`) | `skPrf` (`Basic.lean:84`), domain `(PK.seed, ADRS)` | yes |
| `prfAdvantage (bPrfMsg A)` | same | `msgPrfScheme`: `prims.PRFmsg skPrf opt_rand M`, key uniform | yes |
| `ITSRAdvantage (bItsr A)` | target oracle samples a fresh uniform key per query and returns it; win = candidate `(R*, x*)` not a target and all its indices covered (`ITSR.lean:71-110`) | `prims.Hmsg R pkSeed root M`, indices = the `k` FORS leaves of `splitDigest` (`Basic.lean:98-114`) | yes |
| `OpenPRE….advantage (bOpenPre A)` | commit tweaks, one uniform hidden input per tweak, images + seed revealed, opening oracle; win = valid tweak list, index never opened, preimage of its image | `F = Thash pk t [x]`, inputs `$ᵗ prims.Y`, cap `2^h·k·2^a`, no collection | yes |
| `SM_DT_TCR_Advantage (bTcr A)` | chosen `(tweak, msg)` targets with distinct tweaks, then seed, then `m ≠ mⱼ` with equal hash (`SMDTTCR.lean:98-135`) | `prims.Thash` on `List Y`, cap `(constructionAddresses vp).length`, no collection | yes (cross-arity, see D1) |
| `SM_DT_UD_Advantage (rUd …)` | `|Pr[real] − Pr[ideal]|`; real answers `F(t, x)`, `x` uniform; ideal uniform | `F`, collection = whole `Thash`, cap `#inst·len` | yes |
| `SM_DT_PRE_Advantage (rPre …)` | challenge = `F(t, x)` for uniform `x`; win = any preimage of target `j` | same | yes |
| `SM_DT_TCR_Advantage (rTcr …)` | as SM-TCR, with collection | `F`, collection = `Thash`, cap `#inst·len·w` | yes |

All games read the seed from `pkSeedDist`, the same distribution the scheme uses. I re-read the
VCVio definitions of all eight games; they are as `AUDIT.md` Q2 describes.

### The forger type

`Forger = SignatureAlg.UnforgeableAdversary (internalAlg …)`, a structure with one field
`main : PublicKey → OracleComp (unifSpec + (List Byte →ₒ Signature)) (List Byte × Signature)`.
It is the ordinary adaptive chosen-message adversary with private uniform randomness. There is no
side condition: no query bound, no message-distinctness requirement, no restriction on `optRand`
or `pkSeedDist`. The type is inhabited by every such program, so the quantifier is not emptied.
The number of signing queries `q_s` does not appear in the theorem; it appears only as a
hypothesis of the separate resource lemmas (section 2).

## 2. The reduction adversaries

### Explicitness

Result of the definition-level analysis, per adversary (all nine are also `noncomputable`-marked
or built from `noncomputable` parts only because `ProbComp` sampling and `Fintype.mPi` are):

| adversary | edges into choice-dependent definitions |
|---|---|
| `bPrf` | none |
| `bPrfMsg`, `bItsr`, `bOpenPre`, `bWots` | `Fintype.mPi → Fintype.equivFin` (inside `sampleTable`) |
| `bTcr` | `Fintype.mPi → Fintype.equivFin`; `structureVia → Finset.toList` |
| `rUd`, `rPre`, `rTcr` (generic in `W`) | none |

So `AUDIT.md`'s remark that all of them "depend on `Classical.choice`" is true only through
proof terms; at the level of definitions exactly two uses remain:

1. `sampleTable = Fintype.mPi fun _ : Fin (2^256) => $ᵗ prims.Y` (`Games.lean:47-48`).
   `Fintype.mPi` (VCVio `ToMathlib/Control/Monad/Fold`) orders the index type with
   `Fintype.equivFin`, which is obtained by choice. The choice is an ordering of the public type
   `Fin (2^256)`; the resulting distribution does not depend on it.
2. `structureVia` (`TCR.lean:39`) iterates over `(Finset.univ : Finset (LayerTreeCoord vp)).toList`.
   Again an ordering of a public finite type (the XMSS trees). It fixes the order in which `bTcr`
   submits its targets; `honestCalls` in phase 2 uses the same term, so the two phases agree.
   `AUDIT.md` M1 asked to replace it by `allXmssTrees vp`; this was not done.

Neither use selects anything that depends on a secret, on the forger, or on the hash function,
and neither is a search. Nothing else was found:

- `writeBlock` (`Tables.lean:293`, `h.choose`) is used only inside `Tables.lean` lemmas. No
  adversary, game, step statement or the final theorem reaches it (`readBlock`, which is
  constructive, appears in three proof-only statements of `WotsEmbed.lean`).
- `updateList`, `mix`, `sampleList`, `freshImpl`, `tablePrf` are not reachable from any adversary.
- `Classical.propDecidable` / `Classical.decEq` are reachable only inside `Fintype.equivFin`.
  Every `if` and `decide` in the adversaries uses the `DecidableEq` instances of the theorem.
- No `Classical.epsilon`, `Nat.find`, `Function.invFun`, `Quot.out` outside the two items above.
- No search over `prims.Y` is possible in the generic theorem: the adversaries have only
  `SampleableType`, `DecidableEq` and `Inhabited` on `prims.Y`, no `Fintype`.
- Secrets of the challenger: by typing, phase 1 of every SM adversary is an `OracleComp` over the
  game's oracle interface and phase 2 receives only its own state and the seed (and, for OpenPRE,
  the images and the opening oracle). The revised `bWots`, `bOpenPreWith`, `openSign`,
  `itsrRandomizer`, `chooseBody`, `msgAt`, `signFromHist` were read line by line: they use only
  oracle answers, the adversary's own table and public data.

### Table: adversary → game → resources/caps → explicitness verdict

`q_s` = number of signing queries of `A` (hypothesis
`∀ pk, IsQueryBoundP (A.main pk) (·.isRight) q_s` of the resource lemmas).

| adversary (file:line) | game | runs of `A` | samples itself | game queries / targets, with the lemma that bounds them | refusals ruled out by | explicit? |
|---|---|---|---|---|---|---|
| `bPrf A` (`PRFHop.lean:41`) | PRF on `PRF(·, SK.seed, ·)` | 1 (`runForger`) | `PK.seed ← pkSeedDist`, `SK.prf`, `opt_rand` per query | function queries at its own `PK.seed` and canonical secret addresses: `≤ 2^h'·len + q_s·(k·2^a + d·2^h'·len)` — `bPrf_queryBound_exact`; looser `bPrf_queryBound` | not applicable (PRF oracle never refuses) | yes, choice-free |
| `bPrfMsg A` (`PRFMsgHop.lean:24`) | PRF on `PRF_msg(SK.prf, ·, ·)` | 1 (`runForger`) | `PK.seed`, table, `opt_rand` | `≤ q_s` — `bPrfMsg_queryBound` | not applicable | yes, up to item 1 |
| `bItsr A` (`ITSR.lean:87`) | ITSR on `H_msg` | 1 (`runForgerLog`) | `PK.seed`, table, `opt_rand` | one target per signing query with a new `(opt_rand, M)`: `≤ q_s` — `bItsr_queryBound` | not applicable | yes, up to item 1 |
| `bOpenPre A` (`OpenPRE.lean:98,114`) | SM-DT-OpenPRE on `F` | 1 (`runForgerLog`, in `find`) | table (`pick`); `opt_rand` and lazy `R` (`find`) | commits `forsLeafKeys` = all `2^h·k·2^a` FORS leaves = cap — `forsLeafKeys_nodup_length`; `k` openings per signing query (no lemma states `≤ k·q_s`; the game has no opening cap); no collection query | validity bit true: `op_initSt_initial`; every opening in range and answered by the real preimage: `op_sign_run` | yes, up to item 1 |
| `bTcr A` (`TCR.lean:1999`) | SM-TCR on `Thash` | 1 (`g2Run`, in `forge`) | table (`choose`); `opt_rand`, lazy `R` (`forge`) | exactly `tcrTargets vp` challenges, distinct tweaks — `honestCalls_nodup_length` (via `honestCalls_map_fst`: a permutation of `constructionAddresses`) | `bTcr_choose_run`: the game's challenge history is exactly `honestCalls tbl pk` | yes, up to items 1 and 2 |
| `bWots A` (`WotsEmbed.lean:143`) | internal WOTS game (not in the statement) | 1 (`g2RunWith`, in `forge`) | table (FORS cells used); `opt_rand`, lazy `R` | signs each instance of `wotsInsts vp` once (`chooseBody`, memoised by `topsAt`); collection only at non-chain tweaks | `chooseBody_run` (deterministic run, history `HistGood`; uses `x1_not_reserved`, `x2_not_reserved`) | yes, up to item 1 |
| `rUd (bWots A)` (`WotsUD.lean:66`) | SM-UD on `F` | 1 (through `W.choose`, `W.forge` once each) | hybrid index `k ← $ᵗ Fin (w−3+1)`; start values of chains with digit `≤ k+1` | at most one challenge per chain, `≤ #inst·len` = cap — `UdInv.len` with `hist_length_lt` | `ud_hcoll`, `ud_hsign` (invariant `UdInv`), assembled in `udFixed_eq`, `experiment_eq` | yes, up to item 1 (inherited from `bWots`) |
| `rPre (bWots A)` (`WotsFinal.lean:88`) | SM-PRE on `F` | 1 | start values of digit-0 chains | one challenge per chain with nonzero digit, `≤ #inst·len` = cap — `PreInv.len`, `sum_preCount_le`, `hist_length_lt` | `pre_hcoll`, `pre_hsign` (invariant `PreInv`) | yes, up to item 1 |
| `rTcr (bWots A)` (`WotsFinal.lean:167`) | SM-TCR on `F` | 1 | all start values | `w−1−b` challenges per chain, `≤ #inst·len·(w−1)` `<` cap `#inst·len·w` — `TcrInv.len`, `sum_tcrCount_le` | `tcr_hcoll`, `tcr_hsign` (invariant `TcrInv`) | yes, up to item 1 |

"Runs `A` once" is syntactic: `A.main` occurs only in `runForger`, `runForgerLog`, `g2RunWith`
(`Harness.lean`, `Games.lean`), each a single `simulateQ` over `A.main pk`, and each adversary
calls exactly one of them once. In the three WOTS reductions `A` runs after the seed reveal, with
all game interaction done before it, as in the paper.

Refused answers are read as `default` (`wColl`, `udColl`, `preChal`, `wtcrChal`, `bTcr`'s
challenge wrapper, `topsAt`). `AUDIT.md` N5 asked for the no-refusal facts to be explicit; they
are now all proved (last column). Since the step lemmas are proved, these facts no longer carry
any risk for the truth of the theorem; they document that the reductions behave as intended.

### Changes to adversary definitions since the first audit (M1 re-audit)

| adversary | change | assessment |
|---|---|---|
| `bPrf`, `bPrfMsg`, `bTcr`, `rUd` | none reported, none seen | — |
| `bItsr` | inline randomizer named `itsrRandomizer`; projections instead of pattern `let` | same program |
| `bOpenPre` | now `bOpenPreWith (sampleTable vp prims) A`; signing body named `openSign`, hypertree part `opHt` | same program; the sampler parameter exists only to work around an elaboration loop |
| `rPre`, `rTcr` | inline lambdas named `preStart`, `preChainHash`, `tcrStart`, `tcrChainHash` | same programs |
| `bWots` | rewritten: `msgAt` (explicit Merkle root over `T_len(chain ends)` through the collection oracle), `chooseBody` (loop over `allWotsInstances`, then `msgAt d 0 0`), `signFromHist` (recorded WOTS+ signatures plus authentication paths over recorded chain ends), `histEntry` | a real revision, and a cleaner one: the earlier "identity chain hash" device is gone. Still one run of `A`, no search, no choice beyond `sampleTable`. Behaviour is the paper's reduction |

No revision added a second run of the forger, a search, or a `Classical.choose`.

## 3. Frozen files and non-vacuity

### Frozen files

There is no version control, so the comparison is against `AUDIT.md`'s descriptions and line
references and against file times.

- Every line reference of `AUDIT.md` into frozen files still matches: `Basic.lean:55` (`Structural`),
  `65/71/77` (`thashList`, `fHash`, `thashColl`), `84`, `90`, `98`, `103`, `134`;
  `Games.lean:32, 36-38, 47-48, 79-86, 222-226`; `WotsGame.lean:69-74`; `Steps.lean:91-106`;
  `Main.lean:25, 35-67`.
- Last-modified times: `Basic` 12:34, `WotsGame` 12:36, `Steps` 12:38, `Harness` 12:41,
  `WotsSim` 12:44, `Games` 12:46, `Final` 12:48, `Main` 12:50 — all before `AUDIT.md` (13:04).
  `Instance128s` 13:02 (`structural_128s` proved by P9).
- Content read in full: definitions and step statements are as `AUDIT.md` describes them.
- The package notes report no change to a frozen file and no request to change one. Two lemma
  statements inside owned files changed: `wotsAnswer_wins` (new hypothesis `HistGood`; the old
  hypotheses were insufficient) and the usable form of `idealRoot_congr` (`op_idealRoot_congr`
  with `WotsAgree`). Neither is part of the final statement.

SHA-1 of the frozen files at audit time, for future comparison:

```
5f33675aa1b0335f74b0ad74e7e34ee70776626d  Reduction/Basic.lean
1b4118448192ba36bd7ac28ec239b5dc397d3993  Reduction/Games.lean
bf10614785abb55b161d5051da73b2988cd31784  Reduction/WotsGame.lean
1c43f10f71b879a3f801a65a564be124b7ec1954  Reduction/Steps.lean
51b331088c2cbebc3a52e7b74c3520b96c3a11a5  Reduction/Harness.lean
d4420ef6de7e57516577a9967b93feb858ce3810  Reduction/Main.lean
4bf1aeaf3db5b129bda727395e311ccc32be7c7f  Reduction/WotsSim.lean
5675a2a89ff53bce0570f1a1aa207742c4f4e230  Reduction/Final.lean
33ff5514cb35ee6bebfc4ad4a60b41e86d06777c  Reduction/Instance128s.lean
```

Stale text (not a logical issue): `Final.lean:15-16` ("its `sorry` footprint is exactly that of
the step lemmas") and `Main.lean:7-9` ("to be added by the last work package").

### Non-vacuity (`NonVacuity.lean`, all proved, standard axioms)

| game | can be lost (advantage 0) | can be won on a degenerate bundle |
|---|---|---|
| PRF (`skPrf`) | `prf_const_adv_zero` | `prfTester_adv`, `toy_prf` (advantage 1/2) |
| PRF_msg | `prfMsg_const_adv_zero` | **missing** |
| ITSR | `itsr_trivial_adv_zero` | `itsrReplayer_adv_one`, `toy_itsr` |
| SM-DT-OpenPRE(F) | `openPre_trivial_adv_zero` | `openPreInverter_adv_one`, `toy_openPre` |
| SM-TCR(Thash) | `tcr_trivial_adv_zero` | `tcrCollider_adv_one`, `tcr_winnable`, `toy_tcr` |
| SM-UD(F) | `ud_const_adv_zero` | `udTester_adv`, `toy_ud` (advantage 1/2) |
| SM-PRE(F) | `pre_trivial_adv_zero` | `preInverter_adv_one`, `pre_winnable`, `toy_pre` |
| SM-TCR(F) (`wotsTcrProblem`) | `wotsTcr_trivial_adv_zero` | **missing** |

Six of eight games have both directions. The two gaps are routine (the PRF_msg tester is
`prfTester` at the other scheme; the WOTS SM-TCR collider is `tcrCollider` at arity one). There
is also no statement that the left side can be nonzero (a forger with positive advantage against
`toyPrims`); `verifyInternal_idealSign` (`TCR.lean:2046`) at least shows verification accepts
honest signatures, so the left side is not identically zero by a broken verifier.

## 4. `Structural` and `structural_128s`

`Structural vp prims` (`Basic.lean:55-58`) has three fields:

- `byteLaws : prims.core.ByteLaws` — `Function.Injective yToBytes`;
- `keyInj : CorePrimitives.KeyInjective vp prims.core` — `Set.InjOn adrsToKey {a | AddressFacts vp a}`;
- `bounds : CanonicalAddressBounds vp.params` — seven numeric inequalities
  (`d ≤ 2^32`, `(d−1)·h' ≤ 96`, `h' ≤ 32`, `a ≤ 32`, `k·2^a ≤ 2^32`, `len ≤ 2^32`, `w ≤ 2^32`).

None mentions a probability, an adversary or a hash value; all three are encoding facts.
`structural_128s : Structural Link.vp Link.prims` (`Instance128s.lean:21-24`) is proved from
`Concrete.sha2Primitives_byteLaws` (nodes are `Bytes 16`, identity encoding),
`Concrete.keyInjective_sha2Primitives` (injectivity of the compressed address `ADRSc` on in-range
addresses) and `fipsApprovedAddressBounds Link.S128` (by `decide`). Standard axioms only. The
128s theorem therefore has no hypothesis besides the forger.

Not audited here: that `Link.prims` (`sha2Primitives`) is FIPS 205 SHA2-128s (the `Link` library).

## 5. Comparison with Hülsing–Kudinov Theorem 1 and the EasyCrypt result

EasyCrypt final lemma `EUFCMA_SPHINCS_PLUS` (read from the artefact): PRF + PRF_msg + ITSR
+ max(0, DSPR − SPprob) + 3·TCR(F, FORS leaves) + TCR(FORS tree hash) + TCR(FORS root compression)
+ (w−2)·UD(F) + TCR(F, chains) + PRE(F) + TCR(WOTS pk compression) + TCR(XMSS tree hash).
HK22 Theorem 1 has the same shape with insecurity functions and query counts over the whole
structure (stated here from memory of the paper, not re-read).

| aspect | HK22 / EasyCrypt | this development | effect |
|---|---|---|---|
| FORS leaves | DSPR + 3·TCR on `F` | SM-DT-OpenPRE on `F` assumed directly (BDHMS intermediate notion) | different assumption, one step short of the paper; VCVio's `OpenPREFromTCRDSPR` is not composed in |
| WOTS chains | (w−2)·UD + TCR + PRE on `F` | the same three terms, same coefficients | same. SM-PRE is an assumption in the paper's and EC's theorem too; HK22 only relates it to DSPR+TCR afterwards for the bit-security estimate, which is also absent here |
| tree and compression hashes | four separate SM-TCR terms (FORS `H`, `T_k`, `T_len`, XMSS `H`) | one SM-TCR term on variable-arity `Thash` | fewer terms, but the assumption is cross-arity and its cap is the sum of all calls of the structure, including chain steps and FORS leaves that the collision case never needs; a stronger assumption, hence a slightly weaker theorem if read as an implication |
| target counts | whole key structure, independent of `q_s` | same (`2^h·k·2^a`, `#inst·len`, `#inst·len·w`, all ledger calls) | same |
| PRF query count | whole structure | `2^h'·len + q_s·(k·2^a + d·2^h'·len)` (`bPrf_queryBound_exact`) | tighter here |
| tightness | coefficient 1 except `w` or `w−2` on UD and 3 on TCR(F) | coefficient 1 except `w−2 = 14` on UD | as tight as EC; no factor 3 because OpenPRE is not reduced further |
| security notion | EUF-CMA | EUF-CMA | same; SUF-CMA not covered |
| scheme | abstract SPHINCS+ with tweakable hashes | FIPS 205 internal algorithms 18–20 over a primitive bundle, with the SHA2-128s bundle instantiated and `Structural` proved | closer to the standard; but the external `slh_sign`/`slh_verify` wrappers (context string, pre-hash) are not covered |
| seed and randomizer | uniform `PK.seed` | arbitrary `pkSeedDist`, arbitrary `optRand pk` (deterministic and hedged signing) | more general; no corollary at uniform seed is stated |
| statement form | bound over all adversaries with given time and queries (insecurity functions); EC: explicit reductions | explicit reductions, each running `A` once | like EC |
| cost of the reductions | time of `A` plus about one evaluation of the key structure (about `2^79` hash calls for 128s) | no running-time statement. `bPrfMsg`, `bItsr`, `bOpenPre`, `bTcr`, `bWots` draw an eager table of `2^256` values and carry it as state | weaker: nothing formal says the reductions are feasible, and as written they are not |
| `q_s` | appears in the query counts | does not appear in the theorem; three separate resource lemmas | no packaged concrete-security corollary |
| model | standard model | standard model, no oracle, axioms `propext, Classical.choice, Quot.sound` | same |

## 6. Defects

### Fatal

None found. The theorem is what it says: the EUF-CMA advantage of an arbitrary forger against
the FIPS 205 internal algorithms is bounded by eight advantages of named games, on the scheme's
own functions, for nine adversaries that are explicit programs running the forger once.

### Must-fix (about what may be claimed, not about truth)

**M1 (carried over, partly open). Two definition-level uses of choice in the adversaries.**
`structureVia` still uses `Finset.univ.toList` (`TCR.lean:39`), and `sampleTable` uses
`Fintype.mPi`, which goes through `Fintype.equivFin`. Both only fix an enumeration order of a
public finite type and change no distribution or advantage, but as long as they are there the
sentence "every reduction is an explicit program" is not literally true for `bTcr`, `bPrfMsg`,
`bItsr`, `bOpenPre`, `bWots`.
Minimal fix: in `structureVia` and `mf_all` replace
`(Finset.univ : Finset (LayerTreeCoord vp)).toList` by `allXmssTrees vp` (`mf_univ_length`
becomes `allXmssTrees_length`; `allXmssTrees_nodup` exists; `mf_ledger_subset` needs membership
of every coordinate). For the table either define `sampleTable` with `Fin.mOfFn (2^256)` directly
(then prove `sampleTable_eq_uniformTable` instead of `rfl`), or state the limitation next to the
theorem. Keep the definition-level check as a gate (the metaprogram is 40 lines).

**M2 (carried over, open). Efficiency wording and the `2^256` table.**
`REDUCTION_STATUS.md:108` ("efficient, exactly like the paper's") and `TCR.lean:19` ("as
(in)efficient as in the paper") are still inaccurate: five adversaries sample `2^256` values and
carry the table as state; the paper's reductions cost about `2^79` hash calls. No lemma states
that the adversaries depend only on the table cells of the secret-address ledger.
Minimal fix: correct the two sentences and add to the docstring of `slhdsa_euf_cma` that no
running-time claim is formalised. Better: index `SecretTable` by the finite ledger of secret
addresses, or prove that each adversary's output distribution is unchanged when the table is
sampled lazily.

### Notes

- N1. Non-vacuity gaps: no "can be won" lemma for PRF_msg and for SM-TCR on `F`
  (`wotsTcrProblem`); no lemma that the left side can be positive.
- N2. No corollary that packages `bPrf_queryBound`, `bPrfMsg_queryBound`, `bItsr_queryBound` with
  the theorem, and no bound `≤ k·q_s` on the openings of `bOpenPre`.
- N3. No corollary at uniform `PK.seed` (the FIPS scheme). For a point-mass `pkSeedDist` the
  theorem is still a true inequality, but the SM assumptions are then false.
- N4. The deviations D1 (cross-arity TCR with merged cap), D2 (OpenPRE assumed), D5 (PRF and ITSR
  adversaries choose `PK.seed`) are documented in `Basic.lean` but not next to the theorem.
- N5. Scope: internal algorithms only; EUF-CMA only; single key.
- N6. Stale docstrings in `Final.lean:15-16` and `Main.lean:7-9`; `REDUCTION_STATUS.md` still
  describes the skeleton.
- N7. `wotsAnswer_wins` keeps an unused hypothesis `hvalid`; `idealRoot_congr` is true but its
  hypothesis is too strong to be useful (`op_idealRoot_congr` is the usable form).
- N8. No version control. The SHA-1 list in section 3 can serve as a baseline.
- N9. The comparison with HK22 Theorem 1 in section 5 is from memory of the paper; the EasyCrypt
  lemma was read from the artefact.

## 7. Verdict

The final state is sound as far as this audit can see. Both theorems type-check with only the
three standard axioms and no `sorry`; the statement, with `bound` unfolded, is a genuine
standard-model inequality between the real EUF-CMA advantage of an unrestricted forger against
`internalAlg vp prims optRand pkSeedDist` and eight advantages of faithful games on `prims.PRF`,
`prims.PRFmsg`, `prims.Hmsg`, `prims.Thash`. The frozen game and step files are unchanged since
the first audit. The nine adversaries are explicit single-run reductions; the revision of
`bWots` improved it and introduced nothing non-constructive. A definition-level analysis found
only two uses of choice, both an ordering of a public finite type, so the first audit's concern
M1 did not materialise in a harmful form, though its cheap fix was not applied. What the theorem
does not give is any statement about the cost of the reductions (the eager `2^256` table makes
five of them infeasible as written), a reduction of SM-OpenPRE to TCR + DSPR, per-arity TCR
assumptions, coverage of the external FIPS 205 interfaces, or SUF-CMA. Relative to the
EasyCrypt result it is equally tight on the terms it shares, closer to FIPS 205, more general in
the seed and randomizer distributions, and one step less reduced on the FORS-leaf term.
