# Independent architecture audit of `Reduction` (definitions and statements only)

(Note added by the W6 documentation sweep) Historical: this audit describes the library when 35 `sorry` remained and only the phase-1 statement existed. There is no `sorry` now; the current theorems and their limitations are in `status/FINAL2.md`. File/line references are to the sources of that time.

Scope: `REDUCTION_STATUS.md`, `Reduction/{Basic,Games,WotsGame,WotsSim,Steps,Harness,Main,Final,Instance128s}.lean`
(frozen), the adversary definitions in `PRFHop, PRFMsgHop, ITSR, OpenPRE, TCR, WotsEmbed, WotsUD,
WotsFinal`, the statements in `NonVacuity`, and the VCVio games they instantiate. Proof bodies were
ignored (35 `sorry`). Nothing was edited. A scratch file importing `Reduction.Instance128s` and
`Reduction.NonVacuity` type-checked and was deleted.

Mechanically checked:
- `#print axioms Reduction.final_of_steps` and `unforgeableAdvantage_eq_prTrue_g0`: `propext, Classical.choice, Quot.sound`.
- `#print axioms Reduction.slhdsa_sha2_128s_euf_cma`: additionally `sorryAx` (expected).
- 128s parameters: `w = 16`, `len = 35`, `(k, a, h, h', d) = (14, 12, 63, 9, 7)`; caps
  `forsF = 2^63·14·2^12 ≈ 2^78.8`, `wotsFPre ≈ 2^68.1`, `wotsFTcr = 16·wotsFPre`.
- All of `bPrf, bTcr, bWots, bOpenPre, rPre, rUd` depend on `Classical.choice` (relevant to defect M1).

Not checked: any proof; that `structureVia` makes exactly the calls of `constructionAddresses`;
`skPrfQueries`; `structural_128s`; the `Link` identification of `sha2Primitives` with FIPS 205.

## Verdict

No fatal defect found. The final statement is a genuine standard-model, explicit-reduction
statement; the eight games are faithful (oracle-based, adaptive, distinct-tweak) instances of
HK22 / BDHMS notions at the scheme's own functions; the nine frozen steps are each plausibly true
and compose without a gap. Two must-fix items concern what the theorem can be *claimed* to mean
(adversary definitions are not frozen; the efficiency wording is wrong), not its truth.

---

## Q1. Is `slhdsa_euf_cma` a genuine standard-model statement?

Yes.

- Left side. `Forger = UnforgeableAdversary (internalAlg vp prims optRand pkSeedDist)`
  (`Games.lean:79-86`). `internalAlg` (VCVio `RomConformance.lean:57-70`) draws `PK.seed ← pkSeedDist`,
  `SK.seed, SK.prf` uniformly, and uses `GeneralScheme.keygenInternal / signInternal / verifyInternal`,
  which are `simulateQ (PublicHash.impl prims)` of the monadic FIPS programs, i.e. deterministic
  functions of `prims.PRF, PRFmsg, Hmsg, Thash` (`GeneralScheme.lean:157-180`). The file name
  "RomConformance" is incidental: no oracle remains. The experiment is VCVio's
  `unforgeableExperiment` (`SignatureAlg.lean:222-233`): fresh-message check plus verification.
  `unforgeableAdvantage_eq_prTrue_g0` (`Main.lean:25`) is proved.
- Right side. `bound` (`Steps.lean:91-106`) is a sum of advantages of the explicit adversaries
  `bPrf A, …, rTcr (bWots A)` in VCVio games instantiated in `Basic.lean` at `prims.PRF` (`skPrf`,
  l.84), `prims.PRFmsg` (`msgPrf`, l.90), `prims.Hmsg` (`hmsgFamily`, l.103), `prims.Thash`
  (`thashList`, `fHash`, `thashColl`, l.65-79). G1, G2, `g2Class`, `WotsGame.hyb` are internal and
  do not appear in the statement.
- No quantifier trick found. No term is ≥ 1 by construction (the two distinguishing terms are
  `boolDist = |Pr − Pr|`; the others are success probabilities of non-trivial experiments; the
  fallback answers `(0, [])`, `(0, default)` of the reductions do not win trivially). Adversary
  types are inhabited structures. `SampleableType` carries a proof of uniformity
  (`SampleableType/Basic.lean:51-57`), so "uniform" cannot be faked by an instance. `Inhabited Y`
  only supplies the witness returned by out-of-range opens.
- `Structural` (`Basic.lean:55-58`) = injective node encoding (`ByteLaws`, `Primitives.lean:136`),
  address encoding injective on in-range addresses (`KeyInjective`, `KeyDiscipline.lean:66`),
  FIPS address widths (`CanonicalAddressBounds`). Non-cryptographic and satisfiable in principle;
  in the instance it is the lemma `structural_128s` (still `sorry`), not a hypothesis, so it
  cannot make the instance vacuous.
- The 128s instance (`Instance128s.lean:26-33`) quantifies over all `optRand` and `pkSeedDist`.

Limits of the statement (notes N1–N3 below): internal algorithms only (FIPS Alg. 18–20, no
context/pre-hash wrapper), EUF-CMA only, no `q_s` in the bound.

## Q2. The eight games

Common shape of the three rejection-on-arrival SM games (VCVio `SMDTTCR.lean:98-135`,
`SMDTPRE.lean`, `SMDTUD.lean`, `Collection.lean`): the experiment samples the seed from
`th.seedGen = pkSeedDist`; phase 1 has private coins, a challenge oracle and a collection oracle and
no seed; phase 2 gets the seed and no oracle (typing fact). Challenge queries are refused beyond
`numTargets`, on a repeated tweak, or on a tweak already used in the collection; collection queries
are refused on a challenge tweak. This is the oracle-based adaptive form of HK22 Def. 2/3/4/7 and
matches the EasyCrypt oracles (`TweakableHashFunctions.eca:71-136, 483-543`), up to
rejection-on-arrival versus final-validity (VCVio `ToFinalValidity` relates them at equal
advantage).

| game | who samples | adversary receives | win | cap | faithful? |
|---|---|---|---|---|---|
| PRF (`skPrf`) | key `SK.seed` uniform; ideal = lazy random function | answers on adversary-chosen `(PK.seed, ADRS)` | `\|real − ideal\|` | none in game; `bPrf_queryBound` (open) | yes (EC `SKG_PRF` has the same domain) |
| PRF_msg | key `SK.prf` uniform | answers on `(opt_rand, M)` | same | `bPrfMsg_queryBound`: `q_s` | yes |
| ITSR (`ITSR.lean:71-110`) | key `R` uniform, sampled *after* the adversary submits `x = (PK.seed, PK.root, M)` | `R` | fresh pair `(R*, x*)` whose `k` FORS indices are all covered | none in game; `bItsr_queryBound`: `q_s` | yes (HK22 Def. 9). Not trivially winnable since `k > 0` (`Params.Valid.k_pos`) |
| SM-DT-OpenPRE(F) | seed; one uniform input per committed tweak | phase 1: nothing (collection is `Empty`); phase 2: seed, all images, opening oracle | index never opened, any preimage of its image, tweak list valid | `2^h·k·2^a`; longer lists truncated | yes (BDHMS Fig. 10/11) |
| SM-TCR(Thash) | seed | hash of adversary-chosen `(tweak, list)` | different list, same tweak, same hash | `(constructionAddresses vp).length` | yes, with deviation D1 |
| SM-UD(F) | seed; real: uniform `x`, returns `F(t,x)`; ideal: uniform `y` | the value, plus collection = whole `Thash` at other tweaks | `\|real − ideal\|` | `#inst·len` | yes (HK22 Def. 4/7) |
| SM-PRE(F) | seed; uniform `x` per tweak | `F(t,x)`, collection | any preimage of target `j` | `#inst·len` | yes (HK22 Def. 3/7) |
| SM-TCR(F) | seed | `F(t,x)` for chosen `(t,x)`, collection | `x' ≠ x`, same image | `#inst·len·w` | yes (EC `FC_TCR`) |

Trivially winnable / unwinnable: none. The adversary never receives a hidden input except through
the opening oracle, which disqualifies that index. No challenger randomness is adversary-chosen.
The collection oracle cannot evaluate at a challenge tweak, in either order.

Coefficients: `(w − 2)` on UD and `1` elsewhere match HK22 Thm. 2 and the EasyCrypt final lemma
(`SPHINCS_PLUS.ec:4339-4364`). UD needs at most one target per chain, PRE at most one, TCR(F) at
most `w − 1` per chain (cap uses `w`, a slack).

Deviations:

- D1. One SM-TCR game on variable-arity `Thash` with `M = List Y` (`Basic.lean:65-68, 134-136`).
  The game admits targets of any arity at any tweak and cross-arity collisions, so the *assumption*
  "every adversary has small advantage" is stronger than the paper's per-arity assumptions, hence
  the theorem read that way is slightly weaker. The concrete `bTcr A` only submits honest arities
  and `findCollision` (`TCR.lean:72-77`) only returns same-arity collisions (a verification call
  versus the honest call at the same address), so nothing is lost for the explicit adversary. The
  merged cap is the sum of the paper's caps plus the WOTS chain steps and FORS leaves, which
  `bTcr` also submits although class `tcr` never needs them. Different, not wrong.
- D2. FORS leaves use SM-DT-OpenPRE directly; HK22/EC continue to `3·TCR + DSPR`. A different
  (BDHMS intermediate) assumption; plausible for a length-preserving `F`.
- D3. `pkSeedDist` is arbitrary. For a point-mass distribution the SM assumptions are false in
  the existential sense (the seed is known in phase 1), but the theorem is still a true inequality
  for the explicit adversaries and both sides use the same distribution. More general than the
  paper, not a loophole.
- D4. Caps are the whole structure, independent of `q_s`, as in EC. A larger cap is a (weakly)
  stronger assumption; harmless generically because tweaks are distinct.
- D5. The PRF and ITSR adversaries may choose `PK.seed` (and `PK.root`) in their inputs. Same as EC.
- D6. OpenPRE is the final-validity presentation; TCR/PRE/UD are rejection-on-arrival. Cosmetic.

## Q3. The steps and their composition

`final_of_steps` (`Main.lean:35-67`) is proved and is exactly
`G0 ≤ G1 + PRF ≤ G2 + PRFmsg + PRF ≤ Σ_c g2Class c + …`, with
`wots ≤ Hyb_0 ≤ Hyb_{w−2} + (w−2)·UD ≤ PRE + TCR_F + (w−2)·UD`. No gap.

| step | assessment |
|---|---|
| `StepPRF` | True if real world = G0 and ideal world = G1. Needs every secret read to be at a canonical address, on which `secIdx` (`Games.lean:36-38`, 32+96+32+32+32+32 = 256 bits) is injective; holds under `Structural.bounds`. |
| `StepPRFmsg` | True. `lazyRandomizer` (`Games.lean:222-226`) keyed on `(M, opt_rand)` is exactly the lazy random function of the ideal PRF experiment. |
| `StepSplit` | True (`classify` is total; in fact equality). |
| `StepITSR` | True. Forged message fresh ⇒ candidate pair not a target; class `itsr` is literally the covering condition (`forsIndices` is used on both sides, `Basic.lean:98`, `Games.lean:201`). `R` in G2 is uniform and independent of the table, as in the ITSR oracle. |
| `StepOpenPRE` | Plausible. `PK.root` reads only top-layer WOTS+ secrets, so `find` can form the key without FORS secrets; committed tweaks are exactly `cap` many and distinct; the game's opened set corresponds to `openedLeaves` through `leafTarget` (needs `KeyInjective`). |
| `StepTCR` | Plausible. Checked by hand: not `itsr` gives an unopened tree; not `openpre` makes its forged leaf differ from the honest one; walking up (FORS `H`, `T_k`, then per layer `T_len` and XMSS `H`) each level either stays different or is a collision against an honest call at the same address; a layer with different messages and equal chain ends is class `wots`, excluded; the roots are equal, so a collision exists. |
| `StepWotsEmbed` | Plausible, least exercised. `WotsGame` gives `bWots` what it needs: signature and chain ends per instance, `Thash` at every non-chain tweak. Each instance signs one fixed message, so recorded signatures suffice in phase 2. Helper statements are still missing (status risk 4). |
| `StepWotsUD` | True for every `W` under `Structural`. Checked: real world of `rUd` at index `k` is `hyb k`, ideal is `hyb (k+1)` (`hybSig` uses `c = min k (b−1)`, `WotsGame.lean:69-74`); `k` uniform on `w − 2` values; tweak sets of challenge and collection are disjoint per chain; `W` cannot touch chain tweaks (`reservedKey`). Trivially true for `w = 2`. |
| `StepWotsFinal` | True for every `W` under `Structural`. `m' ≠ m` gives a chain with `b' < b`; either the forged chain passes through the revealed value (preimage at step `b − 1`) or the chains merge at a step `t ≥ b` (collision against an honest chain value that `rTcr` submitted). |

Signing-query count and message distinctness. `q_s` enters only through the resources of `bPrf`,
`bPrfMsg`, `bItsr` and the number of opens of `bOpenPre`; the SM caps do not depend on it, so no
step needs it. Repeated messages: G2 answers a repeated `(opt_rand, M)` with the recorded `R`
(same signature), and `bItsr` asks for a new ITSR target only on a cache miss (`ITSR.lean:43-50`),
so deterministic signing and hedged signing with colliding `opt_rand` are both handled. `optRand :
PublicKey → ProbComp Y` covers FIPS deterministic (`opt_rand = PK.seed`) and hedged (uniform)
modes; it cannot depend on the message or on state, which FIPS does not need.

## Q4. The reduction adversaries

All nine are explicit terms. Each runs the forger through one of `runForger`, `runForgerLog`,
`g2Run`, `g2RunWith` exactly once, straight-line; `rUd`, `rPre`, `rTcr` run `W.choose` and
`W.forge` once each.

| adversary | legality |
|---|---|
| `bPrf` (`PRFHop.lean:29`) | No restriction in the game. Queries only at its own `PK.seed`. |
| `bPrfMsg` | One query per signing query. |
| `bItsr` | One target per fresh `(opt_rand, M)`. |
| `bOpenPre` (`OpenPRE.lean:67`) | Commits to `forsLeafKeys` = all FORS leaves; needs `Nodup` and length = cap (`forsLeafKeys_nodup_length`), otherwise the validity bit is false. No collection query. Opens `k` indices per signing query. |
| `bTcr` (`TCR.lean:85`) | Every call of the honest structure is a challenge query; needs distinct tweaks and count = cap (`honestCalls_nodup_length`). A refused query is read as `default`, so this lemma is load-bearing. |
| `bWots` (`WotsEmbed.lean:128`) | Signs each hypertree instance once (memoised by `topsAt`), never queries a chain tweak (chain hash replaced by identity). Refusals read as `default`. |
| `rUd` | At most one challenge per chain; collection only at later steps of that chain or on unchallenged chains. Needs `(wotsInsts vp).length·len ≤ cap`. |
| `rPre` | Challenge at step `b − 1`, collection at steps `≥ b`. |
| `rTcr` | Collection at step `b − 1`, challenges at steps `b … w−2` (≤ `w − 1` per chain). |

Efficiency. What can be claimed: each reduction is black-box and straight-line with a single run
of `A`; the numbers of game-oracle queries are bounded as in the table (three of them by pending
lemmas, the rest by the caps the games enforce); the advantage loss is tight (coefficient 1 except
`w − 2` on UD). What cannot be claimed: any running-time statement. VCVio has no cost model, the
adversaries are `noncomputable` and depend on `Classical.choice`, and `bPrfMsg, bItsr, bOpenPre,
bTcr, bWots` begin with `sampleTable`, an eager draw of `2^256` values (`Games.lean:32, 47-48`).
That is far above the paper's reductions (which evaluate the whole key structure, about `2^79`
hash calls for 128s) and above brute force on a 128-bit hash. The sentence "explicit but not
efficient, exactly like the paper's" (`REDUCTION_STATUS.md` §3, `TCR.lean:18`) is therefore
inaccurate. The honest reading is: the Lean theorem is an inequality between advantages of
explicit adversaries; that these correspond to algorithms of cost "`A` plus one evaluation of the
key structure" rests on the informal observation that only the table entries at the structure's
secret addresses are ever read, so the table could be sampled lazily.

---

## Defects

### Fatal
None found.

### Must-fix

**M1. The adversaries named in the final statement are not frozen.** `slhdsa_euf_cma` mentions
`bPrf, bPrfMsg, bItsr, bOpenPre, bTcr, bWots, rUd, rPre, rTcr` by name, but
`REDUCTION_STATUS.md` §6 lets each package revise its adversary. A revision made to get a step
through (a second run of `A`, an unbounded search, a `Classical.choose`) would change the meaning
of the theorem without changing a frozen file, and `#print axioms` cannot detect it because all
of them already depend on `Classical.choice`. `structureVia` already uses `Finset.univ.toList`
(`TCR.lean:38`), an order obtained by choice.
Fix: treat the nine definitions (and `structureVia`, `signFromHist`, `forsSigFromImages`, the
`…Answer` extractors) as part of the statement; diff and re-audit them when the proofs land;
replace `Finset.univ.toList` by `allXmssTrees vp`; add a grep gate against
`Classical.choose|epsilon|Exists.choose|Finset.toList` in adversary bodies.

**M2. Efficiency wording.** As described under Q4.
Fix (minimal): correct `REDUCTION_STATUS.md` §3 and the `TCR.lean`/`Final.lean` docstrings to
state that no running-time claim is formalised and that the table is an eager `2^256`-entry
sample. Fix (better, later): index `SecretTable` by the finite ledger of secret-key addresses, or
prove that every reduction's output depends only on the table entries at those addresses.

### Notes

- N1. Scope: FIPS 205 internal algorithms only; EUF-CMA only (SUF-CMA not covered).
- N2. `q_s` does not appear in the bound; a concrete bound needs `bPrf_queryBound`,
  `bPrfMsg_queryBound`, `bItsr_queryBound` (all open; `skPrfQueries` is an unchecked estimate).
  Consider a corollary that packages them.
- N3. No corollary at uniform `PK.seed`; add one, since that is the FIPS scheme (see D3).
- N4. D1, D2, D4, D5 above should be stated next to the theorem, in particular that the TCR
  assumption on `Thash` is cross-arity.
- N5. Several reductions read a refused oracle answer as `default`. The no-refusal lemmas
  (`honestCalls_nodup_length`, `forsLeafKeys_nodup_length`, and the unstated analogues for `bWots`,
  `rUd`, `rPre`, `rTcr`: `wotsInsts` distinct under `adrsToKey`, length ≤ `wotsInstanceCount`) are
  load-bearing and should be stated explicitly for every reduction.
- N6. `preTargetIndex` / `tcrTargetIndex` assume `Vector.ofFnM` runs in increasing index order
  (already listed as risk 1).
- N7. `stepWotsEmbed` has no stated simulation lemmas yet; it is the step most likely to expose a
  problem in the frozen `WotsGame`. I found none.
- N8. `NonVacuity` has no statement for UD, OpenPRE or PRF_msg, and all five are `sorry`.
  The stated ones are correct as statements (`itsr_trivial_adv_zero` relies on `k > 0`, which
  `Params.Valid` gives).
- N9. `StepWotsUD` is trivial for `w = 2`; `udReal_rUd`/`udIdeal_rUd` correctly assume `3 ≤ w`.
- N10. `structural_128s` is open; until it is proved the 128s instance rests on it.
