# Package D (REDUCTION) — report

All of Task 1 (a)–(e) and Task 2 are done; `lake build MReduction MLink.Security` succeeds, no `sorry`,
`axiom`, `native_decide`, `bv_decide`; all 380 `#print axioms` lines of my modules (one per generated headline and resource theorem) are within
`[propext, Classical.choice, Quot.sound]`. No statement of the early interface (`status/D-interface.ok`)
changed; `MReduction/Explicit.lean`, `Audit.lean`, `Check128s.lean` were added after it.

## Files

| file | content |
|---|---|
| `MReduction/Instances.lean` | `structural S`, `keyDiscipline S`, `codec S`, `detRand S`, `instInhabitedY S`, `instFintypeY S`; rfl checks |
| `MReduction/Headline.lean` (generated) | final headlines, compact right-hand side (`betaSufFinalMemo …`/`betaEufFinalMemo …`), 24 bases × (generic + 6 sets) |
| `MReduction/Explicit.lean` (generated) | the four byte-level final headlines with `boundFinalTight` and its twelve adversaries written out |
| `MReduction/Linear.lean` (generated) | linear forms, 8 bases × 7 |
| `MReduction/HeadlineOld.lean` (generated) | `_final_tight`, `_final_split`, split byte forms (superseded; came for free), 12 bases × 7 |
| `MReduction/Resources.lean` (generated) | numerals per set, `final_resources_final_<set>` |
| `MReduction/Audit.lean` | which function each term is about; arities; PRF domain; non-vacuity |
| `MReduction/Check128s.lean` | at `.s128s` the statements are those of `security/Reduction` (`rfl`) |
| `MLink/Security.lean` | random-oracle statement and program identities, generic in `S` |

Generators (copies in `MReduction/gen/*.py`, not part of the build; the generated files are self-contained; `gen_sec.py`
produced the first draft of `MLink/Security.lean`, which was then edited by hand). They copy the `*_128s` statements of `security/Reduction` and substitute
`Link.vp ↦ S.vp`, `Link.prims ↦ S.prims`, `codec128s ↦ codec S`, `structural_128s ↦ structural S`.

## (a) Instances

```lean
theorem MReduction.structural (S : Sha2Set) : Reduction.Structural S.vp S.prims
theorem MReduction.keyDiscipline (S : Sha2Set) : S.prims.core.KeyDiscipline S.vp
abbrev  MReduction.codec (S : Sha2Set) : CoreWireCodec S.vp.params S.prims.core := SLHDSA.Concrete.sha2WireCodec S.vp.params
theorem MReduction.detRand (S) (s : S.prims.PkSeed) : SLHDSA.Concrete.sha2RandomizerOfPkSeed S.vp.params s = s   -- rfl
instance MReduction.instInhabitedY (S) : Inhabited S.prims.Y      -- all-zero node
instance MReduction.instFintypeY (S) : Fintype S.prims.Y
```
`SampleableType` on `SkSeed`, `SkPrf`, `Y`, `PkSeed` and `DecidableEq` on `Y`, `PkSeed`, `AdrsKey` are VCVio's instances
for `sha2Primitives p` (checked by `example`s). `codec S = approvedWireCodec S.fips` by `rfl` at each of the six sets
(`codec_heq_approved` generically); `Sha2Set.s128s.vp = Link.vp`, `.prims = Link.prims`, `codec .s128s = Reduction.codec128s`,
`structural .s128s = Reduction.structural_128s`, the `Fintype`/`Inhabited` instances: all `rfl`.

## (b) Headlines — naming

`MReduction.slhdsa_sha2_<base> (S : Sha2Set) …` (generic) and `MReduction.slhdsa_sha2_<set>_<base>`
(`<set>` ∈ 128s, 128f, 192s, 192f, 256s, 256f; stated at `Sha2Set.s128f.vp` etc., so `#check` shows the set). `<base>`:

- `{bytes,pure_bytes}_{suf,euf}_cma_final` (and `…_final_explicit`, twelve terms written out),
- `{suf,euf,pure_suf,pure_euf}_cma_final_memo`,
- `{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}` (16; `toY = sha2RandomizerOfPkSeed S.vp.params`, the identity: `detRand`),
- `{suf,euf,pure_suf,pure_euf}_cma_final_linear`, `{bytes,pure_bytes}_{suf,euf}_cma_linear`,
- `{suf,euf,pure_suf,pure_euf}_cma_final_tight`, `…_final_split`, `{bytes,pure_bytes}_{suf,euf}_cma` (superseded forms).

The strong forger is called `F` (the originals call it `S`). Example, verbatim:

```lean
theorem slhdsa_sha2_bytes_suf_cma_final (S : Sha2Set)
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (F : BytesStrongForger S.vp S.prims (codec S) optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
      betaSufFinalMemo (bytesToTypedS F).toUnforgeableAdversary
theorem slhdsa_sha2_256f_bytes_suf_cma_final
    (optRand : PublicKeyCore Sha2Set.s256f.prims.core → ProbComp Sha2Set.s256f.prims.Y)
    (pkSeedDist : ProbComp Sha2Set.s256f.prims.PkSeed)
    (F : BytesStrongForger Sha2Set.s256f.vp Sha2Set.s256f.prims (codec Sha2Set.s256f) optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
      betaSufFinalMemo (bytesToTypedS F).toUnforgeableAdversary
theorem slhdsa_sha2_bytes_suf_cma_final_explicit (S : Sha2Set) (optRand …) (pkSeedDist …)
    (F : BytesStrongForger S.vp S.prims (codec S) optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp F ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (bytesToTypedS F).toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck (bytesToTypedS F).toUnforgeableAdversary)
        (Lazy.bItsrL (bytesToTypedS F).toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS (bytesToTypedS F).toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS (bytesToTypedS F).toUnforgeableAdversary))
        (bTcrArM 1 …) (bTcrArM 2 …) (bTcrArM S.vp.params.len …) (bTcrArM S.vp.params.k …)
        (rUd pkSeedDist (Lazy.bWotsS …)) (rPre pkSeedDist (Lazy.bWotsS …)) (rTcrT pkSeedDist (Lazy.bWotsS …))
```
Every theorem is the generic `Reduction` theorem at `structural S` (one-line proofs).

## (c) Resources (`MReduction/Resources.lean`)

Generic: `final_resources_final_sha2 S`, `final_resources_final_external_sha2 S` (parameter expressions).
Per set `<set>`: `params_<set>`, `xmssTreeCount_`, `wotsInstanceCount_`, `allXmssTrees_length_`, `wotsInsts_length_`,
`openPreTargets_<set>(_val,_bounds)`, `wotsChainTargets_<set>(_val,_bounds)`, `wotsStepTargets_<set>(_val)`,
`wotsExecutedSteps_<set>(_bounds)`, `tcrTargets_<set>(_val,_bounds)`, `signReads_`, `keygenReads_`, `structHashEvals_`,
`structPrfEvals_`, `keygenHashes_`, `signHashes_`, `verifyHashes_`, `forsSignHashes_`, `wotsSignHistHashes_`,
`wotsWinHashes_`, `wotsPreHashes_`, `wotsTcrHashes_`, `arityTargets_<set>`, `thashArityProblemT_cap_<set>`,
`wotsTcrProblemT_cap_<set>`, `otherCaps_<set>`, `directCounts<set>` (def), `directCounts_<set>`,
`final_resources_final_<set>`, `final_resources_final_external_<set>`. Proofs as at 128s (`decide`/`rfl`/`simp` on
closed forms; the whole file checks in about 3 s). `directCounts128s = Reduction.Resources2.directCounts128s` by `rfl`.

```lean
theorem final_resources_final_256f (optRand …) (pkSeedDist …)
    (A : Forger Sha2Set.s256f.vp Sha2Set.s256f.prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    FinalResourcesFinal A qs (directCounts256f qs) (16112 + qs * 327266 + 35043) ∧
    ((thashArityProblemT … 1).numTargets = 5605449015166268868656080 ∧ … ) ∧
    ((wotsTcrProblemT …).numTargets = 316398554352266229316560 ∧ (wotsTcrProblem …).numTargets = 337491791309083977937664)
```

### Numerals per set

| quantity | 128s | 128f | 192s | 192f | 256s | 256f |
|---|---|---|---|---|---|---|
| `n, h, d, h', a, k, m` | 16, 63, 7, 9, 12, 14, 30 | 16, 66, 22, 3, 6, 33, 34 | 24, 63, 7, 9, 14, 17, 39 | 24, 66, 22, 3, 8, 33, 42 | 32, 64, 8, 8, 14, 22, 47 | 32, 68, 17, 4, 9, 35, 49 |
| `len` (= 2n+3) | 35 | 35 | 51 | 51 | 67 | 67 |
| `w − 2` (UD coefficient) | 14 | 14 | 14 | 14 | 14 | 14 |
| signature bytes | 7856 | 17088 | 16224 | 35664 | 29792 | 49856 |
| XMSS trees | 18049651735527937 ≈ 2^54.00 | 10540996613548315209 ≈ 2^63.19 | 18049651735527937 ≈ 2^54.00 | 10540996613548315209 ≈ 2^63.19 | 72340172838076673 ≈ 2^56.01 | 19676527011956855057 ≈ 2^64.09 |
| WOTS instances | 9241421688590303744 ≈ 2^63.00 | 84327972908386521672 ≈ 2^66.19 | 9241421688590303744 ≈ 2^63.00 | 84327972908386521672 ≈ 2^66.19 | 18519084246547628288 ≈ 2^64.01 | 314824432191309680912 ≈ 2^68.09 |
| cap FORS-leaf DSPR/TCR (`openPreTargets` = 2^h·k·2^a) | 528905046081400263933952 ≈ 2^78.81 | 155838093934698292051968 ≈ 2^77.04 | 2568967366681086996250624 ≈ 2^81.09 | 623352375738793168207872 ≈ 2^79.04 | 6649092007880460460883968 ≈ 2^82.46 | 5289050460814002639339520 ≈ 2^82.13 |
| cap class `1` (F) `arityTargets 1` | 533756792467910173399552 ≈ 2^78.82 | 200110279711601215929768 ≈ 2^77.41 | 2576037054272858578614784 ≈ 2^81.09 | 687863275013708857286952 ≈ 2^79.19 | 6667703687548240827313408 ≈ 2^82.46 | 5605449015166268868656080 ≈ 2^82.21 |
| cap class `2` (H) | 528785142244921151848447 ≈ 2^78.81 | 153476910693263469445119 ≈ 2^77.02 | 2568819792728497319837695 ≈ 2^81.09 | 620991192497358345601023 ≈ 2^79.04 | 6648704626254912560300031 ≈ 2^82.46 | 5279015432037904643260415 ≈ 2^82.13 |
| cap class `len` (T_len) | 9241421688590303744 ≈ 2^63.00 | 84327972908386521672 ≈ 2^66.19 | 9241421688590303744 ≈ 2^63.00 | 84327972908386521672 ≈ 2^66.19 | 18519084246547628288 ≈ 2^64.01 | 314824432191309680912 ≈ 2^68.09 |
| cap class `k` (T_k) | 9223372036854775808 = 2^63 | 73786976294838206464 = 2^66 | 9223372036854775808 = 2^63 | 73786976294838206464 = 2^66 | 18446744073709551616 = 2^64 | 295147905179352825856 = 2^68 |
| loose cap `tcrTargets` (sum of the four) | 1062560399506556770327551 ≈ 2^79.81 | 353745305354067910103023 ≈ 2^78.23 | 5144875311795081343532031 ≈ 2^82.09 | 1309012582460270427616111 ≈ 2^80.11 | 13316445279631473644793343 ≈ 2^83.46 | 10885074419541544174423263 ≈ 2^83.17 |
| cap WOTS UD/PRE (`#inst·len`) | 323449759100660631040 ≈ 2^68.13 | 2951479051793528258520 ≈ 2^71.32 | 471312506118105490944 ≈ 2^68.68 | 4300726618327712605272 ≈ 2^71.87 | 1240778644518691095296 ≈ 2^70.07 | 21093236956817748621104 ≈ 2^74.16 |
| cap chain TCR tight (`#inst·len·(w−1)`) | 4851746386509909465600 ≈ 2^72.04 | 44272185776902923877800 ≈ 2^75.23 | 7069687591771582364160 ≈ 2^72.58 | 64510899274915689079080 ≈ 2^75.77 | 18611679667780366429440 ≈ 2^73.98 | 316398554352266229316560 ≈ 2^78.07 |
| cap chain TCR loose (`#inst·len·w`) | 5175196145610570096640 ≈ 2^72.13 | 47223664828696452136320 ≈ 2^75.32 | 7541000097889687855104 ≈ 2^72.68 | 68811625893243401684352 ≈ 2^75.87 | 19852458312299057524736 ≈ 2^74.07 | 337491791309083977937664 ≈ 2^78.16 |
| structure samples (`structCells`) | 529228495840500924564992 ≈ 2^78.81 | 158789572986491820310488 ≈ 2^77.07 | 2569438679187205101741568 ≈ 2^81.09 | 627653102357120880813144 ≈ 2^79.05 | 6650332786524979151979264 ≈ 2^82.46 | 5310143697770820387960624 ≈ 2^82.14 |
| hashes keygen (`keygenHashes`) | 269824 | 4216 | 392704 | 6136 | 257792 | 16112 |
| hashes per signature (`signHashes`) | 2007385 | 108847 | 3311666 | 169105 | 2791676 | 327266 |
| hashes per verification (`verifyHashes`) | 3928 | 11870 | 5681 | 17216 | 8443 | 17521 |
| PRF reads keygen / per signature | 17920 / 182784 | 280 / 8272 | 26112 / 461312 | 408 / 17424 | 17152 / 497664 | 1072 / 36144 |
| `bTcrArM` phase 2 ≤ | 269824 + qs·2007385 + 7857 | 4216 + qs·108847 + 23741 | 392704 + qs·3311666 + 11363 | 6136 + qs·169105 + 34433 | 257792 + qs·2791676 + 16887 | 16112 + qs·327266 + 35043 |
| FORS phase 2 ≤ | 269824 + qs·1950027 + (1 + qs + 14) | 4216 + qs·106702 + (1 + qs + 33) | 392704 + qs·3033121 + (1 + qs + 17) | 6136 + qs·160624 + (1 + qs + 33) | 257792 + qs·2431206 + (1 + qs + 22) | 16112 + qs·309311 + (1 + qs + 35) |
| UD / PRE / chain-TCR phase 2 ≤ qs·x + … | x = 121857; 525 / 560 / 16800 | x = 4577; 525 / 560 / 16800 | x = 564225; 765 / 816 / 24480 | x = 17249; 765 / 816 / 24480 | x = 724993; 1005 / 1072 / 32160 | x = 36385; 1005 / 1072 / 32160 |

(The ≈ values are computed outside Lean; `*_bounds` lemmas prove the integer part of log2 for `openPreTargets`,
`wotsChainTargets`, the executed steps and `tcrTargets`.) Not restated per set: the single-adversary numeral lemmas
`rUd_challenges_128s`, `rPre_…`, `rTcr_targets_…`, `findOpen(Full)_hashes_128s`, `tcrForgeOpen_hashes_128s`,
`memoForgeOpen_hashes_128s`, `final_memo_resources_128s`, `final_resources_direct_128s` (their content is in the fields
of `final_resources_final_<set>`), and the older `counts128s`.

## (d) Audit (`MReduction/Audit.lean`)

Which function each of the twelve terms is about:

| term | game | 128s, 128f (`n = 16`) | 192s, 192f, 256s, 256f (`n = 24, 32`) | backing lemma |
|---|---|---|---|---|
| 1 PRF | `skPrfC`, inputs `(PK.seed, a)`, `a ∈ SkAdrs` | `Trunc_n(SHA-256(PK.seed‖0^(64−n)‖ADRSc‖SK.seed))` | same (SHA-256) | `prf_spec`, `sha2PRFChecked_ok`, `prf_thash` |
| 2 PRF_msg | `msgPrf` | HMAC-SHA-256 | HMAC-SHA-512 | `prfMsg_spec` |
| 3 ITSR | `itsrProblem` on `H_msg` | MGF1-SHA-256 ∘ SHA-256 | MGF1-SHA-512 ∘ SHA-512 | `hmsg_spec` |
| 4, 5 DSPR, 3·TCR at FORS leaves | `forsDsprProblem`, `forsTcrProblem` on `fHash` | SHA-256 | SHA-256 | `fHash_eval` |
| 6 class `1` (F) | `thashArityProblemT … 1` | SHA-256 | SHA-256 | `thash_class` |
| 7 class `2` (H) | `thashArityProblemT … 2` | SHA-256, pad `64−n` | SHA-512, pad `128−n` | `thash_class`, `thash_class_sha512` |
| 8 class `len` (T_len) | `… len` | SHA-256 | SHA-512 | same |
| 9 class `k` (T_k) | `… k` | SHA-256 | SHA-512 | same |
| 10–12 UD (×14), PRE, chain TCR | `wotsUdProblem`, `wotsPreProblem`, `wotsTcrProblemT` on `fHash` | SHA-256 | SHA-256 | `fHash_eval`, `problem_th` |

The same table is in the docstring of every per-set headline. Findings:

1. **The four arities are pairwise distinct at every set** (`arities_pairwise`, `arities_injective`):
   `(len, k)` = (35,14), (35,33), (51,17), (51,33), (67,22), (67,35) (`len_k`). So the four class terms are four
   different games everywhere, and at `n = 24, 32` classes `2`, `len`, `k` contain no singleton, hence are purely
   SHA-512 (`thash_class_sha512`); VCVio's "singleton ⇒ F formula" rule never touches `H`, `T_len`, `T_k`.
2. **The collection oracle of every SM game is the whole `Thash`** (`thashColl`): at `n = 24, 32` an adversary against
   an "F" (SHA-256) game may also query the SHA-512 functions and vice versa. The games are well defined, but
   "SM-TCR of F" at those sets is a statement about SHA-256 targets with a mixed SHA-256/SHA-512 collection. Likewise
   the loose cap `tcrTargets` and the phase-1 structure walk of `bTcrArM` mix both functions.
3. `Structural` holds at every set by the same three VCVio lemmas as at 128s; `fipsApprovedAddressBounds` is proved by
   cases over all twelve FIPS sets and covers 256f, where `(d−1)·h' = 64` exactly (`treeBits`: `≤ 64` everywhere,
   `= 64` iff 256f). Total XMSS tree count at 256f exceeds `2^64` (all layers together); per-layer indices fit.
4. PRF domain: `skAdrs_dom S`, `sha2PRFChecked_ok S` (no fallback on `SkAdrs S.vp`), `prf_thash S`, `prf_spec S`
   (the generic form of the omitted `prf_128s_spec`, via `MLink.PRF_eq`), `not_skDom_badAdrs S`, `prf_256_eq_zero S`,
   `skPrf_broken S` (the unrestricted game `skPrf`, not used by any final theorem, is broken at every set).
   `not_skDom_of_not_sha2Domain`, `not_skDom_256`, `canonical_256` were already generic.
5. No generic `Reduction` definition or theorem bakes in a 128s numeral or instance: the only `Bytes 16` instances
   (`instance : Inhabited Link.prims.Y`, `instFintypeY128s`) are for `Link.prims`; generic statements take
   `[Inhabited prims.Y] [Fintype prims.Y]` as class arguments, no hypothesis on `vp.params` beyond `Structural`.
   `w − 2 = 14` at every set (`w_sub_two`). At `.s128s` two `Inhabited` instances apply (theirs and
   `instInhabitedY .s128s`); they are definitionally equal (`Check128s.lean`: ten statements equal by `rfl`).
6. Sign/verify cost differs qualitatively at the f-sets (verification 11870–17521 hashes vs 4216–16112 for keygen);
   only numerals, no proof impact.
7. `Reduction.ForsTightNonVacuity` (a root of the `Reduction` library) had not been compiled in this project; I built
   it (`lake build Reduction.ForsTightNonVacuity`, unmodified source) because `Audit.lean` imports it.
8. `status/A.md` did not exist when I started; `MLink/Hash.lean` was complete (no `sorry`) and is what I used.

## (e) Non-vacuity

The generic lemmas need no per-set version; `Audit.lean` states the instances: `games_can_be_lost S d n` (the four
class games, chain TCR, FORS TCR/DSPR, PRE, UD, PRF on `SkAdrs`, PRF_msg each have an adversary of advantage 0),
`class_game_winnable S` (`thashArityColliderT_adv_one` at `S`), `caps_pos S`. The "can be won" lemmas need a
seed-independent collision, available only for the toy bundles (`toy_*`, generic in `vp`), as at 128s. Not instantiated:
`itsr_trivial_adv_zero`, `wotsTcrColliderT_adv_one`, `forsDsprGuesser_*`, `udTester_adv`, `prfTesterC_adv` (generic,
apply as they are).

## Task 2 — `MLink/Security.lean` (namespace `MLink`, imports `MLink.Basic`; not added to `MLink.lean`)

`HashSigTest.SLHDSA.CoverageBound.strongUnforgeableAdvantage_sha2_le` is generic over `vp` with
`ApprovedAddressBounds`, so the port is one proof for all six sets:

```lean
theorem security_sha2 (S) (e : S.prims.SkSeed ≃ S.prims.Y) (optRand …) (pkSeedDist …)
    (adv : StrongUnforgeableAdversary (romScheme (vp := S.vp) S.prims.core e optRand pkSeedDist))
    {qh qs : ℕ} (hadv : adv.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) adv ≤
      securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs
theorem security_sha2_euf …            -- same bound, EUF
theorem verifyInternalM_impl_eq, romScheme_verify_eq, hprf_dom, not_hprf, dom_of_secretChild,
        keygenWithSecret_congr, signWithSecret_congr
theorem romScheme_map_romAnswer_sha2 (S) (optRand …) (pkSeedDist …) :
    (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer S.prims))) = internalAlg S.vp S.prims optRand pkSeedDist
```
`not_hprf S` is proved by `cases S <;> decide +kernel` (one SHA-256 evaluation per set, as in the original; not
`native_decide`). `badAdrs` is parameter-free. Differences from the original: `256 ^ 16 ↦ 256 ^ S.vp.params.n`,
`hprf_dom` needs no trailing `rfl`.

## Not done

- No per-set copies of the intermediate (pre-final) theorems other than those listed; `stepPRFC_128s`,
  `skPrf_broken_128s_half` not ported.
- The numerals table's log2 values are not Lean statements (only the `_bounds` lemmas are).
