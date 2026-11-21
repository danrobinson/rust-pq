# Package A (phase 2): canonical-domain PRF game, table-free reductions, resources

(Note added by the W6 documentation sweep) "Headline" below is the intermediate theorem `slhdsa_euf_cma_v2`; the current theorems are `slhdsa_*_cma_final_split` (`Reduction/HeadlineSplit.lean`, `status/FINAL2.md`). On resources: only `bPrfC`, `bPrfMsgL`, `bItsrL` are poly(`qs`). The local hashing of the SM adversaries after the seed reveal, listed below as not formalised, is counted in `Reduction/Resources2*.lean` (`status/W3.md`): `bTcrS A` recomputes the whole key structure there (exactly `tcrTargets`, `≈ 2^79.81` hash evaluations at 128s), so its own hashing is not small.

All files below are NEW; no existing file was edited; `lake build Reduction.Instance128sV2
Reduction.Resources Reduction.PrfDomainNonVacuity` succeeds (old modules untouched, still built).
No `sorry`/`axiom`/`native_decide`/`bv_decide` under `Reduction/`. `#print axioms` of every theorem
named here: `[propext, Classical.choice, Quot.sound]`. Sub-reports: `status/A-prf.md` (PRF game +
audit of the other seven games), `status/A-lazy.md` (lazy adversaries), `status/A-docfixes.md`
(29 overclaiming docstrings in existing files with corrected text, for the lead to apply).

## Headline (Reduction/FinalV2.lean, Reduction/Instance128sV2.lean)

```lean
noncomputable def boundV2 pkSeedDist B₁ … B₈ : ℝ≥0∞   -- `bound` with (skPrfC vp prims).prfAdvantage B₁ as first summand
noncomputable def betaV2 (A : Forger vp prims optRand pkSeedDist) : ℝ≥0∞ :=
  boundV2 pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A) (Lazy.bItsrL A) (Lazy.bOpenPreS A) (Lazy.bTcrS A)
    (rUd pkSeedDist (Lazy.bWotsS A)) (rPre pkSeedDist (Lazy.bWotsS A)) (rTcr pkSeedDist (Lazy.bWotsS A))
theorem slhdsa_euf_cma_v2 (hS : Structural vp prims) (A : Forger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ boundV2 pkSeedDist (bPrfC A) … (as betaV2 unfolded)
theorem slhdsa_euf_cma_v2' (hS) : ∀ A : Forger …, SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaV2 A
theorem slhdsa_euf_cma_v2_resources (hS) A qs (hA : ∀ pk, IsQueryBoundP (A.main pk) (·.isRight = true) qs) : bound ∧ query counts
theorem slhdsa_sha2_128s_euf_cma_v2 optRand pkSeedDist A : … ≤ boundV2 …      -- no hypothesis but the forger
theorem slhdsa_sha2_128s_euf_cma_v2' optRand pkSeedDist : ∀ A, Adv A ≤ betaV2 A
theorem slhdsa_sha2_128s_euf_cma_v2_resources … -- counts as numerals: 17920 + qs*182784, qs, qs, qs*14
```
Proof: `final_of_steps` at the new adversaries (`stepPRF`, `Lazy.stepPRFmsg_lazy`, `stepSplit`,
`Lazy.stepITSR_lazy`, `Lazy.stepOpenPRE_sparse`, `Lazy.stepTCR_sparse`, `Lazy.stepWotsEmbed_sparse`,
the W-generic `stepWotsUD`/`stepWotsFinal`), then the equality `prfAdvantageC_eq`.
`slhdsa_euf_cma_v2'` is in the form `external_bound_of_internal_bound` (C1) wants. `Lazy.bOpenPreS A`
is an `Adversary (forsOpenPreProblem vp prims pkSeedDist)`, so B's generic lemma applies to slot 4.

No eager object: `scratch/A/EagerCheck.lean` (kept; follows definition bodies, not proofs) reports that
`bPrfC`, `bPrfMsgL`, `bItsrL`, `bOpenPreS`, `bTcrS`, `bWotsS`, `rUd`, `rPre`, `rTcr` reach none of
`sampleTable`, `Tables.uniformTable`, `Fin.mOfFn`, `Fintype.mPi`, `Classical.choice`,
`Exists.choose`, `Fintype.equivFin` (control: old `bPrfMsg` is flagged for `sampleTable`).

## (1) PRF game (Reduction/PrfDomain.lean, PrfDomainNonVacuity.lean) — see A-prf.md

Correction to the brief: `⟨256,0,0,0,0,0⟩` IS `isCanonical` (4-byte layer); the SHA-2 PRF falls back
outside `Sha2Domain` (1-byte layer, 8-byte tree). So the domain is
`SkDom vp a := a.isCanonical ∧ a.IsSecretKey (type WOTS_PRF/FORS_PRF) ∧ a.layer < d ∧ a.tree < 2^((d-1)·h')`,
`SkAdrs vp := {a // SkDom vp a}`, `skPrfC vp prims : PRFScheme SkSeed (PkSeed × SkAdrs vp) Y`.
`bPrfC A := simulateQ (Restrict.restrictImpl (skRestrict vp prims)) (bPrf A)` (out-of-domain branch
answers `default` and is never taken: `queriesIn_bRestC`). `prfAdvantageC_eq`, `stepPRFC`,
`bPrfC_queryBound_exact`. Non-vacuity: `prfC_const_adv_zero`, `toy_prfC_lost`, `prfTesterC_adv`,
`toy_prfC`. Old distinguisher excluded: `not_skDom_256`, `not_skDom_of_not_sha2Domain`,
`sha2PRFChecked_ok_128s` (on `SkAdrs Link.vp` the PRF is the genuine SHA-256 expression, never the
fallback), `prf_128s_spec`. Old game provably broken at 128s: `skPrf_broken_128s`
(advantage `= 1 − 1/|Y|`). Other seven games: no out-of-domain artefact (A-prf.md, with file/line).

## (2a) Table-free adversaries

- Generic: `Reduction/Lazy/Core.lean` (kept from the previous owner: open programs over
  `RSpec`, lazy association-list cache, `evalDist_lazyRun_eq_table` lazy = eager under any game
  handler, resource transfer). `Reduction/Lazy/Sparse.lean` (rewritten and finished; the old
  `dedup`-based draft is gone): `sparseOn vp prims is` = `is.length` uniform values at the cells
  `is`, `default` elsewhere; `evalDist_sparseOn_bind/_perm/_extract`, `idealRoot_restrictTo`,
  `idealSign_restrictTo`, `prTrue_g2Class_eq_sparse`.
- `Lazy.bPrfMsgL`, `Lazy.bItsrL` (Open.lean, MsgLazy.lean, ItsrLazy.lean): truly lazy; advantage
  EQUAL to the old ones (`prfAdvantage_bPrfMsgL`, `itsrAdvantage_bItsrL`).
- `Lazy.bOpenPreS := bOpenPreWith (sparseOn (wotsSkIdx vp))` (only WOTS+ cells; FORS secrets are the
  game's), `Lazy.bTcrS := bTcrWith (sparseTable)` (all structure cells), `Lazy.bWotsS :=
  bWotsWith (sparseOn (forsSkIdx vp))` (only FORS cells; WOTS+ starts are the game's). Steps
  re-proved for the sparse samplers (not via advantage equality).

## (2b) Resource table (`qs` = signing queries of `A`; #inst = (wotsInsts vp).length = Σ_{j<d} 2^(h−j·h'))

| adversary | game | count, closed form | at 128s | lemmas |
|---|---|---|---|---|
| `bPrfC A` | PRF (SkAdrs) | oracle queries ≤ 2^h'·len + qs·(k·2^a + d·2^h'·len); no secret samples | 17920 + qs·182784 | `bPrfC_queryBound_exact`, `Resources.keygenReads_128s`, `signReads_128s` |
| `bPrfMsgL A` | PRF_msg | queries ≤ qs; fresh draws (= cache size) ≤ 2^h'·len + qs·signReads; hash evals (keygen+sign) ≤ keygenHashes + qs·signHashes | qs; 17920 + qs·182784; 269824 + qs·2007385 | `Lazy.bPrfMsgL_queryBound`, `_draws`, `_hashes`; `keygenHashes_128s`, `signHashes_128s` |
| `bItsrL A` | ITSR | targets ≤ qs; draws, hashes as above | same | `Lazy.bItsrL_queryBound`, `_draws`, `_hashes` |
| `bOpenPreS A` | SM-DT-OpenPRE(F) | commitments = 2^h·k·2^a exactly, distinct, 0 collection queries; openings ≤ qs·k; samples = #inst·len | 2^63·14·2^12 ≈ 2^78.8; 14·qs; ≈ 2^68.1 | `Lazy.bOpenPreS_targets`, `_pick_queryBound`, `_find_queryBound` (new: closes FINAL limitation 8), `_pick`; `Resources.openPreTargets_128s(_val,_bounds)`, `wotsChainTargets_128s_val` |
| `bTcrS A` | SM-TCR(Thash) | targets = tcrTargets = 2^h(k(2^(a+1)−1)+1) + #inst(len(w−1)+1) + 2^h−1 exactly, distinct tweaks, none refused; samples = 2^h·k·2^a + #inst·len | 1062560399506556770327551 ≈ 2^79.81; ≈ 2^78.81 | `Lazy.bTcrS_choose_run`, `bTcrS_targets`, `sparseTable_eq`, `structSecIdx_length`; `Resources.tcrTargets_eq`, `tcrTargets_128s_val`, `structPrfEvals_128s` |
| `bWotsS A` | WOTS game (internal) | signing queries: each instance at most once, all in wotsInsts (≤ #inst); samples = 2^h·k·2^a | ≈ 2^63.003; ≈ 2^78.8 | `Lazy.bWotsS_choose_signed`, `bWotsS_chooseBody_signed`, `bWotsS_choose_eq`, `bWotsS_sampleCount`; `Resources.wotsInsts_length_128s` |
| `rUd (bWotsS A)` | SM-UD(F) | challenges ≤ #inst·len (every W, both worlds) | 323449759100660631040 ≈ 2^68.13 | `Resources.rUd_challenges_le(_cap,_128s)` |
| `rPre (bWotsS A)` | SM-PRE(F) | challenges ≤ #inst·len | same | `Resources.rPre_challenges_le…` |
| `rTcr (bWotsS A)` | SM-TCR(F) | targets ≤ #inst·len·(w−1) (cap #inst·len·w) | 4851746386509909465600 ≈ 2^72.04 | `Resources.rTcr_targets_le…`, `wotsExecutedSteps_128s` |

Hash evaluations. VCVio's cost machinery (`CostModel`, `IsQueryBoundP`, `withAddCost`, …) charges
oracle queries only; pure code is free. We therefore model local hashing as queries to an oracle
`hspec` interpreted in `Id` (`Lazy/Core.lean`); this gives PROVED hash counts for `bPrfMsgL`,
`bItsrL` (upper bounds; the one final `verifyInternal` and list work are not counted). For the
three structure walkers the count is a closed form only: `Resources.structHashEvals` (= `tcrTargets`,
≈ 2^79.81 at 128s, `structHashEvals_128s`) with the counting argument in the module doc — a count
of the expression, not a theorem about a program.

## (2c) Stretch: not reachable, and why (exactly what is / is not efficient)

Efficient (poly(qs), proved): `bPrfC`, `bPrfMsgL`, `bItsrL`; the opening count of `bOpenPreS`.
Not efficient: `bOpenPreS` (commitment list 2^78.8), `bTcrS` (2^79.8 targets), `bWotsS` and hence
`rUd/rPre/rTcr` (2^63 instances). Obstacle: in VCVio's `SM_DT_TCR_Adversary`, `SM_DT_PRE_Adversary`,
`SM_DT_UD_Adversary` and `SM_DT_OpenPRE_SourceFinalValidity.Adversary` the first phase
(`choose`/`pick`, where targets are registered — adaptively in TCR/PRE/UD, as a list in OpenPRE) has
no access to `PK.seed`, and the second phase (`forge`/`invert`/`distinguish : State → PkSeed →
ProbComp _`; OpenPRE `find` has only the opening oracle) cannot register targets. The forger takes
`pk ∋ PK.seed` as input, so any reduction can run it only in phase 2, i.e. after ALL targets are
fixed; targets cannot depend on the forger's queries or forgery and must cover the whole structure
(or lose a 2^-h guessing factor). SM-TCR's adaptivity is therefore of no use here; this holds for
all four games (TCR, OpenPRE, UD, PRE) and matches HK22/EasyCrypt. A poly(qs) reduction needs a
different game (targets after the seed), which for TCR is plain collision resistance (birthday
2^(n/2)). Not formalised as a theorem (it is a statement about all reductions); it is read off the
four structure definitions.

## Not achieved / caveats

- Local computation cost of `bOpenPreS/bTcrS/bWotsS` is not formalised; their sparse table is a
  function defined by linear list lookup (`Tables.updateList`), so "as written" each secret read
  scans the list. An indexed layout would fix it; not done.
- `bOpenPreS` reads only top-tree/path WOTS+ cells but samples all #inst·len of them (a lazy cache in
  `find` via Core would make its sampling poly(qs); not done — commitment count dominates anyway).
- No formal count of collection-oracle queries or own uniform samples of `bWotsS.choose`, `rUd`,
  `rPre`, `rTcr` (doc-comment arguments in WotsSparse.lean/Resources.lean). "Every instance signed
  exactly once" is proved against the table-reading oracles; in the game itself: at most once.
- Samplers `pkSeedDist`, `optRand` and the forger's randomness are not counted.
- A-docfixes.md refers to pre-existing files only.
