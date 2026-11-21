# Package A → B / C1 / lead interface (final)

(Note added by the W6 documentation sweep) "Headline" below is the intermediate `slhdsa_euf_cma_v2`; current theorems: `slhdsa_*_cma_final_split`, `Reduction/HeadlineSplit.lean`.

## OpenPRE slot
A introduces NO new OpenPRE game. The FORS-leaf summand of `slhdsa_euf_cma_v2` is
`TweakableHash.SM_DT_OpenPRE_SourceFinalValidity.advantage (Reduction.Lazy.bOpenPreS A)` with
`Lazy.bOpenPreS A : …Adversary (forsOpenPreProblem vp prims pkSeedDist)`
(`= bOpenPreWith (Lazy.sparseOn vp prims (Lazy.wotsSkIdx vp)) A`, Reduction/Lazy/OpenPreSparse.lean),
so B's generic lemma about an arbitrary adversary of that problem applies (4th argument of
`Reduction.boundV2`). Useful facts for B: `Lazy.bOpenPreS_targets` (commits `forsLeafKeys`, distinct,
length `openPreTargets vp`), `Lazy.bOpenPreS_pick_queryBound` (no collection query),
`Lazy.bOpenPreS_find_queryBound` (≤ qs·k openings).

## Headline for integration (Reduction/FinalV2.lean, Instance128sV2.lean)
`Reduction.slhdsa_euf_cma_v2' (hS) : ∀ A : Forger vp prims optRand pkSeedDist,
  SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ betaV2 A` — the shape C1's
`external_bound_of_internal_bound` takes; `betaV2 A = boundV2 pkSeedDist (bPrfC A) (Lazy.bPrfMsgL A)
(Lazy.bItsrL A) (Lazy.bOpenPreS A) (Lazy.bTcrS A) (rUd … (Lazy.bWotsS A)) (rPre …) (rTcr …)`;
`boundV2` = `bound` with the PRF advantage in `skPrfC` (domain `PkSeed × SkAdrs vp`).
128s: `slhdsa_sha2_128s_euf_cma_v2`, `…_v2'`, `…_v2_resources`.
No A file imports `ForsTight*`, `Suf*`, `TcrSplit*`, `External`.

## Why no adaptive / poly(qs) variant of the SM reductions
See status/A.md §(2c): in all four SM games targets are registered only in the seed-less first
phase, and the forger needs the seed; only `bPrfC`, `bPrfMsgL`, `bItsrL` are poly(qs).
