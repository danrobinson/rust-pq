# GEN — the reduction for forgers over a general sampling spec

Everything below is proved and in the default build (`lake build Link E2E Reduction`): 24 new modules `Reduction/Gen/*.lean` (6.7k lines) + `E2E/HeadlineGen.lean`; no `sorry`, `axiom`, `native_decide`, `bv_decide`; no conditional theorem; no existing definition or theorem changed (only imports appended to `Reduction.lean`, `E2E.lean`). Brief for the sub-packages: `status/GEN-BRIEF.md`; interface note for quantum: `status/GEN-interface.md`.

## 1. Setting and scope
`ds : OracleSpec κ` is ANY oracle spec with `[OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]`; the forger's private randomness is `gSpec ds = ds + unifSpec` (at `ds := PQ.Interactive.distSpec` this is quantum's `privSpec`). Restriction actually made: **finite answer types** for `ds` (arbitrary real probabilities; `distSpec` qualifies). Not covered: answer measures on infinite types (the proof averages over the answers of a `ds`-query by a finite sum, and VCVio's `prEvent_bind` sum rule needs finite ranges).
Forger types are VCVio's own: `SignatureAlg.(Strong)UnforgeableAdversary (liftAlg ds alg)`, `liftAlg ds alg` = `alg` with its algorithms run through `liftR ds : ProbComp α → OracleComp (ds + unifSpec) α` (same definitions as quantum's `liftSig`, `liftR`; `liftSig sigAlg = liftAlg distSpec sigAlg := rfl`). Advantages: `eufAdvG ds A = 𝒟[SignatureAlg.unforgeableExperiment A] {true}`, `sufAdvG ds S = 𝒟[SignatureAlg.strongUnforgeableExperiment S] {true}` (VCVio's experiments and measure semantics; `eufAdvG_def`, `sufAdvG_def` by `rfl`).

## 2. Route: R2 (derandomisation through the linear form), made rigorous by a minimisation principle
Not re-proved: any hop of the 30k-line reduction. The naive induction on the forger's tree fails (signing queries sit between draws, and the twelve experiments have unrelated intermediate states). What works (`Reduction/Gen/Derand.lean`, pure discrete analysis):
- `Model`: a sub-stochastic stateful interpretation of the non-`ds` queries with a final payoff; `Model.val` = value of a program over `(ds + us) + X`, `ds`-queries averaged with weights `w`.
- `IsLin ds w b Φ`: the functional `Φ` of forger families `F : PK → OracleComp ((ds+us)+X) α` is a weighted sum (mass ≤ `b`) of model values at points of the family; closed under `+`, scalar multiples, weighted `tsum`.
- `Model.exists_resolution`: for two models and any program there is a program with an answer FIXED at every `ds`-query (`IsResolution`) such that `N(oa) + P(t) ≤ P(oa) + N(t)` (induction on the program quantified over ALL pairs of models and state weights — this is what makes the induction go through; at a `ds`-node pick the answer minimising `P − N`, at other nodes sum the children). Hence `IsLin.derand`: **an inequality `N ≤ P` between `IsLin` functionals that holds for all `ds`-free families holds for all families.**
- Bridge (`Sem.lean`): `Pr[true]` of "classical prefix; ONE run of the forger against a classical stateful handler (`runG`); classical suffix" is `IsLin` (`val_modelOf`, `isLin_run`, `isLin_liftR_bind`, `derandG`). `Run.lean`: `runG`/`runGO`/`wrapS`/`wrapFam` and fusion lemmas, so nested simulations are one run.
- Per term (packages P1–P5): the reduction adversary around a general forger family (same classical code, forger run through `runG`/`runGO`), NATURALITY (`…G_embed`: on an embedded classical forger it is the embedded classical adversary) and LINEARITY (`isLin_…`). Then `lin_transfer_{euf,suf}G` (`Headline.lean`) = `derandG` applied to the existing linear headline. R1 (generic re-proof) was rejected as a 25k-line duplication; R3 is what the adversary definitions are (only the forger-facing layer is general).

## 3. Statements (verbatim; `Reduction/Gen/Final.lean`, namespace `Reduction.Gen`; `hS : Structural vp prims` as before, proved at 128s)
```lean
theorem slhdsa_bytes_suf_cmaG (hS : Structural vp prims) (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A ≤ betaSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main
theorem slhdsa_bytes_suf_cma_linearG (hS : Structural vp prims) (A : GBytesStrongForger ds vp prims codec optRand pkSeedDist) :
    sufAdvG ds A + linIdealSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main ≤
      linRealSufG ds optRand pkSeedDist (bytesToTypedSG ds A).main
theorem slhdsa_suf_cmaG (hS : Structural vp prims) (S : GStrongForger ds vp prims optRand pkSeedDist) :
    sufAdvG ds S ≤ betaSufG ds optRand pkSeedDist S.main
```
`GBytesStrongForger … = SignatureAlg.StrongUnforgeableAdversary (liftAlg ds (bytesAlg vp prims codec optRand pkSeedDist))`, `GStrongForger` likewise for `internalAlg`. With `F : GFam ds vp prims` (forger programs indexed by the typed public key; `Headline.lean`):
```lean
betaSufG ds optRand pkSeedDist F = boundFinalTightG ds pkSeedDist (bPrfWCG … sufCheck F) (bPrfMsgWLG … sufCheck F) (bItsrLG … F)
    (toDsprG … F) (toTcrG … F) (bTcrArMG … 1 F) (bTcrArMG … 2 F) (bTcrArMG … vp.params.len F) (bTcrArMG … vp.params.k F)
    (rUdG … F) (rPreG … F) (rTcrTG … F)
boundFinalTightG ds pkSeedDist B₁ B₂ B₃ D T C₁ C₂ C₃ C₄ B₆ B₇ B₈ =
  prfAdvantageG ds (skPrfC vp prims) B₁ + prfAdvantageG ds (msgPrf vp prims) B₂ + ITSRAdvantageG ds B₃ +
    (dsprAdvantageG ds D + 3 * tcrFVAdvantageG ds T) +
    (SM_DT_TCR_AdvantageG ds C₁ + SM_DT_TCR_AdvantageG ds C₂ + SM_DT_TCR_AdvantageG ds C₃ + SM_DT_TCR_AdvantageG ds C₄) +
    ((vp.params.w - 2 : ℕ) : ℝ≥0∞) * SM_DT_UD_AdvantageG ds B₆ + SM_DT_PRE_AdvantageG ds B₇ + SM_DT_TCR_AdvantageG ds B₈
linIdealSufG … F = prfIdealPrG ds (bPrfWCG …) + prfIdealPrG ds (bPrfMsgWLG …) + dsprSPProbabilityG ds (toDsprG …) + (w−2) * SM_DT_UD_IdealSuccessG ds (rUdG …)
linRealSufG  … F = prfRealPrG … + prfRealPrG … + ITSRAdvantageG … + (dsprSuccessG … + 3 * tcrFVAdvantageG …) + (4 class terms) + (w−2) * SM_DT_UD_RealSuccessG … + SM_DT_PRE_AdvantageG … + SM_DT_TCR_AdvantageG …
```
(`linearIdealSideG`, `linearRealSideG` written out in `Headline.lean`; every term is `prG ds (experiment) = 𝒟[·] {true}`, no absolute value.) All variants, same shapes: `slhdsa_{,pure_}{,bytes_}{euf,suf}_cmaG` and `…_cma_linearG` (16 theorems; EUF uses `betaEufG`, `linIdeal/RealEufG` with `bPrfCG`, `bPrfMsgLG`; external/byte-level at `(toInternalG ds A).main`, `(bytesToTypedG ds A).main`, `(toInternalG ds (pureBytesToTypedG ds A)).main`, strong versions `…SG`); the absolute-value forms follow from the linear ones (`boundFinalTightG_of_linear`). 128s without hypothesis: `slhdsa_sha2_128s_{bytes,pure_bytes}_{euf,suf}_cma(_linear)G` (`Resolved.lean`). E2E: `E2E.rust_securityG`, `rust_pure_securityG` (part (a) = part (a) of the existing theorems, unchanged; (b), (c) as above), `rust_security_linearG`, `rust_pure_security_linearG`, `rust_security_resourcesG` (`E2E/HeadlineGen.lean`).
Extra (no wrapper game on the right): `slhdsa_{euf,suf}_cma_resolved` — for every general forger `A` there is a classical forger `A₀` with `IsResolution ds (A.main pk) (A₀.main pk)` for all `pk` (same signing-query bound, `IsResolution.queryBound`) and `eufAdvG ds A ≤ betaEufFinalMemo A₀` (the EXISTING bound, VCVio's games); generic: `exists_resolution_{euf,suf}` for any scheme. `A₀` is not constructive (it fixes the best coins).

## 4. Wrapper games (VCVio's files untouched)
Each: adversary type with EVERY phase over the general interface, VCVio's experiment with its classical parts under `liftR ds` and oracle phases under `runG ds <VCVio's oracle handler>`, value `prG ds (…)`.
| game | file | adversary / values | coincidence with VCVio on classical adversaries | non-vacuity (lost / won) |
|---|---|---|---|---|
| PRF (both `skPrfC`, `msgPrf`) | `GamePrf` | `PRFAdversaryG`; `prfRealPrG`, `prfIdealPrG`, `prfAdvantageG = absDiff real ideal` | `prfRealPrG_embed`, `prfIdealPrG_embed`, `prfAdvantageG_embed` (program level: `prf{Real,Ideal}ExperimentG_embed`) | `prf*PrG_le_one`; through `_embed` every classical value is attained |
| ITSR | `GameItsr` | `ITSRAdversaryG`, `ITSRAdvantageG` | `ITSRAdvantageG_ofClassical` | `itsr_trivial_advG_zero`, `itsrReplayer_advG_one` |
| SM-TCR | `GameTcr` | `SM_DT_TCR_AdversaryG`, `SM_DT_TCR_AdvantageG` | `SM_DT_TCR_AdvantageG_ofClassical` | `thashArityT_trivial_advG_zero`, `thashArityColliderT_advG_one`, `wotsTcrT_trivial_advG_zero`, `wotsTcrColliderT_advG_one` (`GameWots`) |
| SM-UD, SM-PRE | `GameWots` | `SM_DT_UD_AdversaryG`, `…RealSuccessG`, `…IdealSuccessG`, `…AdvantageG`; `SM_DT_PRE_AdversaryG`, `…AdvantageG` | `SM_DT_UD_{RealSuccess,IdealSuccess,Advantage}G_ofClassical`, `SM_DT_PRE_AdvantageG_ofClassical` | `ud_const_advG_zero`, `udTester_advG`, `toy_udG`; `pre_trivial_advG_zero`, `preInverter_advG_one`, `toy_preG` |
| SM-DSPR-FV, SM-TCR-FV | `GameFV` | `DsprFVAdversaryG`, `dsprSuccessG`, `dsprSPProbabilityG`, `dsprAdvantageG = Success − SPProbability`; `TcrFVAdversaryG`, `tcrFVAdvantageG` | `dspr{Success,SPProbability,Advantage}G_ofClassical`, `tcrFVAdvantageG_ofClassical` | `forsDspr_trivial_advG_zero`, `forsDsprGuesser_advG_one`, `forsTcr_trivial_advG_zero`, `forsTcrCollider_advG_one` |
Non-vacuity lemmas are the existing classical ones transported through `ofClassical`. "At `unifSpec`": coincidence is proved for all classical adversaries and EVERY `ds` (stronger than the instance `ds := noDs`, the empty spec, where every adversary is classical).

## 5. Adversaries (around a forger family `F`; `ds`-queries of the forger are forwarded, everything else is the classical code)
`bPrfCG`, `bPrfWCG w` (`AdvPrf`), `bPrfMsgLG`, `bPrfMsgWLG w`, `bItsrLG` (`AdvLazy`), `toDsprG`, `toTcrG` (`AdvOpenPre`; = `toDspr/toTcr (bOpenPreS ·)`), `bTcrArMG n` (`AdvTcr`), `rUdG`, `rPreG`, `rTcrTG` (`AdvWots`; = `rUd/rPre/rTcrT (bWotsS ·)`); wrappers `toInternal(S)G`, `bytesToTyped(S)G`, `pureBytesToTyped(S)G` (`Wrappers`; `external_advantage_leG` etc. by the same derandomisation). Each has `…_embed` (naturality) and `isLin_…` (for arbitrary forger-to-forger wrapper data). First phases of the two-phase adversaries are the classical first phases (`embed ds`), which do not depend on the forger (named via `dummyForger`).
Definition-level check: `scratch/Gen/GenCheck.lean` (output `scratch/Gen/GenCheck.out`; checker of `scratch/Final/FinalCheck.lean`): 76 constants — the eleven adversaries, their parts, the toolkit (`liftR`, `embed`, `gImpl*`, `runG`, `runGO`, `wrapS`, `wrapFam`, `comp*`, `signH`, `liftAlg`), wrappers, `ofClassical` embeddings, the wrapper experiments, the open programs of the resource statements — reach none of `Classical.choice`, `Classical.indefiniteDescription`, `Exists.choose`, `Classical.propDecidable`, `Fintype.equivFin`, `sampleTable`, `uniformTable`, `UniformSampler.sample`, `Fin.mOfFn`, `Fintype.mPi`; controls flagged as expected (`prG`, `betaSufG`, `linRealSufG`, `SM_DT_TCR_AdvantageG`, `eufAdvG`: measures).

## 6. Recovery of the existing theorems (`Reduction/Gen/Recover.lean`)
`betaEufG_embed`, `betaSufG_embed`, `lin{Ideal,Real}{Euf,Suf}G_embed`: on embedded classical forgers the general right sides ARE the existing ones; `eufAdvG_embedAdv`, `sufAdvG_embedAdvS`: the general advantage IS VCVio's. Hence `slhdsa_*_recovered` (any `ds`) and, at `ds := noDs`, sixteen theorems whose types are literally those of the existing ones (`type_of% @Reduction.<name>`): `slhdsa_{bytes,pure_bytes}_{suf,euf}_cma_final_viaG`, `slhdsa_{,pure_}{suf,euf}_cma_final_memo_viaG`, `slhdsa_{bytes,pure_bytes}_{suf,euf}_cma_linear_viaG`, `slhdsa_{,pure_}{suf,euf}_cma_final_linear_viaG`. Since the general theorems are DERIVED from the existing ones, this is a drift check of the statements, not an independent proof.

## 7. Resources (`Reduction/Gen/Resources.lean`, `ResourcesB.lean`)
`final_resourcesG hS F qs hF : FinalResourcesG ds optRand pkSeedDist F qs (directCounts vp qs) (keygenHashes + qs·signHashes + (1 + verifyHashes·2))` for `hF : ∀ pk, IsQueryBoundP (F pk) (fun i => i.isRight = true) qs` (signing queries; the forger's own `ds`/uniform draws are not counted); `…_external`, `…_bytes`, `…_pureBytes`, `final_resourcesG_128s` (numerals as in FINAL3 §6). Content: (1) pre-seed phases are the classical programs (`Phase1Eq`), so target counts/caps, collection counts and phase-1 samples are those of the classical bundle (`FinalResourcesFinal dummyForger …`); (2) post-seed programs equal interpretations of general open programs (`memoForgeOpenG`, `findOpenFullG`, `wotsPhase2OG`) whose hash queries obey the classical numerals; (3) PRF / game-query, lazy-draw and hash bounds of the single-phase adversaries; (4) signing-query bounds of the wrappers. Method: a black-box transfer (`runGO_bind_queryBound`), no classical counting proof repeated. "Fresh samples" = uniform samples drawn by the reduction's own classical code. Not formal, exactly as before: post-seed sample counts of the two-phase adversaries and the "argued" rows of FINAL3 §6.

## 8. Interface for quantum/ (details and what quantum still needs: `status/GEN-interface.md`)
Type-checked against quantum's oleans in `scratch/Gen/QuantumCompose.lean` (`LEAN_PATH="$(lake env printenv LEAN_PATH):$PWD/../quantum/.lake/build/lib/lean" lean scratch/Gen/QuantumCompose.lean`; quantum/ neither built nor edited):
```lean
theorem slhdsa_euf_cma_quantum_viaG (hS : Structural vp prims) (Q : QForger W (internalAlg vp prims optRand pkSeedDist)) :
    qUnforgeableAdvantage Q ≤ betaEufG distSpec optRand pkSeedDist Q.toStrategy.main :=
  qUnforgeableAdvantage_le_of_forall_strategy Q
    (fun A ↦ betaEufG distSpec optRand pkSeedDist A.main) (fun A ↦ slhdsa_euf_cmaG distSpec hS A)
```

## 9. Not done
1. `ds` with infinite answer types (§1). 2. The general right sides are wrapper-game quantities over `ds + unifSpec`, not quantum-machine advantages (quantum would need `toStrategy` analogues of its `Wrap`/`Games`; its limit route already has quantum right sides), and quantum has no SUF analogue of `…_le_of_forall_strategy`. 3. No general-spec versions of the older headlines (`_split`, `_tight`, phase 1) or of the uniform-seed corollaries (`_deterministic`, `_hedged`: instantiate `optRand`, `pkSeedDist` in the general theorems). 4. The general theorems inherit every limitation of FINAL3 §7.

## 10. Build and axioms
`cd security && export PATH=$HOME/.elan/bin:$PATH && lake build Link E2E Reduction` — "Build completed successfully (7750 jobs)", 40.6 s wall for the 25 new modules (rest cached; the other team's build products untouched). `#print axioms` (all new files end with them; 100+ lines, all identical):
```
'E2E.rust_securityG' / 'E2E.rust_security_linearG' / 'E2E.rust_pure_securityG' / 'E2E.rust_pure_security_linearG' / 'E2E.rust_security_resourcesG'
'Reduction.Gen.slhdsa_{euf,suf}_cma(_linear)G', 'slhdsa_sha2_128s_{bytes,pure_bytes}_suf_cma(_linear)G', 'lin_transfer_{euf,suf}G', 'IsLin.derand', 'derandG',
'slhdsa_*_viaG' (16), 'final_resourcesG(_128s)', 'slhdsa_{euf,suf}_cma_resolved', 'Reduction.Gen.slhdsa_euf_cma_quantum_viaG' (scratch)
    depend on axioms: [propext, Classical.choice, Quot.sound]
```
(the syntactic fusion lemmas `runG_embed`, `runG_wrapS`, `runG_runGO`, `wrapS_embed`: `[propext, Quot.sound]`).
