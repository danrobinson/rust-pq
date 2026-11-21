# Common brief — package GEN (forgers over a general sampling spec)

Project `/Users/danrobinson/Projects/formal-sig/security` (Lean 4.36.0; `export PATH=$HOME/.elan/bin:$PATH`).
Goal of GEN: the proven reduction (`Reduction/`, forgers over `unifSpec`) for forgers over
`gSpec ds = ds + unifSpec`, `ds` any oracle spec with `[OracleSpec.AnswerMeasure ds] [∀ d, Fintype (ds.Range d)]`.

## Route (decided; do not change)
Derandomisation of the `ds`-coins through the LINEAR headline. Every term of the linear inequality,
as a function of the forger's program family `F`, is `IsLin` ("classical prefix; ONE run of the forger
against a classical stateful handler; classical suffix"), and an inequality between `IsLin`
functionals that holds for all `ds`-free families holds for all families (`derandG`). So nothing of
the 30k-line proof is re-proved. What each package supplies, per reduction adversary `B` and game:
1. a WRAPPER GAME (adversary type over `ds + unifSpec`, experiment, value), with
   coincidence on classical adversaries and non-vacuity;
2. the reduction adversary around a general-spec forger family, `BG ds … F`;
3. NATURALITY: `BG ds … (fun pk => embed ds (A.main pk)) = <classical adversary embedded> (B A)`;
4. LINEARITY: `IsLin ds (wOf ds) 1 (fun F' => <wrapper-game value> (BG ds … (wrapFam ds w e g F')))`
   for arbitrary forger-to-forger wrapper data `w e g` (this makes the byte-level/external
   headlines free).

## Toolkit (read these files first; they are short and compiled)
- `Reduction/Gen/Defs.lean`: `gSpec`, `liftR ds : ProbComp α → OracleComp (gSpec ds) α`,
  `embed ds : OracleComp (unifSpec + X) α → OracleComp ((ds + unifSpec) + X) α`; simp lemmas.
- `Reduction/Gen/Run.lean`: `runG ds impl oa s` (closed run against a classical handler
  `impl : QueryImpl (unifSpec + X) (StateT σ ProbComp)`), `runGO` (open: handler into
  `OracleComp (unifSpec + G)`, result in `OracleComp ((ds + unifSpec) + G)`), `wrapS`, `wrapFam`;
  `runG_embed`, `runGO_embed`, `runG_bind`, `runG_pure`, `runG_map`; FUSION: `runG_runGO`
  (closed run of an open run = closed run with pair state, handler `compST`), `runG_wrapFam`,
  `runGO_wrapFam` (handler `compS`), `runGO_runGO`, `runG_embedO`.
- `Reduction/Gen/Sem.lean`: `prG ds g = 𝒟[g] {true}`, `prG_liftR : prG ds (liftR ds g) = prTrue g`,
  `isLin_run`, `isLin_run_pure`, `isLin_liftR_bind`, `derandG`, `wOf`.
- `Reduction/Gen/Derand.lean`: `IsLin` and its closure (`IsLin.add`, `.const_mul`, `.mono`).
- `Reduction/Gen/Sig.lean`: `liftAlg`, `eufAdvG`, `sufAdvG`, `sigExpG`, `signH`, coincidence, linearity.
- `Reduction/Gen/Forger.lean`: `GFam ds vp prims` (forger family, typed internal interface),
  `GForger`, `dummyForger`, `g2RunWithG`, `g2RunG`, `g2RunG_embed`.
- WORKED EXAMPLE to imitate exactly: `Reduction/Gen/GameTcr.lean` (wrapper game) and
  `Reduction/Gen/AdvTcr.lean` (adversary `bTcrArMG`, `bTcrArMG_embed`, `isLin_bTcrArMG`);
  `Reduction/Gen/GamePrf.lean` (single-phase open game; `stOf` for stateless handlers).

## Conventions
- Namespace `Reduction.Gen`. `ds` is the first explicit argument everywhere. Names: classical name + `G`
  (`bPrfCG`, `rUdG`, `SM_DT_UD_AdversaryG`, `SM_DT_UD_RealSuccessG`, …); coincidence lemmas
  `…_ofClassical` / `…_embed`; linearity `isLin_<adv>` (one lemma per probability, e.g.
  `isLin_rUdG_real`, `isLin_rUdG_ideal`); naturality `<adv>G_embed`.
- Reduction adversaries take the forger FAMILY `F : GFam ds vp prims` (plus `optRand`, `pkSeedDist`
  explicitly where the classical definition gets them from the forger's type).
- Wrapper-game adversary types: every phase over the general interface (phases that had spec
  `unifSpec + S` get `(ds + unifSpec) + S`; `ProbComp` phases get `OracleComp (gSpec ds)`).
  Experiments: VCVio's experiment with classical parts under `liftR ds`, oracle phases under
  `runG ds <VCVio's oracle handler>`. Values are `prG ds (experiment)`. Advantages that VCVio
  defines as `|real − ideal|` (`boolDist`) are defined as `ENNReal.absDiff real ideal` (cf.
  `Reduction/Linear.lean`, `*_eq_absDiff`, all `rfl`).
- Phases of a reduction adversary that do not run the forger are the CLASSICAL phases, embedded
  (`embed ds …` / `liftR ds …`). If the classical definition mentions the forger only formally
  (structure projection of a definition taking `A`), use `dummyForger` and give the phase its own
  `def` with the state type written out (see `chooseArM` in `AdvTcr.lean`; without this, `rw`/`simp`
  fail with "not type-correct under implicit transparency").
- The forger is run ONLY through `runG`/`runGO`/`wrapFam` (or `g2RunG`), with the SAME classical
  handler as in the classical definition, so that naturality is `runG_embed`/`runGO_embed` + `rfl`.

## Proof patterns
- Naturality: `unfold`; `congr`/`funext`; `simp only [<defs>, runG_embed / runGO_embed / g2RunG_embed, liftR_bind, liftR_pure, embed_bind, embed_pure]`; often closes by `rfl` after that.
- Coincidence of a wrapper game: first restate VCVio's experiment as nested `>>=` without pattern-matching
  `let`s (`…_Experiment_eq`, by `bind_congr` + case split), then `simp only [runG_embed, liftR_bind, liftR_pure]`, then `prG_liftR`.
- Linearity: `unfold <value> <experiment> <BG>`; `dsimp only`; rewrite to the shape
  `liftR ds p >>= fun y => …` with `simp only [runG_embed, runG_wrapFam, runG_runGO, runGO_wrapFam, runG_bind, runG_map, bind_assoc, bind_map_left, map_bind, pure_bind, liftR_bind…]`;
  peel prefixes with `refine isLin_liftR_bind ds _ _ fun y => ?_`; close with `isLin_run ds _ _ _ _`
  (suffix `fun r => liftR ds (post r)`) or `isLin_run_pure` (suffix `fun r => pure (f r)`).
  If the goal has `f <$> runG …` use `map_eq_bind_pure_comp`. If a suffix is `liftR … >>= pure …`,
  fuse it (`← liftR_pure`, `← liftR_bind`) so it reads `liftR ds (post r)`.
- For an OPEN adversary `B : OracleComp ((ds+unifSpec) + G) β` inside a game that runs it by
  `runG ds H B s₀`: write `BG` as `embed ds pre >>= fun x => runGO ds impl (F pk) s >>= fun r => embed ds (post r)`
  and use `runG_bind`, `runG_embedO`, `runG_runGO`.

## Rules (strict)
- Create ONLY the new files your task names (under `Reduction/Gen/`), plus scratch under `scratch/Gen/`.
  Do not rename/delete/change any existing definition or theorem; do not edit existing files
  (including other `Gen` files — if a toolkit lemma is missing, prove it locally in your file and
  report it). Never touch `security/Ideal`, `../quantum`, `../lean`, `../rust`, `../multi`, `../.tools`.
- ANOTHER TEAM builds in `security/` concurrently: never run `lake build`. Check with
  `cd /Users/danrobinson/Projects/formal-sig/security && lake env lean Reduction/Gen/<File>.lean`; write
  oleans by hand when a file is done or needed by another of yours:
  `lake env lean -o .lake/build/lib/lean/Reduction/Gen/<File>.olean Reduction/Gen/<File>.lean`.
  On a lock error wait and retry.
- No `sorry`, `axiom`, `native_decide`, `bv_decide`. Anything unfinished: a clearly labelled
  conditional theorem with a named hypothesis, reported as such. No choice principles / eager
  tables in adversary DEFINITIONS (proofs may be classical). End each file with `#print axioms`
  for its main theorems (⊆ propext, Classical.choice, Quot.sound).
- Hazards: carrier types (`prims.Y`) are definitionally but not reducibly vectors — prefer term-mode
  steps / `erw`; `whnf` timeouts across tight/loose problems — put
  `attribute [local irreducible] arityTargets tcrTargets` at the top; goals mentioning
  `x ∈ support (sampleTable …)` can loop; dependent `State` fields — see `chooseArM`.
- Report to the lead in under 250 words: file names, exact names/signatures of the wrapper games,
  adversaries, naturality, linearity and coincidence lemmas, non-vacuity lemmas, anything not done
  and the precise obstacle, `#print axioms` output.
