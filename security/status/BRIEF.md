# Common brief for Reduction proof packages

Project: /Users/danrobinson/Projects/formal-sig/security (Lean 4.36.0; `export PATH=$HOME/.elan/bin:$PATH`).
Read first: REDUCTION_STATUS.md (architecture, final statement, lemma table, work packages, the
VCVio lemmas to start from), then Reduction/Basic.lean, Games.lean, WotsGame.lean, Steps.lean,
Harness.lean, and your own file(s). VCVio sources: /Users/danrobinson/Projects/formal-sig/.tools/VCVio-upstream
(read-only). EasyCrypt blueprint: /Users/danrobinson/Projects/formal-sig/.tools/formosa-slhdsa/proofs (read-only).

Rules
- Edit ONLY the file(s) your package owns (listed in your task). You may add helper lemmas there
  and revise the reduction adversary defined there. Definitions in Basic/Games/WotsGame/Steps/
  Harness/Main/Final and every `Step…` statement are FROZEN: other packages depend on them.
- Check with `cd /Users/danrobinson/Projects/formal-sig/security && lake env lean Reduction/<File>.lean`.
  NEVER run `lake build`, `lake update`, `lake exe cache`: other agents work concurrently and
  imports resolve to prebuilt skeleton .olean files. Consequence: lemmas of OTHER packages are
  available to you only as their skeleton statements (use them as given facts if needed); new
  helpers you need must live in your own file. If a VCVio module you want to import has no
  .olean, you may build exactly that module by name (`lake build Some.VCVio.Module`).
- No `axiom`, `native_decide`, `bv_decide`. Do not modify anything under ../lean, ../.tools,
  Link/ or E2E/.
- Known friction: carrier types like `prims.Y` are definitionally but not reducibly equal to
  concrete vectors; `rw`/`simp` may fail with "not type-correct under implicit transparency".
  Prefer term-mode steps (`exact`, `refine … .trans ?_`, `congrArg`), `erw`, or helper lemmas
  over abstract types.
- If a frozen statement (a `Step…`, a game, or a lemma statement in your file) is FALSE, vacuous,
  or unprovable as stated, do not paper over it: find the minimal correct statement, apply the
  change only inside your own file where possible, and report the exact issue and proposed fix
  (file, name, old → new) so the lead can change frozen files.
- Goal: no `sorry` left in your file. If you cannot finish something, reduce it to the smallest
  precisely stated helper lemma(s) left as `sorry`, each with a doc comment explaining what is
  missing; everything else must be proved from them.
- At the end: the file must compile; append `#print axioms` for the package's main lemmas; write
  /Users/danrobinson/Projects/formal-sig/security/status/<PACKAGE>.md (proven / open with exact
  statements / statement-change requests / notes for dependants). Do not edit REDUCTION_STATUS.md.
- Final report to the lead: under 200 words — proven, open (names + one-line obstacle), requested
  changes to frozen statements, axioms output. The lead has little context; details go in the
  status file.

## Notes from finished packages (read!)
- HAZARD: tactics that bring `tbl ∈ support (sampleTable vp prims)` into the context (e.g.
  `rcases`/`cases` after `simp [mem_support_bind_iff]`, or `isQueryBoundP_bind` at `sampleTable`)
  make Lean loop at 100% CPU with no heartbeat error. Workaround: prove the step over an abstract
  `my : ProbComp β` and instantiate with `exact`, giving function arguments explicitly (see
  `support_joint_aux`, `run_aux`, `bound_aux` in Reduction/ITSR.lean).
- Reduction/Tables.lean (P0, proven; see status/P0.md for which lemma each consumer should use):
  lazy = eager table, table-coordinate resampling/extraction, `prTrue` calculus.
- Reusable proven helpers: Reduction/ITSR.lean (`prTrue_bind_pure`, `g2Joint`, `g2_eq_joint`),
  Reduction/WotsFinal.lean namespace `Reduction.WotsFinal` (`nested_run`, `ofFnM_run_sample`,
  `ofFnM_run_det`, `sim_step`, `stepKey_inj`, generic over any `simChoose` instance),
  Reduction/PRFMsgHop.lean (private `idealRun_eq`, `lazyRandomizer_step`: copy if needed).
  See status/P2.md, P3.md, P5.md, P8.md.
- Refused oracle answers are read as `default`, so each reduction needs its no-refusal /
  query-legality fact proven where the step uses it.
