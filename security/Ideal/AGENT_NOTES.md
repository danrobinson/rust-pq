# Working notes for agents proving lemmas in security/Ideal (internal; not a status document)

Project: /Users/danrobinson/Projects/formal-sig/security (Lean 4.36, Mathlib v4.36, VCVio at
../.tools/VCVio-upstream, read-only). `export PATH=$HOME/.elan/bin:$PATH` first.

## Rules
- Only create/edit files under security/Ideal/ (and scratch files under security/scratch/ideal/<your-name>/).
  NEVER edit security/Link, security/E2E, security/Reduction, security/lakefile.toml, lean/, rust/,
  quantum/, multi/, .tools/.
- No `sorry`, `axiom`, `native_decide`, `bv_decide` in your final files. (`decide` is fine.)
  If something cannot be proved, turn it into an explicit named hypothesis of the theorem and say so
  in your report; never leave a silent gap.
- Do not change the statements/definitions in files you were not assigned (Ideal/Core/Defs.lean,
  Ideal/Games/TcrDefs.lean, ...). If a statement you were asked to prove is false or needs a changed
  hypothesis, say exactly why in your report and prove the closest true statement (keep the old
  name, document the change in the docstring).
- Check a file with `cd security && lake env lean Ideal/Path/File.lean` (fast, no lock).
  To make a module importable by others run `lake build Ideal.Path.File` (that exact target only).
  NEVER run a bare `lake build` (other agents share the workspace; the lake lock serialises
  builds: if you see a lock/concurrent-write failure, wait 30 s and retry).
- End every file with `#print axioms` lines for its main theorems; they must show only
  `propext`, `Classical.choice`, `Quot.sound`.
- Keep proofs robust (no huge `simp` without `only` on hot paths; set `maxHeartbeats` locally only
  if really needed).

## VCVio pointers (all under ../.tools/VCVio-upstream)
- `OracleComp spec α`, `simulateQ impl oa`, `QueryImpl spec m = (t : spec.Domain) → m (spec.Range t)`,
  spec sums `spec₁ + spec₂` (domain `ι₁ ⊕ ι₂`), `unifSpec` (uniform `Fin (n+1)`), `ProbComp = OracleComp unifSpec`.
  Induction: `OracleComp.inductionOn` (cases `pure`, `query_bind`).
- Probability: `𝒟[mx]` (evalDist, a measure), `𝒟[mx] {true}`, `Pr{ do-block }[ event ]`
  (VCVio/EvalDist/ProbabilityNotation.lean, ProbabilityBounds.lean: `prEvent_mono`, `prEvent_or_le`,
  `prEvent_bind_le_of_forall_le`, `prEvent_bind_bind_eq_lintegral_of_discrete`, swaps `evalDist_bind_bind_swap`…).
- Lazy random oracle: `spec.randomOracle`, `spec.romImpl` (VCVio/OracleComp/QueryTracking/RandomOracle/
  Basic.lean, Simulation.lean); lazy = eager table: `OracleComp.evalDist_simulateQ_romImpl_run'_eq_completeTable`
  (RandomOracle/DependentTable.lean), `evalDist_uniformSample_bind_update_map` (EagerTable.lean).
- Query bounds: VCVio/OracleComp/QueryTracking/QueryBound/{Basic,Simulation}.lean (`IsQueryBoundP`,
  `AllQueriesSatisfy`, `IsQueryBoundP.simulateQ_of_step`).
- Identical-until-bad / invariants / potentials: VCVio/OracleComp/SimSemantics/StateT/{UntilBad,PreservesInv}.lean,
  RandomOracle/FreshAnswer.lean (`IsPotentialStep`, `prEvent_and_le_of_potential`), RandomOracle/HiddenSeed.lean
  (`SecretEncoding`), Unpredictability.lean.
- The existing development security/Reduction/*.lean (24k lines) uses all of this API and is a good
  source of working idioms (e.g. Reduction/Lazy/Core.lean, Reduction/Tables.lean, Reduction/PrfDomain.lean).
