# Common brief, phase 2 (strengthening the standard-model reduction)

Project: /Users/danrobinson/Projects/formal-sig/security (Lean 4.36.0; `export PATH=$HOME/.elan/bin:$PATH`).
Current state (all proven, must keep building): libraries `Link`, `E2E`, `Reduction`. Read
status/FINAL.md (120 lines: headline theorem, games, adversaries, limitations), then
REDUCTION_STATUS.md, status/AUDIT2.md, and the per-package notes status/P0..P9.md as needed.
VCVio sources (read-only): ../.tools/VCVio-upstream. EasyCrypt blueprint (read-only):
../.tools/formosa-slhdsa/proofs (final lemma `EUFCMA_SPHINCS_PLUS` in SPHINCS_PLUS.ec).

Rules
- Add NEW files; do not edit existing files of Reduction/, Link/, E2E/ (other agents work
  concurrently and the existing theorems must keep building). Edit only the files your task
  says you own. Nothing under ../lean or ../.tools may be modified.
- Check with `cd /Users/danrobinson/Projects/formal-sig/security && lake env lean <File>.lean`.
  NEVER run `lake build`, `lake update`, `lake exe cache` (concurrent agents). Imports of
  existing modules resolve to prebuilt .olean files. If one of YOUR files must be imported by
  another of YOUR files, write its olean yourself:
  `lake env lean -o .lake/build/lib/lean/Reduction/<File>.olean Reduction/<File>.lean`.
  If a VCVio module you need has no .olean you may build exactly that module by name.
- No `sorry`, `axiom`, `native_decide`, `bv_decide` in what you hand back. Anything you cannot
  finish must be an explicit, named, precisely stated hypothesis (`def … : Prop`) of a
  conditional theorem — never a placeholder and never a silent weakening. Say so in the report.
- Games must be genuine probabilities over explicit experiments; adversaries explicit programs.
  No adversary definition may use a choice principle, enumerate/sample a type of exponential
  size, or search for preimages. Add a non-vacuity lemma for any NEW game you introduce.
- Known hazards: (1) carrier types like `prims.Y` are definitionally but not reducibly equal to
  concrete vectors — prefer term-mode steps, `erw`, or lemmas over abstract types; (2) tactics
  that put `x ∈ support (sampleTable …)` into the context can loop forever — prove such steps
  over an abstract sampler and instantiate.
- You may spawn your own subagents for independent sub-lemmas (scratch under
  security/scratch/<package>/, delete when done).
- At the end write security/status/<PACKAGE>.md (exact statements proven, any named hypotheses
  left and why, notes for integration) and report to the lead in under 250 words; the lead has
  very little context, so details go in the status file. Do not edit REDUCTION_STATUS.md.
