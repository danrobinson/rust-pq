# Common brief, phase 3 (re-audit follow-ups)

Project: /Users/danrobinson/Projects/formal-sig/security (Lean 4.36.0; `export PATH=$HOME/.elan/bin:$PATH`).
State: libraries `Link`, `E2E`, `Reduction` fully proven. Read status/FINAL2.md first (headline
theorems `slhdsa_{suf,euf,pure_suf,pure_euf}_cma_final_split` in Reduction/HeadlineSplit.lean,
games, adversaries, resource table, limitations), then REDUCTION_STATUS.md and the sources you need.
Also status/BRIEF2.md "Known hazards".

Coordination (strict)
- ANOTHER TEAM is concurrently building a library security/Ideal that imports Reduction and runs
  `lake build` in security/. Never touch security/Ideal, ../lean, ../rust, ../quantum, ../multi,
  ../.tools. Do NOT rename, delete or change the meaning/statement of any existing definition or
  theorem. Add NEW files with new names only; edit only the files your task says you own.
- Check your files with `cd /Users/danrobinson/Projects/formal-sig/security && lake env lean <File>.lean`.
  Do not run a bare `lake build`. If one of your files must be imported by another of yours,
  write its olean: `lake env lean -o .lake/build/lib/lean/<Lib>/<Path>.olean <Lib>/<Path>.lean`.
  If any lake command reports a lock or concurrent write, wait and retry.
- No `sorry`, `axiom`, `native_decide`, `bv_decide`. Anything you cannot finish: a clearly labelled
  conditional theorem with a named hypothesis, and say so. Adversary definitions: explicit, no
  choice principles, no eager/exponential tables. Non-vacuity lemma for any NEW game/problem.
- End each file with `#print axioms` for its main theorems (must be ⊆ propext, Classical.choice,
  Quot.sound). Write security/status/<PACKAGE>.md (exact statements, lemma names, anything not
  done and why, integration notes). Report to the lead in under 250 words; the lead has almost
  no context left, so everything important must be in the status file.
