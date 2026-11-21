# Common brief, work package OPEN (hash evaluations of the reduction adversaries as oracle queries)

Project: /Users/danrobinson/Projects/formal-sig/security (Lean 4.36.0; `export PATH=$HOME/.elan/bin:$PATH`).
Libraries `Link`, `E2E`, `Reduction` are fully proven and green. Read, in this order and only as far as
you need: status/BRIEF3.md (rules, hazards), ../quantum/STATUS.md §0 "REQUESTS TO THE REDUCTION LEAD"
(lines 48–101: THE SPECIFICATION, items R1–R7; read-only), status/FINAL3.md §6–7 (adversaries, what is
formal / argued), status/W3.md, status/W5.md (open-program model and counts), then the sources.

Model already present: `Reduction/Lazy/Core.lean` (`RSpec`, `Kind`, `kind`, `tblImpl`, `lazyRun`,
`lazyRes`, `interp`), `Reduction/Lazy/Open.lean` (`OSpec prims gspec`, `openQ`, `secQ`, `gameQ`,
`openKeygen`, `openSign`, `qb_*` counting lemmas, `keygenHashes`, `signHashes`), open second phases
`findOpenFull` (Resources2Fors), `memoForgeOpen` (TcrMemo; `verifyHashes`), `wotsForgeOpen`
(Resources2Wots), `Lazy.msgOpen(W)`, `Lazy.itsrOpen`. Counting predicate: `IsQueryBoundP`.

Shared new file (already compiled, olean written; import it if useful, do NOT edit it):
`Reduction/Open/WithHash.lean` — `Open.withTH prims T H` (= `prims` with `Thash`, `Hmsg` replaced;
`(withTH prims T H).core = prims.core` by `rfl`, so all types built from `prims.core` are unchanged),
`Open.castForger T H A : Forger vp (withTH prims T H) optRand pkSeedDist` (same `main`),
`Open.HashFns prims`, `Open.withHash prims f` (all four components replaced; NOTE: `PublicKeyCore`,
`SignatureCore`, … take `prims.core`, which contains `PRF`/`PRFmsg`, so with `withHash` these types are
NOT definitionally equal and need transports; `publicHashSpec (withHash prims f).core =
publicHashSpec prims.core` holds by tactic `rfl`).

Rules (strict)
- NEW files only, under `Reduction/Open/`, with the file names your task gives you; new names inside
  `namespace Reduction` (sub-namespace `Open` recommended). Do NOT edit, rename, delete or restate any
  existing definition/theorem or any existing file (other libraries import them). Do not touch
  security/Ideal, ../quantum, ../lean, ../rust, ../multi, ../.tools, Reduction/Gen, Reduction.lean.
- Other agents work in parallel on sibling files in `Reduction/Open/`; do not import their files
  (only `WithHash.lean` and files your task names) and do not edit them.
- Check with `cd /Users/danrobinson/Projects/formal-sig/security && lake env lean Reduction/Open/<F>.lean`.
  NEVER run `lake build`. To import one of your own files from another of yours, write its olean:
  `lake env lean -o .lake/build/lib/lean/Reduction/Open/<F>.olean Reduction/Open/<F>.lean`.
  On a lock / concurrent-write message wait and retry. Never delete build products.
- No `sorry`, `axiom`, `native_decide`, `bv_decide`. If something cannot be finished: a clearly
  labelled conditional theorem with a NAMED hypothesis, or leave it out; say so in the status file.
  New adversary definitions: explicit programs, no choice principles, no eager/exponential tables.
- If a statement of R1–R7 is not provable as worded, prove the nearest true statement and state
  exactly how it differs. Prefer honest, checkable statements over wording fidelity.
- End each file with `#print axioms` for its main theorems (must be ⊆ propext, Classical.choice,
  Quot.sound). When done, every one of your files must compile with no error and its olean must be
  written (command above), because a later bundle file will import it.
- Write `security/status/OPEN-<PKG>.md` (≤ 80 lines): exact names and statements (verbatim
  signatures of the main definitions/theorems), deviations from the spec with reasons, 128s numerals,
  what is not done and the obstacle, axioms output. Final report to the lead: under 200 words; the
  status file must contain everything needed (the lead has little context).
- Work efficiently: reuse existing lemmas (`*_tbl`, `*_kindBound`, `qb_*`) instead of re-proving;
  keep heartbeats reasonable. Proof-engineering hazards: status/BRIEF2.md "Known hazards".
