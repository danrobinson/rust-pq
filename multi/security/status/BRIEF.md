# multi/security — common brief for all work packages

Goal: extend the machine-checked security results for SLH-DSA from SHA2-128s (project
`/Users/danrobinson/Projects/formal-sig/security/`, read its `README.md`, `status/FINAL3.md`) to
all six SHA-2 parameter sets, in the Lake project `/Users/danrobinson/Projects/formal-sig/multi/security/`
(Lean 4.36.0; `export PATH=$HOME/.elan/bin:$PATH`).

## Hard rules
- Do NOT modify anything outside `multi/security/` (in particular not `multi/lean`, `multi/rust`,
  `/lean`, `/rust`, `.tools`, `security/`). If something in `multi/lean` looks wrong, report it.
- No `sorry`, `axiom`, `native_decide`, `bv_decide` in finished work. Temporary `sorry` is allowed
  ONLY while publishing an interface early (see below) and must be gone when you report.
  If something cannot be finished: make it a named hypothesis of a clearly labelled conditional
  theorem, or list it as not done in your report. Never weaken a statement silently.
- `#print axioms` of headline theorems must be ⊆ `propext, Classical.choice, Quot.sound`
  (put `#print axioms` lines at the end of each file, as security/ does).
- Only edit the files of your own package. If you need a lemma in someone else's file, put it in
  your own file (or a new file of yours) and say so in your report.
- Write a short report file `multi/security/status/<PACKAGE>.md` (what is proved, exact statements
  of main theorems, anything not done, anything surprising) and return a summary < 300 words.

## Layout (`multi/security/lakefile.toml`)
- `Spec`, `Slhdsa`: compiled in place from `multi/lean` (parameterised spec `Spec.Params`,
  instances `Spec.sha2_128s` …; Rust extraction + refinement theorems `slhdsa.<S>.*_correct`).
- `Reduction`: the generic standard-model reduction, compiled in place and unmodified from
  `security/Reduction/*.lean` (all modules except `Gen/` and `PrfDomainNonVacuity`), namespace
  `Reduction`. It imports `Link.Basic/Hash/Verify/Security`; here those are satisfied by
  `shim/Link/{Basic,Hash,Verify}.lean` (Spec-free subsets: `Link.vp`, `Link.prims`, `Link.S128`,
  `Link.Dom`, `Link.decodeSig`, …) and the unmodified `security/Link/Security.lean`.
  So the namespace `Link` exists but contains only VCVio-level 128s abbreviations — do not use it.
  security's own `Link` (rest), `E2E`, `Spec`, `Slhdsa` are NOT available (name clashes).
- `MLink` (namespace `MLink`): Spec = VCVio, six sets. `MLink/Basic.lean` is the vocabulary:
  `MLink.Sha2Set` (`.s128s … .s256f`), `S.fips`, `S.spec : Spec.Params`, `S.vp`, `S.prims`
  (`= sha2Primitives S.vp.params = approvedPrimitives S.fips`), `S.Node = Bytes S.vp.params.n`,
  numeric facts (`S.n_eq`, `S.len_eq`, …, proved by `cases S <;> decide`/`rfl` — add what you need
  in your own files the same way), `sp`, `cv`, `spA`, `nd {n} : Bytes n → Spec.Bytes`, `nds`, `adr`,
  `Dom`, `BaseDom`, `xmssBytes S`, `htBytes S`, `forsBytes S`, `sigBytes S`, `pkBytes S`.
- `MReduction` (namespace `MReduction`): instances of the Reduction headlines at the six sets.
- `ME2E` (namespace `ME2E`): Rust functions `sets.<S>.slh_*` = scheme cores + security.

## Porting convention (MLink)
security/Link proves everything for 128s with `Node = Bytes 16`, constants `vp`, `prims`,
numerals (16, 35, 9, 12, 14, 7, 30, 21, 7856 …) and the single-set `Spec` (functions without a
parameter argument). The port is ONE proof generic over `(S : Sha2Set)`, not six copies:
same file names (`MLink/X.lean` for `security/Link/X.lean`), same theorem names, statements
obtained by the systematic substitution `vp ↦ S.vp`, `prims ↦ S.prims`, `Node ↦ S.Node`,
`Spec.f args ↦ Spec.f S.spec args`, numerals ↦ parameter expressions (prefer the `Spec` side,
e.g. `S.spec.sigBytes`, `2 * S.spec.n`, or the VCVio side `S.vp.params.len` where the VCVio
term has that type), `S` the first explicit argument (`variable (S : Sha2Set)`).
Where a proof needs a concrete numeric fact, state it as a lemma over `S` and prove it by
`cases S <;> decide` (or `rfl`/`simp`/`omega`); avoid `cases S` on large goals when a small numeric
lemma suffices (compile time), but it is acceptable when it is the pragmatic way.
Differences that are NOT just numerals — check them, do not assume:
- n = 24/32: `H`, `T_l` use SHA-512 (padding 128−n), `PRF_msg` HMAC-SHA-512, `H_msg`
  MGF1-SHA-512; `F`, `PRF` stay SHA-256 (padding 64−n). VCVio's `sha2Thash` dispatches on the
  list length: singleton ⇒ F formula. `MLink.Tl_eq` therefore has `ys.length ≠ 1`.
- 128f has m = 34 (two MGF1-SHA-256 blocks); 256f has a 64-bit tree index (h − h' = 64,
  treeBytes = 8), 256s/256f k·a not a multiple of 8, f-sets have different h', d, a, k.
- VCVio `Params.len2` uses `Nat.log`, `Spec.Params.len2` uses `Nat.log2`; VCVio `m`,
  `treeIdxBytes`, `leafIdxBytes` are derived, Spec's `m` is a field.
- Address-domain side conditions (`Dom`, `BaseDom`, `WotsDom`, `ForsDom`, bounds like `idx < 2^h'`,
  tree index `< 2^64`, layer `< 256`) must be re-derived for every set.

## Interfaces published early
A package whose results others need first writes ALL its public statements with `sorry`
proofs, compiles them (`lake build MLink.X`), and creates the marker file
`multi/security/status/<PACKAGE>-interface.ok`; then it replaces the `sorry`s without changing
the statements (if a statement must change, note it at the top of `status/<PACKAGE>.md`).
Downstream packages wait for the marker (poll with a Monitor/until loop), then build on it.
`MLink/Hash.lean` already contains the interface of the hash layer (F_eq, H_eq, Tl_eq, PRF_eq,
PRFmsg_eq, Hmsg_eq); `MLink/Encoding.lean` and `MLink/Sha256.lean` are already ported.

## Building
`cd multi/security && lake build MLink.X` builds one module and its dependencies (dependencies
of the project — VCVio, Mathlib, Aeneas, Reduction — are prebuilt; first build of `Slhdsa`
takes ~3 min). Several agents build concurrently in this project: build only your own modules
(`lake build MLink.Foo`, never `lake clean`, never delete `.lake`), and if a build fails in a
module that is not yours, wait and retry — it is probably being edited. For quick iteration
`lake env lean MLink/Foo.lean` type-checks a file against existing oleans without writing.
The 36-core machine is shared with other teams: avoid needless full rebuilds.
