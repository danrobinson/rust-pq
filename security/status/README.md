# security/status

Working reports, kept as written:

- The files directly in this directory are the reports of the single-set development
  (SLH-DSA-SHA2-128s; `Link`, `E2E`, `Reduction`, `Ideal`). Where they name files of `security/Link`
  other than `Basic`, `Hash`, `Verify`, `Sha256`, `Security`, of `security/E2E` other than
  `GuardedRom` and `CodedRom`, `security/Ideal/Rust*.lean`, `../lean`, `../lean-hw`, `../rust`,
  `../compat` or `../opt`, they mean the single-set tree, which is git commit `26aa3d8` (removed from
  the working tree on 2026-11-22). Of `Link/{Basic,Hash,Verify,Sha256}.lean` only the Spec-free parts
  remain (`../STATUS.md`, "The stand-ins").
- `sets/` holds the reports of the six-set work packages (`MLink`: `B.md`, `C.md`; `MReduction`:
  `D.md`; `ME2E`: `E.md`; the common brief `BRIEF.md`; the `*.ok` interface markers). They were
  written when the six-set tree lived in a subdirectory `multi`; its paths have been rewritten to
  the current ones (`security/`, `lean/`, `rust/`). Their `security/Link/*`, `security/E2E/*` are
  the single-set files of git commit `26aa3d8`.
- `axioms.txt`: the `#print axioms` output of the 257 headline theorems, written by
  `../scripts/check.sh`.
