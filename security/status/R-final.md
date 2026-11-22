# R-final — the composed ideal-model headline with no realiser hypotheses (agent `prfmsg`)

State: **done.** All twelve realisers are discharged. New files (only):
- `Ideal/Realize/FinalCore.lean`: caps `QcAll`, `NAll`, `ellB`; `RealizersLe_mono`; the bundle
  with the three WOTS realisers as parameters (`sufRealizersW`, `eufRealizersW`, `…_le`) and the
  `_W` versions of the bounds.
- `Ideal/Realize/Final.lean`: WOTS realisers plugged in; **the headlines**.
- `Ideal/RustFinalClosed.lean`: the Rust-level corollary.
Builds: `lake build Ideal.Realize.Final` → `Build completed successfully (7322 jobs).`;
`lake build Ideal.RustFinalClosed` → `Build completed successfully (7973 jobs).` Every
`#print axioms` line is `[propext, Classical.choice, Quot.sound]`. No `sorry`, `axiom`,
`native_decide`, `bv_decide`, `maxHeartbeats` in these files. (Corrected 2026-11-22: this said the
files were not imported by `Ideal.lean`; they are: `Ideal.Realize.FinalCore`, `Ideal.Realize.Final`,
and `Ideal.RustFinalClosed` until the single-set Rust corollaries `Ideal/Rust*.lean` were removed on
2026-11-22, see `../STATUS.md`; the file is at git commit `26aa3d8`.)

## Parameters
- `S : ForgerI`: ideal-model forger (one oracle program: uniform bits, SHA-256 compression
  queries, signing queries).
- `oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)`: table-independent `opt_rand` sampler (as a
  function of `PK.seed`, `PK.root`), `optRandU oR` the family. Public seed uniform.
- `qf`: the forger's compression queries; `qs`: its signing queries; `ℓ`: byte cap on signed and
  forged messages.
- `QcAll qf qs ℓ = qf + (qs+1)·(2^25 + 2·⌊(ℓ+56)/64⌋)` (`FinalCore.lean:33`): caps the compression
  queries of all eleven non-ITSR realisers. It follows from the agents' own `_le` lemmas:
  `qPrf_le'`, `qMsg_le'`, `q₂T_le`, `q2Fors_eq`, `QcW`.
- `NAll qs = max 2^81 (Prf.qOPrf qs)` (`:37`), with `qOPrf qs = 17920 + 182784·qs`. It caps the
  challenge, collection and PRF-oracle queries. It is above the fixed reduction targets
  `openPreTargets ≈ 2^78.8`, `tcrTargets < 2^80` and `NW ≈ 2^79.81`.
- `ellB ℓ = ⌊(ℓ+63)/64⌋` (`:40`): message length in 64-byte blocks.
- ITSR leg `epsItsrF qf (2*qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ`, with
  `itsrQc qs = 269824 + qs·2007386` and `itsrLc ℓ = max 11 ((ℓ+56)/64+1)`. Here `qP = q = qf`,
  so the forger's own `cB`-shaped queries are bounded by `qf`, honestly.

## Headlines (verbatim; `Ideal/Realize/Final.lean`)
Common hypotheses (only these):
```
(S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) {qf qs ℓ : ℕ}
(hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ (S := List Byte) i = true) qf)
(hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ (S := List Byte) i = true) qs)
(hlong : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isLongQ (S := List Byte) ℓ i = true) 0)
(hout : ∀ pk, ∀ z ∈ support (S.main pk), z.1.length ≤ ℓ)
```
`:74` `theorem suf_ideal_closed … (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :`
```
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((66 * QcAll qf qs ℓ + 40 : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256
```
`:91` `euf_ideal_closed`: the same with `eufI`.

Numeric points (SUF and EUF each: `suf_…`/`euf_…`):
| theorem (line) | forger caps | bound |
|---|---|---|
| `suf_ideal_closed_2_20` (`:108`), `euf_` (`:123`) | `qf + 2^46 ≤ 2^60`, `qs ≤ 2^20`, `ℓ ≤ 2^26` | `2^-70 + 2^-128 + 2^-61` |
| `suf_ideal_closed_2_40` (`:138`), `euf_` (`:153`) | `qf ≤ 2^64`, `qs ≤ 2^40`, `ℓ ≤ 2^26` | `2^-50 + 2^-88 + 2^-41` |
| `suf_ideal_closed_2_64` (`:168`), `euf_` (`:183`) | `qf ≤ 2^64`, `qs ≤ 2^64`, `ℓ ≤ 2^26` | `2^-44 + 2^-43 + 2^-31` |
For example:
```
theorem suf_ideal_closed_2_20 … (hf : qf + 2 ^ 46 ≤ 2 ^ 60) (hs : qs ≤ 2 ^ 20) (hℓ : ℓ ≤ 2 ^ 26) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      ((2 : ℝ≥0∞) ^ 70)⁻¹ + ((2 : ℝ≥0∞) ^ 128)⁻¹ + ((2 : ℝ≥0∞) ^ 61)⁻¹
```
How the points are derived. Each goes through `ComposeFinal.suf_final_2_60_2_20` / `_2_80_2_40` /
`_2_90_2_64`, or the `Itsr` versions, at realiser caps `(Qc, N) = (2^60, 2^81)`, `(2^80, 2^81)`
and `(2^90, 2^82)`, with `ℓ' = 2^20`. The steps are:
- `QcAll ≤ Qc` from `QcAll_le_of`;
- `NAll ≤ N` from `NAll_le_81` / `NAll_le_82`;
- `ellB ℓ ≤ 2^20`;
- `RealizersLe_mono`.

The EUF point at `2^40` uses `euf_ideal_bound_pow` with `num_2_80`.

What `qf` each point supports:
- **`2^20`:** up to `2^60 − 2^46` compression queries.
- **`2^40` and `2^64`:** at most `2^64`. This is the old "`qP ≤ 2^64`" assumption, now a plain cap on `qf`. Beyond about `2^69.8` the ITSR leg is vacuous; that is a proof limitation, not something the counting can remove.

## Rust level (`Ideal/RustFinalClosed.lean:36`)
`theorem rust_ideal_security_closed (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))` has three
conjuncts:
1. The Rust keygen/sign/verify compute `byteKeygen`/`byteSign`/`byteVerify` at `Link.prims`.
2. `bytesAlg … (primsG (liftC realCF)) … (optRandU oR realCF) = bytesAlg … Link.prims codec128s (fun pk => oR pk.pkSeed pk.pkRoot)`.
3. For every `S qf qs ℓ` and the four forger hypotheses, the SUF **and** EUF bounds hold: the
   general one (under `QcAll ≤ 2^126`) and the three numeric points above.

## Remaining hypotheses
Only the four bounds on the forger, plus pure arithmetic on `qf qs ℓ` (`QcAll qf qs ℓ ≤ 2^126`, or
the caps of each point). There is no `Realizes*`, no `SufRealizers`, and nothing about the
reduction.

## Caveats
- The model is a random compression table, not the real SHA-256. Conjunct 3 says nothing about
  `realCF`.
- `opt_rand` must be table-independent (`optRandU`).
- Nothing here has been audited by anyone else. `QcAll` is a deliberately crude cap; it is tight
  to within a factor of about 1.5 of the class-TCR count.
- The `FinalCore.lean` `_W` lemmas still take the WOTS realisers as arguments. They are internal
  steps; `Final.lean` discharges those arguments.
