# Handoff — composed ideal-compression-function bound (SLH-DSA-SHA2-128s)

> **Superseded (2026-11-21).** The remaining chain described here has been carried out: all
> twelve realisers are proved and the closed headline is in `Ideal/Realize/Final.lean`. Current
> state: `../../HANDOFF.md`. This file is kept as the record of the plan that was followed.


Written by the coordinator after the worker was stopped mid-task. Everything marked "checked" was
re-run by the coordinator; everything else is the worker's account or a reading of declaration
names, and is flagged as such. Nothing here has been independently audited. Nothing is committed.

Read with: `../IDEAL_STATUS.md` (top note = latest state of the bounds; audit note below it),
`AGENT_NOTES.md`, `../status/OPEN.md` (the reduction's open programs).

## 1. Where it stands

**Goal.** With SHA-256's compression function a uniformly random table `g` that the forger can
query: any forger with ≤ Qc compression queries and ≤ qs signing queries forges with probability
≤ an explicit number, no `Realizes*` hypotheses.

**Not reached.** Every composed theorem is still conditional on twelve realiser hypotheses.

Headlines (`ComposeFinal.lean`; build green, standard axioms — checked):

| theorem | conclusion | conditions |
|---|---|---|
| `suf_final` (`:172`) | `sufI ≤ epsItsrF … + (66·Qc+40)/2^128 + polyP …/2^256` | `RealizesItsrF`, `SufRealizers`, `R.Le Qc N qs' ℓ'`, `Qc ≤ 2^126` |
| `suf_final_2_60_2_20` (`:202`) | `≤ 2^-70 + 2^-128 + 2^-61` | same, at those caps |
| `suf_final_2_80_2_40` (`:222`) | `≤ 2^-50 + 2^-88 + 2^-41` | same, plus forger's `cB`-shaped queries `qP ≤ 2^64` |
| `suf_final_2_90_2_64` (`:241`) | `≤ 2^-44 + 2^-43 + 2^-31` | same, `qP ≤ 2^64`, `N = 2^82` |
| `euf_final`, `euf_final_2_60_2_20`, `euf_final_2_90_2_64` | EUF analogues | `EufRealizers` |
| `suf_final_optRandU` | `suf_final` with table-independent signing randomness | — |
| `rust_ideal_security_final` (`RustFinal.lean:35`) | Rust-level corollary | — |

`Qc` caps the **realisers'** compression queries (forger + the reduction's own hashing), not the
forger's alone. The older `suf_closed_*` / `rust_ideal_security` rest on caps the real adversaries
do not meet; they are marked superseded and should not be quoted.

**Proved (sound per the earlier audit, or new and unaudited):**
- Per-game ideal-model bounds (`Games/*`, `Inst/*`) — audited sound.
- ITSR with finer accounting — `Itsr.itsr_le_fine` (`Games/ItsrFine.lean:512`),
  `itsr_bound_128s_fine` (`Inst/ItsrFine128.lean:119`). Only queries whose block is `cB` (the
  constant second outer block of `H_msg`, `oblocksH_eq`) count toward `reuseSum`. New, unaudited.
  Proved numeric points via `reuseSum_63_12_14_le_of`: `2^-44` at `n ≤ 11·2^63`, `2^-38` at `2^67`,
  `2^-26` at `2^68`, `2^-13` at `2^69`. Vacuous from ≈ `2^69.8` (hand estimate).

**Assumed:**
- All twelve realisers: `RealizesPrf`, `RealizesMsg`, `RealizesDspr`, `RealizesForsTcr`,
  `RealizesTcr` ×4, `RealizesUd`, `RealizesPre`, `RealizesWotsTcr` (bundle `SufRealizers`), and
  `RealizesItsrF`. Each: the reduction's adversary family `B g` equals `inst A g` for ONE oracle
  program `A` with stated compression-query counts.
- That the realisers meet the caps of the closed theorems (argued from `status/OPEN.md` §2 counts:
  ≤ `269824 + qs·2007385 + 7857` hash calls, ≤ 12 compressions each).
- For ITSR: that the reduction's Thash chains never have second block `cB`. Only
  `tblocks_one_ne_cB` (F/PRF case) is proved; `H`, `T_k`, `T_len` are not. And `cP ≲ 2qs`.

## 2. The obstruction, and the Transport library that addresses it

The reduction adversaries are built over types indexed by the core bundle
(`PublicKeyCore core`, `SignatureCore`, `XmssSigCore`, `ForsTreeSigCore`; also `G2Log`,
`Lazy.OSpec`). The core contains `PRF` and `PRF_msg`, which in the ideal model depend on `g`. So
"one program for all tables" is not even well-typed without transporting those types. They are
not defeq across tables and their type equality is not provable; `rfl` times out.

`Ideal/Transport/` (10 files, 2406 lines) is the worker's answer. **State (checked):** each file
builds on its own (`lake build Ideal.Transport.<File>`), no `sorry`/`axiom`/`native_decide`/
`bv_decide`/`maxHeartbeats`; the nine `_S` headline lemmas below print
`[propext, Classical.choice, Quot.sound]`. **They are NOT imported by `Ideal.lean`**, so the
default `lake build` does not cover them, and nothing uses them yet. Unaudited; I have not read
the proofs, only the statements listed.

Design (`Core.lean`):
- `setPrfC core prf pm` / `setPrf prims prf pm`: the bundle with `PRF`, `PRF_msg` replaced; all
  carrier types, `Thash`, `H_msg` unchanged definitionally.
- `trPk`, `trFors`, `trXmss`, `trSig`: field-wise identity maps between the core-indexed
  structures at `core` and at `setPrfC core prf pm`, with `@[simp]` projection/constructor lemmas
  and injectivity.
- `krfl`: closes `a = b` by `Eq.refl a` checked by the kernel only (the elaborator will not unfold
  stuck `match` auxiliaries whose parameters differ). No axiom. This is the trick that makes the
  small steps cheap.

Contents (statement names; "`_setPrf`"/"`_tr`" = equal after transport):

| file | what it covers |
|---|---|
| `Sign.lean` | FORS/XMSS/hypertree signing with secret callback (`forsSignWithSecret_tr`, `xmssSignWithSecret_tr`, `signWithSecret_tr`, `signInternalWithSecretRandomizerM_tr`, `idealSign_tr`), public hash components, wire codec (`trCodec`, `encodeSignature_tr`, `decodeSignature_tr`), `fusedImpl_tr`, `readForgery_tr`, `g2Run_bytesToTyped_tr`, `g2Run_bytesToTypedS_tr` |
| `Verify.lean` | recovery and verification (`pkFromSigWith_setPrf`, `verifyWith_setPrf`, `verifyCalls_setPrf`, `verifyFree_setPrf`, `verifyInternalM_setPrf`, `verifyInternal_setPrf`), `classify`, `g2Valid`, `g2ClassOf`, `idealPk`, `classOut`, `memoForge_setPrf`, **`bTcrArM_forge_setPrf`** (phase 2 of class TCR, under a hypothesis `hrun` on the forger's run) |
| `AdvCommon.lean` | byte-level forger wrapper inside the three harnesses (`runForger`, `runForgerSig`, `runForgerLog`), `trLog`, `sufCheck_setPrf`, `harnessValid_setPrf` |
| `AdvLazy.lean` | `castO`/`castO'` between `Lazy.OSpec` at the two bundles, `lazyRun_setPrf`, lazy harness lemmas |
| `AdvPrf.lean` | `bPrfC_setPrf`, `bPrfWC_setPrf`, **`bPrfWC_setPrf_S`**, real/ideal experiment forms. Invariant under a change of `PRF` only (these machines evaluate `PRFmsg` themselves) |
| `AdvMsg.lean` | `bPrfMsgL_setPrf`, **`bPrfMsgWL_setPrf_S`**, real/ideal experiment forms |
| `AdvFors.lean` | `toTcr_setPrf`, `toDspr_setPrf`, **`toTcr_setPrf_S`**, **`toDspr_setPrf_S`**, experiment forms |
| `AdvWots.lean` | `rUd_setPrf`, `rPre_setPrf`, `rTcrT_setPrf`, **`_S`** forms, experiment forms |
| `AdvItsr.lean` | `bItsrL_setPrf`, **`bItsrL_setPrf_S`**, advantage/experiment forms |

So, by declaration names, the invariance-under-`setPrf` statement exists for every adversary
family. What I could NOT confirm from names alone, and the next person must check first:
- Class TCR has only the phase-2 lemma with `hrun` as a hypothesis; I saw no `bTcrArM_setPrf_S`
  (whole adversary, `choose` included, at the byte-level forger wrapper). `hrun` should follow
  from `g2Run_bytesToTyped(S)_tr`.
- Whether the `_S` lemmas are stated in the exact shape a realiser needs (both sides at
  `primsG (liftC g)` vs. a fixed base bundle; `optRand'` related to `optRand` by `hopt`).
- EUF (`bytesToTyped`, non-`S`) variants: present for some families (`bPrfC_*`, `bPrfMsgL_*`),
  not checked for all.

## 3. Remaining chain, in order

1. **Wire Transport into the build.** Add the ten imports to `Ideal.lean` (or a
   `Ideal/Transport.lean` root), run the full `lake build`, add the `_S` lemmas to
   `scratch/ideal/Axioms.lean`. Close the class-TCR gap (`bTcrArM` whole-adversary `_S` form).
2. **From `setPrf`-invariance to table-uniformity.** For each family, derive
   `B (primsG (liftC g)) = transport (B (base))` where `base` is one fixed bundle whose core does
   not depend on `g` (e.g. `setPrf (primsG (liftC g)) prf₀ pm₀` with fixed dummies — check that
   `Thash`/`H_msg` dependence on `g` is then handled by the existing `withTH` uniformity in
   `Reduction/Open`). This is where `setPrf` (changes PRF/PRFmsg only) meets `withTH` (changes
   Thash/H_msg only); together they cover all four components.
3. **Forger pass-through.** The ideal-model forger is itself an oracle program over `g`. Prove
   once that its own compression queries pass through the open programs unchanged. Not started.
4. **Hash query → compression chain.** Generic substitution: each `Thash`/`H_msg`/`PRF`/`PRF_msg`
   oracle query of an open program is replaced by its Merkle–Damgård/HMAC/MGF1 chain of `g`
   queries (`Sha/Shape.lean`, `HmacShape.lean`, `HmsgShape.lean` give the shapes), with a count
   lemma `compression queries ≤ hash queries × blocks`. Import counts from
   `Reduction.Open.final_resources_final_open_128s`; do not hand-copy numerals. Not started.
5. **One realiser end to end** — `RealizesPrf` or `RealizesTcr` — via the existing
   `Realizes*.ofEq` constructors (`Compose.lean:350–371`), with its count as a theorem. Then the
   rest: Msg, ForsTcr, Dspr, other Tcr arities, WotsTcr, Ud, Pre.
6. **`RealizesItsrF` for `bItsrL`**, including: Thash chains for `H`, `T_k`, `T_len` never have
   second block `cB` (extend `tblocks_one_ne_cB`), and `cP ≤ ~2qs`.
7. **Final headline.** Realisers removed; `Qc` restated as the forger's cap with the reduction's
   hashing added inside the bound; `optRandU` only (drop the arbitrary `g`-indexed `optRand`,
   under which realisers can be false); SUF and EUF; update `RustFinal.lean`.

## 4. Known limits that finishing the chain will NOT remove

- **ITSR at large forger budgets.** `qP` counts the forger's own `cB`-shaped queries, and a forger
  can give all its queries that shape, so the ITSR leg is vacuous once the forger exceeds ≈ `2^69.8`
  compression queries, at any `qs`. A proof-technique limit, not an attack. Fix would be a bound
  in which only target digests are coverers (re-randomising hybrid, as done on the quantum side in
  `quantum/PQ/QROM/ExactItsr4.lean`); not attempted.
- PRF oracle count exceeds `2^81` at `qs = 2^64` (hence `N = 2^82` there).
- Model is a random compression table, not Davies–Meyer / ideal cipher. Not started.

## 5. Cross-project note

`quantum/` needs this same transport to discharge its `hInd` hypothesis
(`quantum/Integration/SlhDsaComposedEnc.lean`: the PRF distinguisher machine does not depend on
the `PRF` component). `AdvPrf.lean`'s `bPrfWC_setPrf` is the classical statement of exactly that;
the quantum machine `qbPrfWC` needs the analogous lemma, presumably by the same pattern. See
`../../quantum/HANDOFF.md`.

## 6. Commands (last run by the coordinator)

```
cd security && PATH=$HOME/.elan/bin:$PATH lake build
#   → Build completed successfully (7939 jobs).      (does NOT include Ideal/Transport)
lake build Ideal.Transport.{Core,Sign,Verify,AdvCommon,AdvFors,AdvItsr,AdvLazy,AdvMsg,AdvPrf,AdvWots}
#   → each: Build completed successfully.
lake env lean scratch/ideal/Axioms.lean               # worker's list; not re-run by the coordinator
```
