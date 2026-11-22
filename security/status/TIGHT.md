# TIGHT — tightening the closed ideal-compression bound (SLH-DSA-SHA2-128s)

> **Update (second session, 2026-11-22).** Step M1 of §4.2 (shape marking in the `PRF` and
> `PRF_msg` games) is done: `suf/euf_ideal_closed_tight2` (`Ideal/Realize/FinalTight2.lean`),
> coefficient `QlinT2 = 27·qf + (qs+1)·(187792316 + 45·⌊(ℓ+56)/64⌋)`; points
> `2^-77 + 2^-132 + 2^-63`, `2^-63 + 2^-94 + 2^-58`, `2^-45 + 2^-46 + 2^-36` (the last was
> `… + 2^-35`). Step M2 (challenger-input accounting) was NOT started in Lean: the per-game
> `_fresh` plan fails at the realiser end (§7.2), an alternative is proposed there. Steps 3–5 were
> not begun (order of the brief). Details: §7.


> **Update (third session, 2026-11-22).** Current best: `suf/euf_ideal_closed_tight6`
> (`Ideal/Realize/FinalTight6.lean:126`), coefficient
> `QlinT6 = 27·qf + qs·(16944275 + 31·x) + 29487951 + 45·x`; points `2^-77 + 2^-132 + 2^-63`,
> `2^-63 + 2^-94 + 2^-59`, `2^-45 + 2^-46 + (2^-39 + 2^-40)` (P64 leg II `2^-38.44`, was
> `2^-36.19`). Steps 1–2 (answer-storing class TCR, all arities): `_tight3`. Step 3: not done —
> the store route is structurally impossible for FORS and was not built for WOTS (§8.3). Step 4:
> L5 for FORS (`_tight4`) and WOTS (`_tight5`), per-signature message-block coefficient
> (`_tight6`). Dominant now at P64: the message blocks `31·x·qs`; at P20/P40: `27·qf`. §8.

> **Update (fourth session, 2026-11-22).** Current best: `suf/euf_ideal_closed_tight8`
> (`Ideal/Realize/FinalTight8.lean:431`), `QlinT8 = 27·qf + qs·(16771392 + 14·x) + 29487855 + 13·x`;
> P64 `2^-45 + 2^-46 + 2^-39` (was `… + (2^-39 + 2^-40)`), P20/P40 unchanged. Step 1 (message blocks
> as free chain queries, `Core/ChainFine.lean`) done for four of the nine games (SM-UD ×14 in
> `_tight7`; class TCR `F`, `H` and WOTS TCR in `_tight8`); PRE, class TCR `T_len`/`T_k`, FORS TCR
> not done. Steps 2–5 assessed only. §9.

Scope: `suf_ideal_closed` / `euf_ideal_closed` (`Ideal/Realize/Final.lean`) and their
context-string / Rust / API corollaries. Quantum side, other parameter sets and the
standard-model statement are out of scope.

## 0. The bound being tightened

```
sufI S ≤ epsItsrF qf (2·qs) qf (itsrQc qs) (itsrLc ℓ) qs ℓ           -- leg I   (ITSR of H_msg)
       + (66·QcAll qf qs ℓ + 40) / 2^128                             -- leg II  (eleven games, 2^-128 part)
       + polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) / 2^256         -- leg III (eleven games, 2^-256 part)
epsItsrF qP cP q qc Lc qs ℓ = reuseSum 63 12 14 (qP + cP + 2(qs+1))               -- I.a
                            + (q + qc·Lc + (qs+1)((ℓ+56)/64+3))² / 2^256         -- I.b
QcAll = qf + (qs+1)(2^25 + 2·⌊(ℓ+56)/64⌋),   NAll = max 2^81 (17920 + 182784·qs)
```

The three numeric points (all with `ℓ ≤ 2^26`, so `x := ⌊(ℓ+56)/64⌋ ≤ 2^20`):
P20 = (`qf + 2^46 ≤ 2^60`, `qs ≤ 2^20`), P40 = (`qf ≤ 2^64`, `qs ≤ 2^40`),
P64 = (`qf ≤ 2^64`, `qs ≤ 2^64`). Stated: P20 `2^-70 + 2^-128 + 2^-61`,
P40 `2^-50 + 2^-88 + 2^-41`, P64 `2^-44 + 2^-43 + 2^-31`.

All "value" numbers below are exact evaluations of the stated formulas at the cap values (Python
with exact integers/fractions, scratch scripts `budget.py`, `num.py`, `cover.py`, `fors.py`, not
machine-checked); "proved" numbers are Lean theorems.

## 1. Loss budget (written before any proof work)

Classification: **A** = artefact of the counting/arithmetic (better arithmetic on statements
already proved removes it); **S** = structure of the reduction or of a proof technique (needs a
different argument); **I** = inherent (a matching generic attack exists).

### 1.1 Where each factor enters

| # | factor | enters at (file : lemma) | class |
|---|---|---|---|
| L1 | numeric point rounds the cap up to a power of two: `Qc = 2^60 / 2^80 / 2^90` instead of `QcAll` (`2^60`, `2^65.6`, `2^89.1`) | `FinalCore.lean`: `suf_closed_2_80_W` (`QcAll_le_of … ≤ 2^80`), `ComposeFinal.lean`: `suf_final_2_80_2_40` | A |
| L2 | one cap `Qc` for all eleven realisers, and `66 = Σ` of coefficients that include `2·q₁` / `q₁` terms, although every realiser has `q₁ = 0` (`Fors.pFors`, `Tcr.tcrP`, `Wots.pU/pP/pW` all start with `0`) | `Compose128.lean`: `Realizers.eps_le` (`epsUd_le` gives `3·Qc` for `q₂ + 2q₁`, `epsDspr_le` `2·Qc` for `2q₁`, `epsPre_le` `3Qc+2`, …) | A |
| L3 | every realiser charged the largest per-signature count `2^25` (class TCR, `q₂T ≤ qf + (qs+1)(25135729 + x)`), although PRF/PRF_msg/FORS are ≈ `2^24.4` and the three WOTS realisers `11·121857 ≈ 2^20.35` per signature (`QcW`) | `FinalCore.lean`: `QcAll`, `qPrf_le_QcAll`, …, `Final.lean`: `QcW_le_QcAll` | A |
| L4 | reduction's own hashing charged as adversary queries: each signature ≈ `2.0·10^6` tweakable-hash calls (`signHashes = 2007385`) re-evaluated by every reduction adversary in phase 2, each a potential "hit" at `2^-128` | `Realize/*Count.lean` (`q₂T`, `q2Fors`, `qPrf`, `qMsg`, `q2 … udH`), forced by the realiser shape `B g = inst A g` (`Compose.lean`: `Realizes*`) | S |
| L5 | every `Thash` call charged `thashCost len = 11` compressions; `F`, `PRF`, `H` (> 99.8 % of the calls in a signature) cost 2 | `Realize/Chain.lean`: `thashCost`; uniform weight in `qb_simulateQ_classes*` (`PrfReal`, `ForsBound`, `TcrCount`, `WotsCount1`) | A (needs per-arity counts of the open programs, see §4) |
| L6 | sum over the reduction's games: `qf` coefficient `1 + 2 + 3 + 4 + 14 + 2 + 1 = 27` (PRF, PRF_msg ×2 directions, FORS-TCR ×3, class TCR ×4, WOTS-UD ×(w−2)=14, PRE ×2, WOTS-TCR) | `Compose.lean`: `suf_ideal_bound`; `Reduction/HeadlineFinal.lean` | S (same structure as Hülsing–Kudinov / Barbosa et al.) |
| L7 | ITSR coverers: `n = qf + 2qs + 2(qs+1)` digests each counted as a potential coverer of every other (forger's own `cB`-shaped queries included) | `Games/ItsrFine.lean`: `itsr_le_fine`; `Inst/ItsrFine128.lean` | S |
| L8 | ITSR `2(qs+1)`: inner/outer SHA-256 of `H_msg` not domain separated, two coordinates per target | `Games/ItsrFine.lean` (`hashM_bound2`) | A (one more bad event, `IDEAL_STATUS.md` §7) |
| L9 | `reuseSum ≤ n·2^-168·∏_{i<14}(i + n/2^63)` (`reuseSum_le_prod`) instead of the Stirling form `n·targetCoverBound` | `Inst/ItsrNumeric.lean`: `reuseSum_le_prod` | A |
| L10 | `reuseSum_le_prod` further rounded at the points (`n ≤ 2^62` / `7·2^63` / `11·2^63`) | `ItsrNumeric.lean`: `reuseSum_63_12_14_le_small/_big`, `ComposeFinal.lean`: `_r11` | A |
| L11 | I.b: `qc·Lc` with `Lc = 2^20+1` for ALL chain queries (`Thash` chains have ≤ 11 blocks; only the `≤ qs` inner `H_msg` chains are long) | `Inst/ItsrFine128.lean`: `itsr_bound_128s_fine` (`hLc` is a uniform length bound) | A (needs a two-class chain count) |
| L12 | III: `18·(2Qc + 22N + 21)²` from `T_len`/`T_k` internal chaining-value collisions over all `≈ 2^80` key-structure targets | `Inst/TcrTight128.lean` / `Compose128.lean`: `epsTcrLen_le` | S (challenger-side collisions; negligible here) |
| L13 | caps `qf ≤ 2^64` (P40, P64), `qf + 2^46 ≤ 2^60` (P20) | the numeric theorems | A (the formula is informative up to `qf ≈ 2^69.8`, L7) |

### 1.2 Sizes at the three points (log₂ of each contribution; "stated" = the proved number)

Leg II (`2^-128` part of the eleven games):

| | P20 | P40 | P64 |
|---|---|---|---|
| stated (proved) | −61 | −41 | −31 |
| formula at `QcAll` itself (L1 removed) | −61.96 | −56.31 | −32.87 |
| L1 (rounding of the cap) | 1.0 bit | **15.3 bits** | 1.9 bits |
| per-realiser counts, `q₁ = 0` used (L2 + L3 removed): `27qf + 253924886·qs + …` | −63.25 | −58.51 | −35.83 |
| L2 + L3 | 1.3 bits (66→27 on `qf`) | 2.2 bits | **3.0 bits** (`66·2^25 = 2^31.04` → `2^27.92` per signature) |
| of which reduction hashing (L4, incl. L5) | `qs·2^27.92` = 2^-80.1 (negligible) | 2^-60.1 (≈ ½ of leg II) | 2^-36.08 (**all** of leg II) |
| L5 inside L4 (11 vs ≈2.03 compressions per call) | — | ≈ 2.4 bits of the qs part (0.4 of the total) | ≈ 2.4 bits of the hashing part (1.7 of leg II) |
| L6 (27 games vs 1 generic target) | 4.75 bits | 4.75 bits | — (masked by L4) |
| best possible (generic attack `qf/2^128`, I) | −68 | −64 | −64 |

Leg I (ITSR):

| | P20 | P40 | P64 |
|---|---|---|---|
| stated I.a / I.b | −70 / −128 | −50 / −88 | −44 / −43 |
| `n` | 2^60.00 | 2^64.00 | 2^66.32 (`5·2^64`) |
| `reuseSum_le_prod` at the actual `n` (L10 removed) | −77.9 | −63.75 | −45.69 |
| Stirling form `n·targetCoverBound(n)` (L9 removed) | −95.5 | −69.7 | −47.1 |
| I.b at actual counts, `Lc = 2^20+1` | −132.9 | −94.1 | −46.1 |
| I.b with two-class chain lengths (L11 removed) | ≈ −133 | ≈ −120 | ≈ −79 |
| ROM literature (`q·p(qs)`, below) — the inherent part | −151 | −127 | −69.75 |

Leg III (`polyP/2^256`): P20 −79.9, P40 −79.9, P64 −70.5 (dominated by L12; `NAll ≥ 2^81` is
the fixed key-structure target count, not a per-query cost). Never dominant.

**Dominant term per point.** P20: leg II, `27·qf/2^128` (L6, structural; L1–L3 cost 2 bits).
P40: leg II, by the rounding L1 (15 bits), then L2/L3 (2 bits); after that `27qf` and the
reduction's hashing (L4) are each about half. P64: leg II, entirely the reduction's hashing
(L4: `qs·2^27.92/2^128`), with ~3 bits of L2/L3 on top.

### 1.3 Best possible bound, and the literature instantiated for random functions

Generic attacks (lower bounds on any true bound):
- (Second) preimage on one 128-bit tweakable-hash output: each query hits one target with
  probability `2^-128` (the tweak/seed prevents multi-target amplification), so success
  `≈ qf·2^-128`: P20 2^-68, P40 2^-64, P64 2^-64.
- FORS few-time forgery (ITSR): per `H_msg` query the probability that all `k = 14` revealed
  indices are covered, `p(qs) = Σ_γ C(qs,γ)(1−2^-63)^{qs−γ}2^{-63γ}(1−(1−2^-12)^γ)^{14}`:
  `p(2^20) = 2^-211.0`, `p(2^40) = 2^-191.0`, `p(2^64) = 2^-133.75` (`fors.py`); attack success
  `≈ qf·p(qs)`: 2^-151, 2^-127, 2^-69.75.
- So the best possible bound is ≈ P20 `2^-68`, P40 `2^-64`, P64 `2^-63.9`.

Literature, ROM instantiation (recalled, the papers were NOT re-read in this session):
- Hülsing–Kudinov (ePrint 2022/346), SPHINCS+ tight bound:
  `PRF + PRF_msg + ITSR + SM-TCR + 3·SM-DSPR`-type sum; in the ROM each SM-TCR/SM-DSPR term is
  `O(q/2^{8n})` and ITSR is `q·p(qs)` (no `q²` term). Constant in front of `q/2^128`: a handful.
- Barbosa et al. (ePrint 2024/910), the fixed WOTS-TW argument: adds the `(w−2)·SM-UD`,
  `SM-PRE`, `SM-TCR`(chains) terms; ROM instantiation `≈ c·q/2^128 + q·p(qs)` with `c` of the
  order of our 27 (our reduction is that structure: `Reduction/HeadlineFinal.lean`).
- Neither charges the signing oracle's hashing to the adversary: in their ROM instantiations
  the challenger answers signing queries, so `qs` enters only through `p(qs)`. Our L4 is
  therefore not in the literature bound; it is an artefact of composing per-game ideal-model
  bounds through realisers (`B g = inst A g`).

## 2. Plan (ordered by bits gained per unit of work)

1. L1 + L2 + L3 + L10 (pure arithmetic over proved statements): new per-realiser evaluation of
   `Realizers.eps` with `q₁ = 0`, the actual per-realiser `q₂` caps, and exact numerics at the
   three points. Expected: P20 −61 → −63, P40 −41 → −58, P64 −31 → −35; ITSR legs
   −70/−50/−44 → −77/−63/−45, I.b −128/−88/−43 → −132/−94/−46.
2. L5 (per-arity compression counts): ≈ 2.4 bits on the hashing part (P64 −35.8 → ≈ −37.5).
   Needs per-arity hash-query counts of the eleven open programs. Plan in §4, not done.
3. L4 (stop charging the reduction's hashing): ≈ 28 bits at P64. Structural. Plan in §4.
4. L9 / L11 / L8: ITSR only; not dominant at any point after step 1. Not done.

## 3. What was proved (step 1 of the plan; all built, standard axioms only)

New files (nothing existing was changed except three `import` lines appended to `Ideal.lean`):
`Ideal/Realize/FinalTight.lean`, `Ideal/Realize/FinalPureTight.lean`,
`Ideal/RustFinalClosedTight.lean`.

Mechanism (`FinalTight.lean`):
- `Realizers.eps_le_tight` (`:184`): for any realiser bundle with `R.Le Qc N qs ℓ`, no
  first-phase queries (`q₁ = 0` for all nine `P3`/`P5` parameters) and per-realiser
  second-phase caps `QP, QM, QF, QT, QW`:
  `R.eps γu ≤ nf (linT QP QM QF QT QW) (polyP Qc N qs ℓ)`,
  `linT = QP + 2·QM + 3·QF + 4·QT + 17·QW + 40`. The `2^-256` part is the old `polyP`, unchanged.
- `QlinT qf qs ℓ = 27·qf + (qs+1)·(253924886 + 45·⌊(ℓ+56)/64⌋)` (`:226`);
  `linT_le_QlinT` (`:228`) at the realisers' proved caps (`Prf.qPrf_le'`, `Prf.qMsg_le'`,
  `Fors.q2Fors_eq`, `Tcr.q₂T_le`, `Wots.pU_le/pP_le/pW_le`); `QlinT_le_old` (`:240`):
  `QlinT ≤ 66·QcAll + 40` (never worse).
- `reuseSum_63_12_14_le_frac` (`:341`): `reuseSum_le_prod` evaluated with `n ≤ r·2^(63−d)`
  (fractional `n/2^63`), used with `d = 10`.

Headlines (same forger hypotheses as `suf_ideal_closed`; `hQ : QcAll qf qs ℓ ≤ 2^126` as before):

```
theorem suf_ideal_closed_tight … (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :      -- FinalTight.lean:306
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256
theorem euf_ideal_closed_tight …                                        -- FinalTight.lean:322
```

Numeric points (SUF and EUF each; `ℓ ≤ 2^26`):

| point | hypotheses | old (proved) | new (proved) | theorem |
|---|---|---|---|---|
| P20 | `qf ≤ 2^60` (old: `qf + 2^46 ≤ 2^60`), `qs ≤ 2^20` | `2^-70 + 2^-128 + 2^-61` (≈ 2^-60.99) | `2^-77 + 2^-132 + 2^-63` (≈ 2^-62.99) | `suf/euf_ideal_closed_tight_2_20` (`:462`, `:483`) |
| P40 | `qf ≤ 2^64`, `qs ≤ 2^40` | `2^-50 + 2^-88 + 2^-41` (≈ 2^-41.0) | `2^-63 + 2^-94 + 2^-58` (≈ 2^-57.96) | `…_tight_2_40` (`:504`, `:525`) |
| P64 | `qf ≤ 2^64`, `qs ≤ 2^64` | `2^-44 + 2^-43 + 2^-31` (≈ 2^-31.0) | `2^-45 + 2^-46 + 2^-35` (≈ 2^-35.0) | `…_tight_2_64` (`:546`, `:567`) |

Gain: 2.0 / 17.0 / 4.0 bits. Unrounded values of the new formula at the caps: leg II+III
−63.25 / −58.51 / −35.83; ITSR −77.9 / −63.75 / −45.69 (I.a), −132.9 / −94.1 / −46.1 (I.b).

Carried through:
- `Ideal/Realize/FinalPureTight.lean`: `suf/euf_ideal_pure_closed_tight` (`:27`, `:44`) — the
  general bound at message length `ℓ + 257` — and `…_tight_2_20/_2_40/_2_64` (`:61`–`:136`,
  `ℓ + 257 ≤ 2^26`, same numbers).
- `Ideal/RustFinalClosedTight.lean`: `rust_ideal_security_closed_tight` (`:36`, internal
  interface), `rust_ideal_security_closed_pure_tight` (`:93`), `api_ideal_security_closed_pure_tight`
  (`:140`): conjuncts 1 and 2 taken from the existing statements unchanged, conjunct 3 the tight
  bounds (general + three points, SUF and EUF).

## 4. What remains loose, and plans

After step 1 the dominant terms are: P20 `27·qf/2^128` (L6); P40 `27·qf/2^128` and the
reductions' hashing `2^27.92·qs/2^128` about equally; P64 the reductions' hashing alone
(`2^-36.08`), plus the message-block part `45·x·qs/2^128 = 2^-38.5` (`x = 2^20` blocks for
`2^26`-byte messages). Distance to the generic attacks: 5 / 6 / 29 bits.

### 4.1 L5 — per-arity compression counts (artefact; ≈ 1.7 bits at P64, ≈ 0.4 at P40)

Of the `2007385` hash calls per signature (`Reduction/Lazy/Open.lean: signHashes`), only
`d·(2^hp+1) = 3591` are `T_len` (11 compressions) and one is `T_k` (5); the rest are `F`, `H`,
`PRF` (2 compressions: `thashCost 1 = thashCost 2 = 2`). Weighted ≈ `4.05·10^6` compressions per
signature instead of `2.21·10^7` (factor 5.46). The per-signature constant `253924886` would drop
to ≈ `4.7·10^7`; with the unchanged message-block part, P64 leg II goes from `2^-35.83` to
≈ `2^-37.5`.

Statement: for each realiser family, `IsQueryBoundP A isCompQ q₂'` with
`q₂' = qf + Hsmall·2 + Hlen·11 + Hk·5 + (msg terms)`, `Hsmall/Hlen/Hk` hash counts by arity.
Work: (a) `Reduction/Lazy/Open.lean`, `Reduction/Open/{Prf,MsgV,Fors,Tcr,Wots*}.lean`: kind bounds
split by arity — the generic lemmas `qb_wotsTops`, `qb_xmssNode`, `xmssSignB`, `xmssPkB` already
take separate weights `cF cT cH cS`; only the instantiations (`openKeygen_kindBound`, the
`sign` and `verify` bounds, `ind K .hash` used for all three) and the closed forms need a
per-arity version (≈ 300–500 lines); (b) `Ideal/Realize/{PrfReal,MsgReal,ForsBound,TcrCount,
WotsCount1}.lean`: replace the single `Thash` class with cost `thashCost Bmax` by three classes
in `qb_simulateQ_classes4`-style transfers (≈ 150–300 lines each); (c) new `linT` instance.
Estimate 1.5–2.5k lines. Not started.

### 4.2 L4 — the reductions' own hashing charged as adversary queries (structural; ≈ 25 bits at P64)

Why it is there: a realiser is ONE oracle program `A` with `B g = inst A g`; every hash
evaluation of the reduction adversary `B` (≈ `2·10^6` per signature, recomputing honest
signatures) becomes a compression query of `A`, and the per-game theorems (`Games/*`) charge
every syntactic second-phase query `2^-128` (`ForgeBound q₂`, `DistBound q₂`).

Two mechanisms are needed, by game:
- (M1, shape marking; PRF, PRF_msg): as in `Games/ItsrFine.lean`, only queries whose first block
  can be the hidden row matter — `PRF` calls are `Thash`-shaped with an `SkAdrs`-type tweak in
  the first block (`PRF_eq_Thash`, `tblocks`), the distinguisher's `F`/`H`/`T` recomputations have
  other address types. Statement: `skPrf_bound_128s_fine : boolDist ≤ qMarked·U + (q+qO)²·V`
  with `qMarked` the raw queries whose first block has a PRF tweak plus chain queries whose
  first block does; realisers then count only the forger's queries of that shape (`≤ qf`).
  Files: `Games/Prf.lean`, `Games/MsgPrf*.lean` (fine variants, ≈ 600–900 lines each, the
  `ItsrFine` invariant pattern), `Inst/SkPrf128.lean`, `Inst/MsgPrf128.lean`, the chain/raw split
  of the PRF/Msg realisers (`Realize/PrfPort.lean`, `MsgPort.lean`: ≈ 300 lines each).
- (M2, challenger-input accounting; class TCR, FORS TCR/DSPR, WOTS UD/PRE/TCR): a second-phase
  query whose input is a challenger-registered input returns the registered value and can never
  complete a second preimage. Statement: the per-game bounds with `ForgeBound q₂` replaced by a
  bound on queries OUTSIDE the challenger's log (the per-step lemmas already charge only fresh
  cells: `prEvent_routeRO_bad_le`, `potential_le_of_step`, `IDEAL_STATUS.md` §7 item 3). The
  reductions register all key-structure nodes (`≈ 2^80` targets) in phase 1, so honest
  re-signing reads only logged inputs; the required invariant is the cover property already
  proved for the answer-storing class adversaries (`Reduction/Open/TcrStoreCover.lean`:
  `hKeygen`, `hSign`). Obstacle noted in `TcrStoreCount.lean`: a lookup-with-fallback program has
  no worst-case syntactic hash bound, so the realiser count must be the semantic one (on sound
  stores), i.e. the per-game theorems must take the semantic hypothesis. Files: `Games/Tcr*.lean`,
  `TcrMulti*.lean`, `Ud*.lean`, `Pre*.lean`, `Dspr*.lean` (a `…_fresh` variant of each headline,
  ≈ 400–800 lines each), `Inst/*128.lean`, and per-realiser cover invariants through the open
  programs (`Realize/{Tcr,Fors*,Wots*}.lean`, ≈ 1–2k lines per family).
- Remaining after M1+M2 at P64: `27·qf + 45·x·qs` per `2^128` — the message blocks of the
  signing oracle's `H_msg`/`PRF_msg` (`2^-38.5` at `ℓ = 2^26`). Removing those needs M1-style
  marking in the TCR/UD/PRE games too (an `H_msg` chain cannot end in a `Thash` cell).
Estimate: 8–12k lines; expected result ≈ `2^-59` at P64 (`27·qf` and ITSR `2^-45.7` then
dominate — ITSR becomes the bottleneck, see 4.3).

### 4.3 ITSR (L7–L11)

Not dominant at any point after step 1, but it is the next bottleneck once L4 is removed
(P64: `2^-45.7`). Cheapest: L9 (evaluate the Stirling form `n·targetCoverBound n` instead of
`reuseSum_le_prod`: −45.7 → −47.1 at P64, needs a proof of the surjection counts `S(14,r)·r!`
for `r ≤ 14`, by a recurrence, not by enumeration). L11 (two-class chain lengths in
`itsr_bound_128s_fine`; I.b −46.1 → ≈ −79 at P64) needs the realiser's chain count split into
`Thash` chains (≤ 11 blocks) and the `qs` inner `H_msg` chains (`Realize/ItsrCount.lean`,
`ItsrBound.lean`, ≈ 400 lines). L7 (structural): a re-randomising hybrid in which only target
digests are coverers (as on the quantum side, `quantum/PQ/QROM/ExactItsr4.lean`), giving
`≈ qf·p(qs)`; large.

### 4.4 Inherent / structural floor

- `qf/2^128` (generic preimage on 128-bit outputs): inherent.
- `qf·p(qs)` (FORS few-time forgery): inherent; `2^-69.75` at P64.
- the factor 27 (L6) is the structure of the reduction (sum over games, `(w−2)·UD`); a
  direct ideal-model proof could reach a small constant, but not with this reduction.
- leg III (`≈ 2^-70`–`2^-80`): challenger-side chaining-value collisions over `2^80` targets
  (L12); structural, never dominant.

## 5. Things found in existing statements and documents

No existing theorem was found false or overstated. Documentation points:
- `HANDOFF.md` (repo root) and the brief say the ITSR leg is vacuous once `qf + 2·qs` reaches
  about `2^70`; the argument of `reuseSum` is `qP + cP + 2(qs+1) = qf + 4·qs + 2`.
- `security/README.md` says `Ideal` is not a default target; `lakefile.toml` lists it in
  `defaultTargets`. `status/R-final.md` says `Final`/`RustFinalClosed` are not imported by
  `Ideal.lean`; they are.
- The P40 points (`suf/euf_ideal_closed_2_40`) are 15 bits weaker than their own general formula
  at the same caps (rounding `QcAll ≤ 2^80`); true, just loose.

## 6. Builds (run in this session)

```
cd security && export PATH=$HOME/.elan/bin:$PATH
lake build Ideal.Realize.FinalTight        # Build completed successfully (7324 jobs).
lake build Ideal.Realize.FinalPureTight    # Build completed successfully (7332 jobs).
lake build Ideal.RustFinalClosedTight      # Build completed successfully (8061 jobs).
lake build Ideal                           # Build completed successfully (8064 jobs).
lake build                                 # Build completed successfully (8081 jobs).
```
Every `#print axioms` of the three new files: `[propext, Classical.choice, Quot.sound]`; no
`sorryAx` anywhere in the `lake build` output. The new files contain no `sorry`, `axiom`,
`native_decide`, `bv_decide`, `set_option` or `maxHeartbeats`.

## 7. Second session: M1 done, M2 analysed (not implemented)

### 7.1 Step M1 — shape marking for the `PRF` and `PRF_msg` games (done, built)

New files (nothing existing changed; eight `import` lines appended to `Ideal.lean`):

| file | content |
|---|---|
| `Ideal/Games/PrfFine.lean` | `Prf.markQ blk` (compression query whose block is `blk a k` for SOME `a`, `k`); `prfAdvantageI_le_marked`: `prfAdvantageI ≤ qM/|K| + (q+qO)²/|St|` |
| `Ideal/Inst/SkPrf128Fine.lean` | `skPrf_bound_128s_marked`; `key_of_tblocks_eq_blk128` (a first `Thash` block equal to a key block carries a secret-key address key) |
| `Ideal/Realize/PrfMark.lean` | the `PRF` realisers make `≤ qPrfM qf qs ℓ` marked queries (`AprfS_mark`, `AprfE_mark`); `qPrfM_le : qPrfM ≤ qf + (qs+1)(32272 + 2x)` |
| `Ideal/Games/MsgPrfFine.lean` | `MsgPrf.markK ik ok` (block `ik k` or `ok k` for some `k`); `macAdvantageI_le_marked`, `prT_mac_two_sided_marked` (`2qM/|K|` in place of `2q/|K|`) |
| `Ideal/Realize/MsgMark.lean` | `msgPrf_bound_128s_marked`; the `PRF_msg` realisers make `≤ qMsgM qf qs ℓ` HMAC-key-block queries (`AmsgS_mark`, `AmsgE_mark`); `qMsgM_le : qMsgM ≤ qf + (qs+1)(39438 + x)` |
| `Ideal/Realize/FinalTight2.lean` | `ideal_bound_core_legs` (composition with the PRF / PRF_msg legs as hypotheses), `Realizers.epsL_le_tight`, `QlinT2`, `QlinT2_le_QlinT`, `tight2_le_tight`, the headlines and the six points |
| `Ideal/Realize/FinalPureTight2.lean` | context-string interface (`ℓ + 257`) |
| `Ideal/RustFinalClosedTight2.lean` | `rust_ideal_security_closed_tight2`, `rust_ideal_security_closed_pure_tight2`, `api_ideal_security_closed_pure_tight2` |

Why the reduction's `F`/`H` evaluations are never marked:
- PRF game: the seed block is no key block (`sb128_ne_blk128`); the first block of
  `Thash(pk, key, xs)` begins with `key`, so it is a key block only if `key` is the key of a
  secret-key address; every tweakable-hash call of the SLH-DSA programs is at an address of type
  `≤ 4` (VCVio `GeneralScheme.keygenInternalWithSecretM_pred`, `signInternalWithSecretRandomizerM_pred`,
  `verifyInternalM_pred`), and `Concrete.keySeparated_sha2Primitives` separates those keys from
  the secret-key keys (`Prf.keygen_sk`, `sign_sk`, `verify_sk`, `PprfS_sk`); `F`, `H` have no
  block after the first. What is still counted: the forger's queries, the 9 blocks after the
  first of each `T_len`/`T_k` (`512 + 3585·qs + 8` such evaluations, `Prf.PprfS_long`), every
  block of `H_msg` and `PRF_msg`.
- PRF_msg game: bytes `16..63` of `ikey k`/`okey k` are `0x36`/`0x5c`; byte 16 of a seed block
  is `0`, byte `22 + 16n` of the first block of an `n ≤ 2`-value `Thash` is the padding byte
  `0x80` (`Ideal.sb128_not_keyBlk`, `tblocks_not_keyBlk`). Counted: the forger's queries, every
  block of `T_len`/`T_k` (`11` each) and of `H_msg`.

Headline (`Ideal/Realize/FinalTight2.lean:418`, same hypotheses as `suf_ideal_closed`):
```
theorem suf_ideal_closed_tight2 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ} (hqf …) (hqs …) (hlong …) (hout …) (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT2 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256
QlinT2 qf qs ℓ = 27 * qf + (qs + 1) * (187792316 + 45 * ((ℓ + 56) / 64))      -- :327
```
`euf_ideal_closed_tight2` (`:434`) the same with `eufI`. `QlinT2_le_QlinT` (`:341`) and
`tight2_le_tight` (`:451`): never above `suf_ideal_closed_tight`.

Points (proved, SUF and EUF; `ℓ ≤ 2^26`):

| point | hypotheses | tight (session 1) | tight2 (proved) | theorem |
|---|---|---|---|---|
| P20 | `qf ≤ 2^60`, `qs ≤ 2^20` | `2^-77 + 2^-132 + 2^-63` | `2^-77 + 2^-132 + 2^-63` | `suf/euf_ideal_closed_tight2_2_20` (`:479`, `:539`) |
| P40 | `qf ≤ 2^64`, `qs ≤ 2^40` | `2^-63 + 2^-94 + 2^-58` | `2^-63 + 2^-94 + 2^-58` | `…_tight2_2_40` (`:499`, `:559`) |
| P64 | `qf ≤ 2^64`, `qs ≤ 2^64` | `2^-45 + 2^-46 + 2^-35` | `2^-45 + 2^-46 + 2^-36` | `…_tight2_2_64` (`:519`, `:579`) |

Unrounded legs II+III at the caps (Python, exact integers, NOT machine-checked; script
`num2.py` in the scratch area): P20 −63.245 → −63.245 (unchanged: `27·qf` dominates),
P40 −58.51 → −58.64, P64 −35.83 → −36.19. Gain 0 / 0.13 / 0.36 bits. Small because the two
PRF games carried only `66·10^6` of the `254·10^6` compressions charged per signature.

Context-string forms: `suf/euf_ideal_pure_closed_tight2{,_2_20,_2_40,_2_64}`
(`FinalPureTight2.lean:27`–`:136`). Rust/API: `rust_ideal_security_closed_tight2` (`:37`),
`rust_ideal_security_closed_pure_tight2` (`:94`), `api_ideal_security_closed_pure_tight2`
(`:141`) in `RustFinalClosedTight2.lean`; conjuncts 1–2 are those of the existing statements.

State after M1, P64 (unrounded, outside Lean): leg II `2^-36.19` = reduction hashing in the
class-TCR (`4·25135729 ≈ 1.0·10^8` per signature), FORS (`3·21450308 ≈ 6.4·10^7`) and WOTS
(`17·QcW ≈ 2.3·10^7`) games, plus the message blocks `45·x·qs` (`2^-38.5`); ITSR `2^-45.7`,
`2^-46.1`. Distance to the generic attack at P64: ≈ 28 bits.

### 7.2 Step M2 — not implemented; why the planned route fails, and an alternative

Test target: class TCR, arity 1 (`tcrArityT_bound_128s`, realiser `Tcr.realizesTcrF_S`). The
test was done by reading the proofs (`Games/TcrDefs.lean`, `TcrMultiPhase2.lean`,
`TcrMultiBasic.lean`, `Realize/Tcr.lean`, `TcrCount.lean`, `Reduction/Open/TcrStore*.lean`);
no Lean was written for it.

**The `_fresh` per-game plan (§4.2, M2).** The per-game bound charges phase two through
`ForgeBound q₂ := ∀ st pk, IsQueryBoundP (A.forge st pk) isRight q₂` (all states, all oracle
answers) and `MP2.prEvent_bad_le_of_step_cap` with the query predicate `isRight`. A version that
charges only fresh cells is provable in principle: a step at a cached cell of `routeRO` neither
changes the cache nor makes `MP2.Good` fail. But the count of fresh-cell queries is a property
of the run of `routeRO F.IV (F.sb seed) cv` from the phase-one cache `c`, not of the program,
so the hypothesis replacing `hq₂` has to be stated over that internal simulation (cache
satisfying `MInv`, hidden row `cv`). For a realiser to discharge it one needs, inside that
simulation, that every compression of the reduction's honest recomputation is a cached cell:
(i) `MInv` covers only target chains (`MInv.tgt`), so it must be extended to the chains of all
collection queries; (ii) the realiser's phase-two Thash inputs must be shown to be inputs it
registered in phase one (`TcrStoreCover`'s `calls_*` lemmas give this for the Reduction-level
programs, not for the chain-interpreted port program `tcrMOpenP` run under `routeRO`);
(iii) through `chainImpl`, a registered input's compressions must be shown to hit exactly the
cells written by the challenger's chain query, at the symbolic `.inr`/`.inl` cell keys of the
cache. Each layer is a new invariant through code that currently has none (`Port.lean`,
`Phase1.lean`, `Tcr.lean`), and the per-game theorems of all seven game families would carry
a hypothesis about their own proof internals. Not attempted: I judged it out of reach as one
finished step.

**Proposed alternative (no change to any per-game theorem).** `RealizesTcr` asks only for
equality of experiment DISTRIBUTIONS at every table, not of adversaries. So:
1. Target the answer-storing adversary `bTcrArA n` instead of `bTcrArM n`:
   `Reduction.Open.bTcrArA_experiment_eq` (used in `TcrStoreHeadline.lean`) already gives equal
   experiments at every `Structural` bundle, in particular at `primsG (liftC g)`.
2. Build the ideal-model adversary whose phase one is that of `bTcrArA` (state: secret table,
   honest calls `L`, store `S = ann pk L` of the challenger's answers) and whose phase two answers
   every `Thash` query of key regeneration and signing FROM THE STORE, with a default value and NO
   compression query on a miss, and evaluates only `H_msg` and the verification of the forgery by
   compression chains. Its `ForgeBound` is then syntactic:
   `qf + (qs+1)·hmsgCost ℓ + 11·verifyHashes ≈ qf + (qs+1)(x+3) + 43219`, against
   `qf + (qs+1)(25135729 + x)` now.
3. Equality of the two phase-two distributions on the support of phase one: on a sound store
   containing the honest calls, the pinned key regeneration and signatures make no query outside
   the store (`TcrStoreCover.cover_keygen`, `cover_sign`, i.e. the `hKeygen`, `hSign` of
   `storeForgeOpen_hashes_of_cover`), so the no-fallback and the fallback handlers agree on every
   query actually made (a generic "no `p`-query ⇒ handlers agreeing off `p` give the same
   simulation" lemma, by induction).
4. Reuse the existing realiser chain (`Transport/AdvTcr.lean`, `Realize/Tcr.lean`,
   `TcrCount.lean`) for the new phase two; the open program has to be split so that verification
   keeps the chain handler.
Expected effect (outside Lean): class TCR's `4·25135729` per signature → `4·(x + O(10))`; P64
leg II `2^-36.19` → `≈ 2^-37.0` (the FORS and WOTS realisers and the message blocks then
dominate: `2^-37.0` is `3QF + 17QW + 45x` per signature). The same pattern should apply to the
FORS (`bOpenPreS`) and WOTS (`bWotsS`) reductions if they have answer-storing variants with
cover lemmas; I did not check. Estimated size for class TCR: 1.5–2.5k lines, most of it the
transport (`setPrf` invariance) of the new adversary and the split open program.

**Cheaper gain not taken (order of the brief).** L5 (§4.1) applies to every realiser now and
does not depend on M2: TIGHT's estimate is P64 `2^-35.83 → ≈ 2^-37.5` before M1; after M1 the
same arithmetic (outside Lean, factor 5.46 on the remaining hashing part) gives roughly `2^-36.2 → 2^-37.7`.

### 7.3 Builds (this session)

```
cd security && export PATH=$HOME/.elan/bin:$PATH
lake build Ideal.Realize.FinalTight2        # Build completed successfully (7336 jobs).
lake build Ideal.Realize.FinalPureTight2    # Build completed successfully (7344 jobs).
lake build Ideal.RustFinalClosedTight2      # Build completed successfully (8073 jobs).
lake build Ideal                            # Build completed successfully (8080 jobs).
lake build                                  # Build completed successfully (8097 jobs).
```
Every `#print axioms` of the eight new files: `[propext, Classical.choice, Quot.sound]` (two
arithmetic lemmas `[propext, Quot.sound]`); `grep -c sorryAx` over the full `lake build` log: 0.
No `sorry`, `axiom`, `native_decide`, `bv_decide`, `maxHeartbeats` in the new files.

## 8. Third session: answer-storing realisers (round-3 brief)

### 8.1 Steps 1–2 — class TCR, all four arities (done, built)

The route of §7.2 works. One construction, parametric in the arity `n`, so steps 1 and 2 came
together (no separate one-arity headline was made: it would be the same theorem at `n = 1`).

| file | content |
|---|---|
| `Ideal/Realize/TcrStore3.lean` | generic: `lkImpl pk S` (no-fallback lookup handler: stored `Thash` values, `default` on a miss, no `Thash` query ever forwarded); `lk_tbl_eq` (on a sound store, a program whose pinned run has no `Thash` query outside the store is interpreted by the table identically with and without `lkImpl`; induction over the program); `miss_keygen`, `miss_sign` (from `TcrStoreCover.cover_keygen`, `pin_openSign_eq`, `wSign_subset`); `tcrMOpenPS` (the port program `tcrMOpenP` with key regeneration and signing through `lkImpl`, verification unchanged); `tcrMOpenPS_tbl` (`:351`, at the store `ann pk (honestCalls tbl pk)` it is interpreted as `tcrMOpenP`); counts `tcrMOpenPS_port/_th/_hmsg/_bad`; the hash-free recording router `routeHFA` (`= routeA`), `tcrPhase1A` (`= (bTcrArA n A).choose`, `bTcrArA_choose_eq_A` `:827`), `routeHFA_cap/_len` |
| `Ideal/Realize/Tcr3.lean` | `advT3` (`:61`), `forgeP3G T H` (second phase written over `R₀ T H`), `forgeP3G_inst` (`:69`), `exp3_eq` (`:171`, via `bTcrArA_choose_run`, `bTcrArM_choose_run` at `structural₀`), `adv3G_TH` (bundle-independence by kernel `rfl` with abstract `T`, `H`), `advT3_eq` (`:210`): the experiment of `instRT (advT3 …) g` equals that of `bTcrArM n (S.typedS (optRandU oR) pkSeedDist g)` at every table |
| `Ideal/Realize/TcrCount3.lean` | counts, `tcrP3`, `realizesTcr3S/E` (`:160`, the SAME families as `realizesTcrS/E`), `q₂T3_128s` (`:188`): `q₂T3 = qf + 86416 + (qs+1)·(x+3)` against `q₂T = qf + (277681 + 2007385·qs)·11 + (qs+1)(x+3)`; `q₂T3_le_q₂T` |
| `Ideal/Realize/FinalTight3.lean` | bundles `sufRealizers3`/`eufRealizers3`, `QlinT3` (`:84`), `linT_le_QlinT3`, `QlinT3_le_QlinT2` (`:98`), headlines, `tight3_le_tight2` (`:208`), six points |
| `Ideal/Realize/FinalPureTight3.lean`, `Ideal/RustFinalClosedTight3.lean` | context-string and Rust/API corollaries (conjuncts 1–2 unchanged) |

Technical points met (for whoever extends this): (i) the elaborator and the kernel must never
compare a term over `P₀ = R₀ dT dH` with one over `R₀ (thG g) (hmG g)` *through their arguments*
— `dT =?= thG g` unfolds SHA-256 symbolically (timeouts, "deep recursion"). Every bridge is a
lemma with ABSTRACT bundle functions (`tcrMOpenPS_withTH`, `adv3G_TH`, `tcrPhase1A_withTH`),
proved by kernel `rfl`, then instantiated; the experiment comparison is done entirely over
`R₀ (thG g) (hmG g)` (`adv3G … (thG g) (hmG g)`). (ii) `rw` with such lemmas often fails at
instance transparency (`Bytes 16` vs `(R₀ …).PkSeed`); `erw` or `kexact` were used.

Headline (`FinalTight3.lean:175`, same hypotheses as `suf_ideal_closed`):
```
theorem suf_ideal_closed_tight3 (S : ForgerI) (oR : Bytes 16 → Bytes 16 → ProbComp (Bytes 16))
    {qf qs ℓ : ℕ} (hqf …) (hqs …) (hlong …) (hout …) (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT3 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256
QlinT3 qf qs ℓ = 27 * qf + (qs + 1) * (87595076 + 45 * ((ℓ + 56) / 64))
```
`euf_ideal_closed_tight3` (`:191`) the same with `eufI`.

Points (proved, SUF and EUF, `ℓ ≤ 2^26`; `FinalTight3.lean:260`–`:360`):

| point | tight2 | tight3 (proved) |
|---|---|---|
| P20 (`qf ≤ 2^60`, `qs ≤ 2^20`) | `2^-77 + 2^-132 + 2^-63` | `2^-77 + 2^-132 + 2^-63` |
| P40 (`qf ≤ 2^64`, `qs ≤ 2^40`) | `2^-63 + 2^-94 + 2^-58` | `2^-63 + 2^-94 + (2^-59 + 2^-62)` |
| P64 (`qf ≤ 2^64`, `qs ≤ 2^64`) | `2^-45 + 2^-46 + 2^-36` | `2^-45 + 2^-46 + (2^-37 + 2^-44)` |

Unrounded legs II+III at the caps (Python, exact integers, NOT machine-checked; scratch
`num3.py`, `pt.py`): P20 −63.245 (unchanged, `27·qf`), P40 −58.64 → −58.87, P64 −36.19 → −36.99.
The two-term third summands are the best `2^-k + 2^-k'` roundings (−58.83, −36.99).

State after steps 1–2, per signing query (`2^-128` units): FORS TCR/DSPR `3·21450308 =
64350924`, WOTS UD/PRE/TCR `17·1340427 = 22787259`, PRF+PRF_msg marked `≈ 1.1·10^5`, class TCR
`4·86419`; message blocks `45·x` (`47185920` at `x = 2^20`). P64 leg II `2^-37.0`; ITSR `2^-45.7`
(not the bottleneck: leg II is 8.7 bits above it).

### 8.2 What exists for the other families (checked before building)

- Answer-storing adversaries and cover lemmas exist ONLY for class TCR
  (`Reduction/Open/TcrStore*.lean`). Nothing for FORS (`Lazy.bOpenPreS`, `toTcr`, `toDspr`) or
  WOTS (`Lazy.bWotsS`, `rUd`, `rPre`, `rTcrT`).

### 8.3 Step 3 — FORS TCR/DSPR, WOTS UD/PRE/TCR: NOT done

**FORS: the store route is impossible for these games, not merely unbuilt.**
`forsTcrProblem` and `forsDsprProblem` are `.standalone` (`Reduction/ForsTightFinal.lean:51,58`):
the collection is `Empty`, so the first phase of any adversary sees only the challenge oracle
(images of the FORS-leaf targets) and never a `Thash` value at the game's seed. Every hash value
of key regeneration and signing other than the target images depends on `PK.seed`, which is
revealed only in phase two; in the ideal model it can be obtained only by compression queries
of phase two. So for these games, with the per-game bounds that charge every phase-two query,
the reduction's re-signing hashing is necessarily charged. Options: (a) a collection-augmented
FORS game (new Reduction-level problems and per-game ideal bounds — a change of the
standard-model reduction); (b) M1-style shape marking in the FORS games (only phase-two
compression queries whose block is the first `F` block at a FORS-leaf tweak can matter; the
honest `H`/`T_k`/WOTS/XMSS evaluations never are; the leaf `F` evaluations of re-signing
`≈ k·2^a = 57344` per signature still would be): a `…Fine` version of the FORS-TCR and DSPR
game bounds in the style of `Games/PrfFine.lean` (est. 1.5–2k lines), plus a marked count of
the FORS realiser. Not attempted.

**WOTS: possible in principle, not built (judged not worth it).** The three WOTS games have
the whole `Thash` as collection, and `chooseBody` of `bWotsS` already makes a collection query
for every hash it later needs (FORS trees, `T_k`, XMSS nodes; `WotsSparse.lean` header), so a
recording phase one plus a cover lemma for `signFromHist` would remove the `121857` hash calls
per signature of the three WOTS realisers. Nothing exists: recording `wColl`, the closed form of
the recording phase one, the cover lemma for `signFromHist`, and three realisers (UD real+ideal,
PRE, TCR) on the `WotsPort`/`WotsReal`/`WotsRealize` stack — est. 2–3k lines. Gain (outside
Lean): P64 leg II `2^-36.99 → 2^-37.27` before L5, `≈ 0.1` bit after L5 (§8.4); none at P20/P40.
Per the brief ("completely or not at all") it was not started.

### 8.4 Step 4 — what was done (all built)

Order chosen by gain at P64 after 8.1 (FORS 64.4M, message blocks 47.2M, WOTS 22.8M per
signing query): L5 for FORS, L5 for WOTS, then the message-block coefficient. ITSR (`2^-45.7`) was
never the bottleneck (8.6).

**L5, FORS** (`Ideal/Realize/ForsL5.lean`): `forsSignOpen_long`, `openKeygen_long`,
`forsFindOpenP_long` (long `Thash` queries — more than two values — of the FORS port program:
`512 + 3585·qs`), `chainImplP_boundL` (4-class transfer: `2` per hash query, `9` more per long
`Thash`, `hmsgCost ℓ` per `H_msg`; `thashCost_le_L`), `q2ForsL_eq` (`:240`):
`q2ForsL = qf + 544286 + 3932321·qs + (2qs+1)(x+3)` (was `qf + 2968229 + 21450308·qs + …`),
realisers `realizesDsprL_S/E`, `realizesForsTcrL_S/E` (`:285`–`:309`; same adversaries and
experiments as `ForsRealize.lean`, new `hq₂`). Headline `suf/euf_ideal_closed_tight4`
(`FinalTight4.lean:163`, `:179`), `QlinT4 = 27·qf + (qs+1)·(35041115 + 45x)` (`:71`),
`QlinT4_le_QlinT3`, `tight4_le_tight3` (`:196`).

**L5, WOTS** (`Ideal/Realize/WotsL5.lean`): `wotsSignFromHistO_long` (`3577` long per signature,
`wotsSignLong_128s` `:156`), `wPhase2P_long` (the one-off answer extraction bounded by its hash
count), `chain_countL`, `udDist/preInv/tcrForge_boundL`, realisers `realizesUdL`, `realizesPreL`,
`realizesWotsTcrL` (+`…E`, `:285`–`:323`), cap `QcWL = qf + 2·(121857·qs + 146514) +
9·(3577·qs + 146514) + (qs+2)(x+3)` (`:334`, `QcWL_le_QcW`). Headline `…_tight5`
(`FinalTight5.lean:175`, `:191`), `QlinT5 = 27·qf + 16944275·qs + 29487951 + 45·x·(qs+1)` (`:82`;
the shape changes because the one-off WOTS answer extraction, `≈ 2.9·10^7`, is now larger than
the per-signature constant), `QlinT5_le_QlinT4`, `tight5_le_tight4` (`:208`).

**Message blocks per signing query** (`Ideal/Realize/FinalTight6.lean`, arithmetic only, same
bundle as `_tight5`): `QlinT5`'s `45·x·(qs+1)` uses the one-off coefficient for every signing
query; per signing query the realisers issue `31` `H_msg` chains (PRF 2, PRF_msg 2, FORS 3·2,
class TCR 4, WOTS 17). `QlinT6 = 27·qf + qs·(16944275 + 31·x) + 29487951 + 45·x` (`:33`),
`QlinT6_le_QlinT5` (`:48`), headline `…_tight6` (`:126`, `:142`), `tight6_le_tight5` (`:159`).

Each of `_tight4/5/6` has the six points, the context-string forms (`FinalPureTight{4,5,6}.lean`)
and the Rust/API forms (`RustFinalClosedTight{4,5,6}.lean`: e.g. `rust_ideal_security_closed_tight6`
`:38`, `rust_ideal_security_closed_pure_tight6` `:95`, `api_ideal_security_closed_pure_tight6`
`:142`; conjuncts 1–2 those of the untightened statements).

Points (proved, SUF and EUF each, `ℓ ≤ 2^26`):

| | P20 (`qf ≤ 2^60, qs ≤ 2^20`) | P40 (`qf ≤ 2^64, qs ≤ 2^40`) | P64 (`qf ≤ 2^64, qs ≤ 2^64`) |
|---|---|---|---|
| tight2 | `2^-77 + 2^-132 + 2^-63` | `2^-63 + 2^-94 + 2^-58` | `2^-45 + 2^-46 + 2^-36` |
| tight3 | same | `… + (2^-59 + 2^-62)` | `… + (2^-37 + 2^-44)` |
| tight4 | same | `… + 2^-59` | `… + (2^-38 + 2^-40)` |
| tight5 | same | `… + 2^-59` | `… + (2^-38 + 2^-49)` |
| tight6 | same | `2^-63 + 2^-94 + 2^-59` | `2^-45 + 2^-46 + (2^-39 + 2^-40)` |

Unrounded legs II+III at the caps (Python, exact integers, NOT machine-checked; `pt.py`,
`pt5.py`, `pt6.py`): P20 −63.245 (all versions); P40 −58.64 (t2) → −58.87 → −59.00 → −59.05 →
−59.10 (t6); P64 −36.19 (t2) → −36.99 → −37.71 → −38.07 → −38.44 (t6).

### 8.5 What remains loose after `_tight6` (P64, per signing query, `2^-128` units)

| part | size | class | what would remove it |
|---|---|---|---|
| message blocks `31·x` (`x ≤ 2^20`) | `3.25·10^7` | S | M1-style marking: an `H_msg` chain block is never target-shaped in the TCR/UD/PRE/DSPR games; `…Fine` per-game bounds for FORS TCR/DSPR, class TCR, WOTS UD/PRE/TCR (like `Games/PrfFine.lean`) |
| FORS re-signing `3·3.93·10^6` | `1.18·10^7` | S | standalone FORS games (§8.3): marking (only first `F` blocks at FORS-leaf tweaks matter) or a collection-augmented FORS game |
| WOTS re-signing `17·2.76·10^5` | `4.7·10^6` | S/A | the store route (§8.3; now worth `≈ 0.14` bit) |
| class TCR, PRF, PRF_msg | `≈ 4.5·10^5` | A | negligible |
| `27·qf` | — | S (L6) | dominant at P20, P40 |

P64 leg II `2^-38.44`; ITSR `2^-45.7 + 2^-46.1`; generic attack `≈ 2^-64`.

### 8.6 ITSR (L7, L9, L11) — assessed, not done

ITSR is `2^-45.7` (I.a) and `2^-46.1` (I.b) at P64, 7.3 bits below leg II after `_tight6`, and
below `2^-63` at P20/P40: no ITSR improvement changes any stated point now. L9 (Stirling form) and
L11 (two-class chain lengths) are artefacts: −45.7 → −47.1 and −46.1 → ≈ −79. L7 (re-randomising
hybrid in which only target digests are coverers; `quantum/PQ/QROM/ExactItsr4.lean` is the
template) is structural: it would bring I.a to `≈ qf·p(qs) = 2^-69.75` at P64 and remove the
vacuity limit at `qf ≈ 2^69.8`. It needs a new per-game ITSR bound in the ideal-compression model
(the coverers become the challenger's target digests, themselves `H_msg` chains through the random
table; the hybrid re-samples the cells of those chains) and a new realiser count — several
thousand lines. It matters only once leg II is below `≈ 2^-46` at P64, i.e. after the message-block
and FORS marking above. Not started.

### 8.7 Builds (this session)

```
cd security && export PATH=$HOME/.elan/bin:$PATH
lake build Ideal.Realize.TcrStore3 Ideal.Realize.Tcr3 Ideal.Realize.TcrCount3
lake build Ideal.Realize.FinalTight3 Ideal.Realize.FinalPureTight3 Ideal.RustFinalClosedTight3
lake build Ideal.Realize.ForsL5 Ideal.Realize.WotsL5
lake build Ideal.Realize.FinalTight{4,5,6} Ideal.Realize.FinalPureTight{4,5,6} Ideal.RustFinalClosedTight{4,5,6}
lake build Ideal        # Build completed successfully (8114 jobs).
lake build              # Build completed successfully (8131 jobs); 0 `sorryAx` in the log.
```
All `#print axioms` lines of the new files: `[propext, Classical.choice, Quot.sound]` (a few
arithmetic lemmas `[propext]` or `[propext, Quot.sound]`). No `sorry`, `axiom`, `native_decide`,
`bv_decide`, `maxHeartbeats` in the new files. 17 new files, 17 `import` lines appended to
`Ideal.lean`; nothing existing changed.

## 9. Fourth session: message blocks as free chain queries (round-4 brief)

### 9.1 Step 1, first game end to end — SM-UD (done, built)

**The marking argument** (generic, `Ideal/Core/ChainFine.lean`).  A second-phase program may be
given with *chain queries* `bs` (the Merkle–Damgård iteration from `IV` over `bs`, interface
`pcS = unifSpec + (hS + chQ)`), expanded into raw compression queries by `expandImpl IV`.  In
the ideal (hidden-prefix) game phase two answers `(IV, sb seed)` by `cv` and row `cv` from the
private row table.  A chain query whose first block is not `sb seed` (`freeC`) reads only public
cells unless a public cell read has the value `IV` or `cv` (`PubBad`): cell `0` is `(IV, b₀)`,
`b₀ ≠ sb seed`, public since `cv ≠ IV`; every later cell's chaining value is the value of the
previous (public) cell.  `free_fold`, `routeRO_potential_fine` (pathwise: a potential raised only
by row cells rises by `≤ n·ε`, `n` the RAW queries, or the final cache is `PubBad`),
`prEvent_routeRO_pubBad_le` (`Pr[PubBad] ≤ 2q₂/|St|` from a non-`PubBad` cache, `q₂` ALL
compression queries).  The block *contents* play no role: a free chain may contain any blocks
(the forger's messages are arbitrary); what is used is only that the chain does not start with
the seed block, which the realiser guarantees by construction (below).  A query that does start
with the seed block is issued raw and charged.

**The game** (`Ideal/Games/UdFine.lean`).  `ud_ideal_le_fine` / `ud_bound_fine`: `ud_bound` with
the distinguisher given as the expansion of `dC st pk` (`hdC`), and, outside a set `bad` of public
seeds of probability `≤ β`, `dC st pk` with `≤ qM` raw queries and only free chain queries:
`udRealI ≤ udIdealI + (qM + q₂·β)/|M'| + 2q₁γ + (old 2^-256 term + 1 + 2(q₁+qc)·max 1 L + 2q₂)/|St|`.
The extra `/|St|` terms: `cv = IV`, a public value of phase one equal to `IV` or `cv`
(`prEvent_preSim_pubHit_le`, `prT_preSim_cvBad_le`: `≤ (q₁+qc)·max 1 L/|St|` each; `cv` is drawn
after phase one), a fresh public value of phase two equal to `IV` or `cv` (`2q₂/|St|`).  At bad
seeds the old count `q₂` is charged.

**The realiser** (`Ideal/Realize/WotsUdFine.lean`).  `udDistC st pk`: `udDist` with the handler
`chainImplH st.1.1 pk`, which issues each of the two SHA-256 chains of an `H_msg` query as one
chain query unless its first block is `sb128 pk` (then raw, `chainOrRaw`).  `udDist_eq_expand`
(the same program), `udDistC_free` (by construction), `udDistC_boundR`: for `pk ≠ 0`, at most
`qMU qf qs = qf + 2·udH qs + 9·udLg qs` raw queries — the `H_msg` chains cost none because every
`H_msg` query of the second phase is at the public seed `pk` (`wUdP_foreign`) and both first
blocks carry `pk` in bytes `16..31` where `sb128` has zeros (`iblocksH_head_ne`,
`oblocksH_head_ne`).  `bad = {0}`, `β = γ`.  `wotsUd_bound_128s_fine`, `udLeg_fine(E)`.

**The headline** (`Ideal/Realize/FinalTight7.lean`).  `ideal_bound_core_legs7` (UD leg as a
hypothesis), `Realizers.epsL7_le_tight` (`linT7 = QP + 2QM + 3QF + 4QT + 3QW + 14QU + 40`,
`polyP7 = polyP + 14·(20N + 1)`), `QlinT7 qf qs ℓ = 27·qf + qs·(16944233 + 17·x) + 29487867 + 17·x`
(`QlinT7_add : QlinT7 + 14·(qs+2)·(x+3) = QlinT6`), `tight7_le_tight6` (the right-hand side is
never above `_tight6`'s: the `2^-256` part gains `14(20·NAll+1) ≤ 14(qs+2)(x+3)·2^128`).
```
theorem suf_ideal_closed_tight7 (S : ForgerI) (oR …) {qf qs ℓ : ℕ} (hqf …) (hqs …) (hlong …) (hout …)
    (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT7 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP7 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256
```
(`FinalTight7.lean`, same hypotheses as `suf_ideal_closed`), `euf_ideal_closed_tight7`; points
`…_tight7_2_20/_2_40/_2_64`; context-string forms `FinalPureTight7.lean`; Rust/API forms
`RustFinalClosedTight7.lean` (`rust_ideal_security_closed_tight7`,
`rust_ideal_security_closed_pure_tight7`, `api_ideal_security_closed_pure_tight7`; conjuncts 1–2
unchanged).

| point | tight6 | tight7 (proved) |
|---|---|---|
| P20 (`qf ≤ 2^60`, `qs ≤ 2^20`) | `2^-77 + 2^-132 + 2^-63` | same |
| P40 (`qf ≤ 2^64`, `qs ≤ 2^40`) | `2^-63 + 2^-94 + 2^-59` | same |
| P64 (`qf ≤ 2^64`, `qs ≤ 2^64`) | `2^-45 + 2^-46 + (2^-39 + 2^-40)` | `2^-45 + 2^-46 + (2^-39 + 2^-43)` |

Unrounded legs II+III (Python, exact integers, NOT machine-checked, `scratchpad/tight4/pt7.py`):
P20 −63.245 (unchanged), P40 −59.096 → −59.138, P64 −38.44 → −38.95.

### 9.2 Step 1, three more games — single-block SM-TCR (class TCR `F`, `H`; WOTS-chain TCR) (done, built)

`Ideal/Games/TcrFine.lean`: `prEvent_chainRO_pubHit_le` (generic phase one: a fixed value is a
public value with probability `≤ (q₁ + C)·max 1 L/|St|`), `prT_cvBad_le_of`,
`idealGame_le_of_inv_fine` (`idealGame_le_of_inv` with the phase-two bound needed only from
non-`PubBad` caches, larger by `b` on a seed set `bad`), `prEvent_tcr_phase2_le_fine`,
`tcr_ideal_le_fine`, `tcr_bound_fine`:
`tcrAdvantage ≤ (qM+1)·δ + (q₂+1)·δ·β + q₁γ + (old + 2(q₁+qch+qc)·max 1 L + 2q₂)/|St|`.
Generic addition in `ChainFine.lean`: `prEvent_routeRO_bad_fine` (a bad predicate fired only by
fresh row cells: `Pr[bad ∧ ¬PubBad] ≤ n·ε`, `n` raw queries).

`Ideal/Realize/TcrWotsFine.lean`: `tcrForgeC` / `tcrForge_eq_expand` / `tcrForgeC_boundR`
(WOTS-chain TCR, raw cap `qMW = qf + 2·tcrH + 9·tcrLg ≤ QU`), `tcrMOpenPS_foreign`,
`forgeP3GC` / `forgeP3G_eq_expand` / `forgeP3GC_boundR` (class TCR, raw cap
`qMT qf = qf + 86416`: the answer-storing realiser's only per-signature compressions were the
`H_msg` chains).  `Ideal/Realize/TcrLegsFine.lean`: `tcrArityT_bound_128s_fine`,
`wotsTcrT_bound_128s_fine`, `epsTcrF`, `classTcrLeg_fine(E)` (`n = 1 ∨ n = 2`),
`wotsTcrLeg_fine(E)`.

`Ideal/Realize/FinalTight8.lean`: `ideal_bound_core_legs8`, `Realizers.epsL8_le_tight`
(`linT8 = QP + 2QM + 3QF + 2QT + 2QTF + 2QW + QWT + 14QU + 40`, `polyP8 = polyP7 + 3(Qc + 40N + 1)`),
`QlinT8 qf qs ℓ = 27·qf + qs·(16771392 + 14·x) + 29487855 + 13·x` (`QlinT8_add`:
`QlinT8 + 172841·qs + 3·qs·x + 4·x + 12 = QlinT7`), `tight8_le_tight7` (under the headline's own
hypothesis `QcAll ≤ 2^126`).  Headline (`FinalTight8.lean:431`, same hypotheses as
`suf_ideal_closed`):
```
theorem suf_ideal_closed_tight8 … (hQ : QcAll qf qs ℓ ≤ 2 ^ 126) :
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      epsItsrF qf (2 * qs) qf (Itsr.itsrQc qs) (Itsr.itsrLc ℓ) qs ℓ +
        ((QlinT8 qf qs ℓ : ℕ) : ℝ≥0∞) / 2 ^ 128 +
        (polyP8 (QcAll qf qs ℓ) (NAll qs) qs (ellB ℓ) : ℝ≥0∞) / 2 ^ 256
```
`euf_ideal_closed_tight8` (`:447`); points `…_tight8_2_20/_2_40/_2_64`; `FinalPureTight8.lean`,
`RustFinalClosedTight8.lean` (`rust_ideal_security_closed_tight8`, `…_pure_tight8`,
`api_ideal_security_closed_pure_tight8`).

| point | tight6 | tight7 | tight8 (proved) |
|---|---|---|---|
| P20 | `2^-77 + 2^-132 + 2^-63` | same | same |
| P40 | `2^-63 + 2^-94 + 2^-59` | same | same |
| P64 | `2^-45 + 2^-46 + (2^-39 + 2^-40)` | `… + (2^-39 + 2^-43)` | `2^-45 + 2^-46 + 2^-39` |

Unrounded legs II+III (Python, NOT machine-checked, `scratchpad/tight4/pt8.py`): P20 −63.245,
P40 −59.148, P64 −39.093 (tight6 −38.44).

### 9.3 Step 1, what was NOT done (and why)

Remaining message-block charge per signing query after `_tight8`: `14·x` (PRF 2, PRF_msg 2,
FORS TCR 3×2, SM-PRE 2, class TCR `T_len`, `T_k` 1+1).  Not built (budget of the session), the
route is the one of 9.1–9.2 in each case:
* SM-PRE (`Games/PreIdeal.lean`): `prT_pre_phase2_le` uses `prEvent_routeRO_bad_le` (`PreGood`),
  `routeRO_potential_le` (hidden reads) and the guess term; the fine forms are
  `prEvent_routeRO_bad_fine` and `routeRO_potential_fine`; the cv-averaging needs
  `prEvent_preSim_pubHit_le` generalised from `UdAdv.pick` to `PreAdv.choose` (same oracle
  interface).  Realiser: `preInvC` exactly as `udDistC` (`wPreP_foreign` as `wTcrP_foreign`).
  Expected P64 gain (outside Lean): −39.09 → −39.19.
* class TCR `T_len`, `T_k` (`Games/TcrMulti*`, `MP2.prEvent_bad_le_of_step_cap`): a different
  phase-two machinery (multi-block targets); the free-chain argument applies unchanged to the
  `H_msg` chains but `MP2` would need its own fine step lemma.  −39.19 → −39.30.
* FORS TCR (`Games/TcrFV*`): the game side is the same as `tcr_bound_fine` (`FvInv.good` gives
  `TcrGood`; `prEvent_fv_phase2_le` has the same two calls).  The realiser side is the costly part:
  its second phase is `simulateQ (outerC tg) (simulateQ (chainImplP tbl) …)` (`ForsGuess.lean`),
  two stateful handler layers over the FORS game interface `GP P₀`, so `chainImplH` has to be
  re-done for `liftCS`/`outerC` and the expansion identity carried through `StateT`.
  −39.30 → −39.68.
With all of step 1: P64 leg II ≈ `2^-39.68` (Python).

### 9.4 Step 2 (FORS re-signing) — assessed, not started

A sound marking exists and needs no hypothesis on the forger: in the FORS-TCR (and every
single-block TCR) game, a cached private-row cell can break `TcrGood` only if its block's tweak
`btw B` is a target tweak (`prEvent_not_tcrGood_cacheQuery_row_le` charges `δ` only then).
So a raw phase-two query `(c, b)` with `c = IV` (never in row `cv`, since `cv ≠ IV`) or with
`btw b ∉ T`, for a set `T` containing every challenge tweak of phase one (a hypothesis on the
ideal-model adversary's OWN challenge queries, `AllQueriesSatisfy`), is never charged — on every
run, whatever the queries are.  For the FORS realiser `T` = FORS-leaf addresses; marked raw
queries per signature would be the second compression of each FORS-leaf `F` (`k·2^a = 57344`) and
the continuation blocks of the long `Thash` queries (`9·3585`, their tweak bytes are hash values,
so they must be charged in the worst case).  Missing: per-address-type counts through the FORS
open programs (`Lazy.qb_forsSign`, `qb_authPath`, … are uniform in the address; a count of `F`
calls at FORS-leaf addresses needs the address arguments of every call: est. 1.5–2k lines).
Expected (Python): after steps 1 and 2, P64 leg II ≈ `2^-40.8`.

### 9.5 Steps 3–5 — assessed, not started

* Step 3 (WOTS re-signing, store route §8.3): `17·(2·121857 + 9·3577) = 4.69·10^6` per signing
  query; after steps 1–2 it would be about half of the remaining per-signature coefficient
  (Python), i.e. within the 2-bit window: worth doing after step 2, not before.
* Step 4 (ITSR L7): ITSR is `2^-45.69 + 2^-46.1` at P64, leg II after all of steps 1–3 ≈
  `2^-41.5`; ITSR is not the bottleneck at any point yet.  The plan of §8.6 stands: a
  re-randomising hybrid (template `quantum/PQ/QROM/ExactItsr4.lean`) in which the coverers are the
  target digests (themselves `H_msg` chains through the table), bringing I.a to `≈ qf·p(qs)`;
  missing: the per-game ITSR bound in that form and its realiser count (several thousand lines).
  L11 (two-class chain lengths, I.b −46.1 → ≈ −79) is the cheap part and should come first.
* Step 5 (factor 27 on `qf`): the factor is the sum over the reduction's games of the per-game
  charge of each forger query (PRF 1, PRF_msg 2, FORS TCR 3, class TCR 4, UD 14, PRE 2, WOTS TCR 1).
  Tweak marking (9.4) would make a forger query count in a TCR-type game only if its block's tweak
  is that game's target type, and the target-tweak sets of the games are nearly disjoint (the 14
  UD hybrids target distinct chain positions).  But the composition applies each per-game bound
  with a worst-case count per game, and the forger may put all its queries into any one game's
  tweak set; a gain needs a JOINT accounting across games (`Σ_G E_G[#queries in T_G]` under
  different experiments), which the per-game structure does not give.  Not an artefact of the
  arithmetic; structural (L6).  Nothing cheap was found.

### 9.6 Builds (this session)

```
cd security && export PATH=$HOME/.elan/bin:$PATH
lake build Ideal.Core.ChainFine Ideal.Games.UdFine Ideal.Games.TcrFine
lake build Ideal.Realize.WotsUdFine Ideal.Realize.TcrWotsFine Ideal.Realize.TcrLegsFine
lake build Ideal.Realize.FinalTight7 Ideal.Realize.FinalPureTight7 Ideal.RustFinalClosedTight7
lake build Ideal.Realize.FinalTight8 Ideal.Realize.FinalPureTight8 Ideal.RustFinalClosedTight8
lake build Ideal        # Build completed successfully (8138 jobs); 0 `sorryAx`, 0 errors in the log.
lake build              # Build completed successfully (8155 jobs); 0 `sorryAx`, 0 errors in the log.
```
All `#print axioms` of the new files: `[propext, Classical.choice, Quot.sound]` (a few arithmetic
lemmas `[propext]` or `[propext, Quot.sound]`).  No `sorry`, `axiom`, `native_decide`,
`bv_decide`, `maxHeartbeats` in the new files.  12 new files, 12 `import` lines appended to
`Ideal.lean`; nothing existing changed.
