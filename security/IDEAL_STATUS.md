> **Note, 2026-11-22 (tightening).** Tighter forms of the closed bounds, same forger hypotheses:
> `suf_ideal_closed_tight` / `euf_ideal_closed_tight` (`Ideal/Realize/FinalTight.lean`; the
> coefficient `66·QcAll + 40` becomes `QlinT = 27·qf + (qs+1)(253924886 + 45·⌊(ℓ+56)/64⌋)`) with
> points `2^-77 + 2^-132 + 2^-63` (`qf ≤ 2^60`, `qs ≤ 2^20`), `2^-63 + 2^-94 + 2^-58`
> (`qf ≤ 2^64`, `qs ≤ 2^40`), `2^-45 + 2^-46 + 2^-35` (`qf ≤ 2^64`, `qs ≤ 2^64`); context-string
> and Rust/API forms in `Ideal/Realize/FinalPureTight.lean`, `Ideal/RustFinalClosedTight.lean`.
> Loss budget and plans: `status/TIGHT.md`.

# Ideal-compression-function bounds for the hash assumptions of the SLH-DSA-SHA2-128s reduction

> **Note, 2026-11-21.** Where this file says the external pure interface (sign/verify with a
> context string) is not covered, that is no longer so: `suf_ideal_pure_closed`,
> `euf_ideal_pure_closed` (`Ideal/Realize/FinalPure.lean`) and
> `rust_ideal_security_closed_pure` (`Ideal/RustFinalClosedPure.lean`) state the closed bounds
> for it, with the message length `ℓ` replaced by `ℓ + 257`.

> **Update (2026-11-21): the composed ideal-compression theorem is finished. Read this first;
> everything below it describes an earlier, conditional state.**
> All twelve realisers are proved (`Ideal/Realize/*.lean`). `suf_ideal_closed` / `euf_ideal_closed`
> (`Ideal/Realize/Final.lean:74`, `:91`) have hypotheses on the forger only: at most `qf`
> compression queries, `qs` signing queries, messages of at most `ℓ` bytes, plus
> `QcAll qf qs ℓ ≤ 2^126`. Numeric points (messages ≤ 2^26 bytes): `qs ≤ 2^20`, `qf ≤ 2^60 − 2^46`:
> `2^-70 + 2^-128 + 2^-61`; `qs ≤ 2^40`, `qf ≤ 2^64`: `2^-50 + 2^-88 + 2^-41`; `qs ≤ 2^64`,
> `qf ≤ 2^64`: `2^-44 + 2^-43 + 2^-31`. Rust level: `rust_ideal_security_closed`
> (`Ideal/RustFinalClosed.lean:36`). `lake build` green (8035 jobs), standard axioms. The theorem
> is about the internal interface (Algorithms 18–20). State, file map, caveats and the
> statement-level audit: `../HANDOFF.md`, `status/AUDIT-closed.md`, `status/R-final.md`.


> **Update after the audit (2026-11-20, later). Read this first; it answers audit items 1–4.**
>
> New modules (in `Ideal.lean`, `lake build` green, 7939 jobs; axioms of every theorem named here
> `[propext, Classical.choice, Quot.sound]`): `Ideal/Games/ItsrFine.lean`,
> `Ideal/Inst/ItsrFine128.lean`, `Ideal/ComposeFinal.lean`, `Ideal/RustFinal.lean`.
>
> **Proved.**
> * *ITSR with finer accounting (audit item 1).* `Itsr.itsr_le_fine` (generic) and
>   `itsr_bound_128s_fine`: the adversary has raw compression queries and **chain queries**
>   (`bs ↦ mdFold g IV bs`, the way every SHA-256 evaluation uses `g`). Only raw queries whose
>   block is the constant second outer block `cB` of `H_msg` (`oblocksH_eq`), chain queries whose
>   SECOND block is `cB`, and `2(qs+1)` calls of the final check are coordinates of `reuseSum`:
>   `itsrIF A ≤ reuseSum 63 12 14 (qP + cP + 2(qs+1)) + (q + qc·Lc + (qs+1)((ℓ+56)/64+3))²/2^256`.
>   All other compression work enters only the `Q²/2^256` term.
> * `reuseSum_63_12_14_le_of` (`n ≤ r·2^63` ⇒ `≤ r·∏_{i<14}(i+r)/2^105`): `2^-44` at `n ≤ 11·2^63`,
>   `2^-38` at `2^67`, `2^-26` at `2^68`, `2^-13` at `2^69`; vacuous from about `2^69.8`.
> * *Composition with honest caps (audit item 2).* `suf_final` (general),
>   `suf_final_2_60_2_20` (`2^-70 + 2^-128 + 2^-61`), `suf_final_2_80_2_40`
>   (`2^-50 + 2^-88 + 2^-41`), `suf_final_2_90_2_64` (`2^-44 + 2^-43 + 2^-31`, `N = 2^82`);
>   `rust_ideal_security_final`. `Qc` is the cap on the REALISERS' compression queries (forger
>   plus the reduction's own hashing). The old `suf_closed_*` are marked superseded.
>
> **Not proved — still hypotheses of every composed theorem.**
> * **All twelve realisers** (`SufRealizers`: eleven; `RealizesItsrF`: the ITSR one in the new
>   form). None is discharged. Obstruction found: the reduction adversaries are built over types
>   indexed by `(primsG (liftC g)).core` (`PublicKeyCore`, `Signature`, `G2Log`, `Lazy.OSpec`),
>   and the core contains `PRF` and `PRF_msg`, which depend on `g`. `Reduction/Open`'s uniformity
>   (`withTH`) fixes the core; identifying the open programs at two tables needs transports of
>   every core-indexed type through every reduction program. Not built. Also not built: the
>   forger's own compression queries exposed in the open programs, and the generic
>   hash-query → chain-query substitution with counts.
> * That the realisers meet the caps used in the closed theorems (argued from `status/OPEN.md` §2,
>   not proved), in particular that the ITSR realiser's chain queries with second block `cB` are
>   only its `H_msg` evaluations (`tblocks_one_ne_cB` proves the block fact for `F`/`PRF` only).
> * *ITSR at large forger budgets.* `qP` includes the forger's own compression queries with block
>   `cB`; a forger can give all its queries that shape. So `suf_final_2_80_2_40` and
>   `suf_final_2_90_2_64` assume `qP ≤ 2^64`; with `qP = Qc` the ITSR leg is vacuous at both
>   points. Only `(2^60, 2^20)` is free of that extra assumption. Removing it needs a bound in
>   which only target digests are coverers (re-randomising hybrid); not attempted.
> * `optRand` (audit item 4): still an arbitrary `g`-indexed family in the statements; for a
>   family that genuinely depends on `g` the realiser hypotheses can be false. PRF-oracle count:
>   `17920 + qs·182784 > 2^81` at `qs = 2^64`, so `suf_final_2_90_2_64` uses `N = 2^82`.
> * EUF analogues are now stated: `euf_final`, `euf_final_2_60_2_20`, `euf_final_2_90_2_64`
>   (same hypotheses for the EUF adversaries). `suf_final_optRandU`: `suf_final` at a
>   table-independent `opt_rand` family `optRandU oR` (the form in which realisers can be true).
>
> **Second pass on the realisers (same day): none proved; blocked. Precise blocker.**
> For a realiser one needs, for each open program `X` of `Reduction/Open` (e.g.
> `tcrMOpen`, `forsFindOpen`, `wotsUdOpenAll`, `bPrfWCOpen`, `msgOpenWV`, `Lazy.itsrOpen`) with
> the forger `Coded.reduce … S` built from ONE byte-level program `S`:
> `∀ c c' : CompressFn, X (prims := primsG c) … = X (prims := primsG c') …` (*uniformity in the
> table*). This reduces to naturality in the core of VCVio's generic signing / verification code
> (`GeneralScheme.signInternalWithSecretRandomizerM`, `keygenInternalWithSecretM`,
> `forsPkFromSigWith`, `GeneralHypertree.pkFromSigWith`, the wire codec; about 110 definitions
> over `PublicKeyCore`, `SecretKeyCore`, `SignatureCore`, `XmssSigCore`, `ForsTreeSigCore`, all
> structures indexed by `core`, which contains `PRF`, `PRF_msg`). Checked: (i) these types are
> not definitionally equal across tables and their equality is not provable, so only explicit
> equivalences can work; (ii) `rfl` cannot do it (intermediate binder types differ; a program
> applied to the abstract forger is stuck); even
> `Lazy.OSpec (primsG c) gspec = Lazy.OSpec (primsG c') gspec := rfl` times out in the
> elaborator (400k heartbeats); (iii) `Reduction/Open`'s `withTH` lemmas do not help, because
> `primsG c` and `primsG c'` differ in the core, and changing the scheme to one with a
> table-independent core changes `PRF`/`PRF_msg`, i.e. the scheme. No transport library was
> written. Everything else needed (pass-through of the forger's own queries, hash-query →
> chain-query substitution with counts) is downstream of this and was not started.

> **Audit note (independent review, 2026-11-20 19:20 PST). Read this before the tables below.**
>
> The per-game theorems are sound and about the real SHA-2 constructions. The composed numbers are
> weaker than §8 reads:
>
> 1. **ITSR leg is vacuous at qs = 2^64 for the Reduction's actual adversary.** `itsr_bound_128s`
>    counts every compression query of the adversary as a coordinate of `reuseSum`. The Reduction's
>    ITSR adversary `bItsrL` signs every query itself (`lazyHashes = 269824 + qs·2007385`), so a
>    realiser needs about 2^85 own compression queries at qs = 2^64, where `reuseSum` exceeds 1
>    (it passes 1 near n = 2^70). `suf_closed_2_64_memo` / `_store` assume `RealizesItsr … (2^64)`,
>    which is not plausibly satisfiable. With honest accounting the ITSR bound is informative only
>    for qs up to about 2^43. Likely repair (not proved): mark only adversary queries whose block is
>    the constant second outer block of `H_msg`.
> 2. **`suf_closed_2_64_store` and the "answer-storing" rows assume `R.Le (2^68)` for adversaries
>    (`bTcrArM`, `bOpenPreS`, …) whose own phase-2 hashing is about qs·2^21.** No answer-storing
>    adversary is named in the hypothesis. Only `suf_ideal_bound_2_90` matches the Reduction's
>    resource counts; the (2^60, 2^40) and (2^40, 2^20) rows are off by a small factor too.
> 3. **All twelve realisers are unproved.** The supportable composed figure today is
>    `εI + 2^-31` at Qc = 2^90, with εI itself not established at qs = 2^64 (item 1).
> 4. Minor: `optRand` may depend on g by its type; PRF oracle count slightly exceeds N = 2^81
>    without caching; §4–§6 contain text superseded by §8.


Library `Ideal` (`security/Ideal/`, root `Ideal.lean`, 67 modules, ≈18.4k lines), in the default
`lake build` of `security/` (targets `Link`, `E2E`, `Reduction`, `Ideal`; 7887 jobs, success).
No `sorry`, `axiom`, `native_decide`, `bv_decide`, no `maxHeartbeats` overrides. Every theorem
named below prints `[propext, Classical.choice, Quot.sound]` or a subset
(`lake env lean scratch/ideal/Axioms.lean`). Nothing outside `security/Ideal`, `Ideal.lean`,
`lakefile.toml` (one `[[lean_lib]]` + default target) and `scratch/ideal/` was changed.

## 1. Model

SHA-256's compression function is a **uniformly random table** `g : St × Blk → St`
(`St = Bytes 32` chaining values, `Blk = Bytes 64` blocks; `Ideal.CF St Blk`), and every
adversary has **oracle access to `g`** (spec `Ideal.hS St Blk`) in all phases. Everything else is
the real construction: Merkle–Damgård with FIPS 180-4 padding, truncation, HMAC, MGF1, FIPS 205
§11.2.1.

Why this model and not Davies–Meyer: it is the weakest idealisation in which the twelve games are
information-theoretically hard, VCVio has lazy/eager random-function machinery but no ideal-cipher
(inverse-query) machinery, and it already exposes all structural issues the task lists
(truncation, shared first block, length extension, key in message position, seed hiding).
What Davies–Meyer (`h(c,m) = E_m(c) + c`, `E` ideal cipher with inverse queries) would change —
NOT proved here, and ePrint 2026/2624 was not consulted: (i) "fresh answer is uniform" becomes
"uniform among unused permutation values" (a PRP/PRF switching term of order `Q²/2^256`);
(ii) inverse queries let the adversary create cells `(c, m)` with random `c` and output `z + c`
for chosen `z`, and fixed points `h(c,m) = c`; the hidden-seed, target-collision and guessing
steps below charge events of the form "a query lands in a hidden row / at a hidden cell" or "a
fresh output hits a fixed value", which stay `≈ 2^-256` resp. `2^-128` per (forward or backward)
query, so the same bounds are expected up to constants and the switching term, but each step
would have to be redone for the two-sided interface.

Ideal-model quantity for a game: VCVio's experiment for the Reduction's problem at the primitives
built from `g`, run with the adversary whose compression queries are answered by `g`, with `g`
uniform: `𝒟[do g ← $ᵗ CF; Experiment (inst A g)] {true}` (wrappers `idealAdv`/`idealAdvT`/
`cfAdvantage`; literal forms are the `*_def` theorems). Only the adversary's OWN compression
queries are counted (`q₁` before, `q₂` after the seed reveal); challenger-side hashing (target
and collection oracle answers) is never charged at `2^-128`.

## 2. This is the scheme's hash, not a lookalike (`Ideal/Sha/`)

* `Sha/Generic.lean`: `sha256G c`, `mgf1G c`, `hmacSha256G c`, `sha2ThashG c p`, …,
  `sha2PrimitivesG c p`, `primsG c : Primitives Link.vp.params` — verbatim copies of VCVio's
  definitions with the compression function `c` abstracted.
  `sha2PrimitivesG_compress : sha2PrimitivesG compress p = sha2Primitives p := rfl`,
  `primsG_compress : primsG compress = Link.prims := rfl`.
* `Sha/Instantiate.lean`: `liftC (g : CF St Blk) : CompressFn`, `realCF : CF St Blk`,
  **`liftC_realCF : liftC realCF = VCVio.Algorithms.Sha2.compress`**,
  `primsG_liftC_realCF : primsG (liftC realCF) = Link.prims`, `card_St : card St = 2^256`.
  Each instance file also proves `…Problem … (primsG (liftC realCF)) … = …Problem … Link.prims …`
  (for ITSR and PRF_msg at the level of the hash function only, see §6).
* `Sha/Shape.lean`, `HmacShape.lean`, `HmsgShape.lean`: MD shapes for every table `g`:
  `sha256G_shape`, `thash_shape : Thash_g pk a xs = out16 (keyedChain IV128 sb128 g pk (tblocks a xs))`
  (first block `sb128 pk = pk ‖ 0^48`; `tblocks` independent of `pk`, jointly injective, first
  block contains the tweak, exact block count `(22+16n+8)/64` after the first),
  `PRF_eq_Thash`, `msgPrf_shape`, `hmsg_shape`; truncations `out16`, `dig30` map the uniform
  distribution to the uniform distribution.

## 3. Core lemmas (`Ideal/Core/`)

* `hiddenPrefix` (HiddenPrefix.lean + HP*.lean): for any two-phase game whose phase one uses the
  keyed chain only through the challenger and does not know the seed,
  `Pr[real] ≤ Pr[ideal] + q₁·γ + (2q₁ + C(1+2L) + 1)/|St|`; in the ideal game phase one reads a
  private row table instead of row `cv = g(IV, sb seed)`, and `seed`, `cv` are drawn after phase
  one. `γ` = max probability of a seed value, `q₁` = adversary's phase-one compression queries,
  `C` = challenger chain evaluations, `L` = blocks after the first. Only `q₁` multiplies `γ`.
* LazyLemmas / SimLemmas / HiddenInput: step bounds, fusion of nested simulations, invariants,
  hidden-input (deferred sampling) lemmas.

## 4. The twelve games at SLH-DSA-SHA2-128s (`Ideal/Games/`, `Ideal/Inst/`)

`U = 2^-128`, `V = 2^-256`; `γ` as above (`= U` for uniform `PK.seed`; `_uniform` corollaries);
`q₁/q₂` = adversary's own compression queries before/after the seed reveal; `qch`, `qc` =
its challenge / collection queries; `L` = max blocks after the first in its collection queries.

| headline term | theorem | bound |
|---|---|---|
| SM-TCR `F`, `H` (`thashArityProblemT`, n = 1, 2) | `tcrArityT_bound_128s` | `(q₂+1)·U + q₁·γ + (2q₁ + (qch+qc)(1+2L) + 2)·V` |
| SM-TCR `F` on chains (`wotsTcrProblemT`) | `wotsTcrT_bound_128s` | same |
| SM-TCR `F` at FORS leaves, final validity (`forsTcrProblem`) | `forsTcr_bound_128s` | `(q₂+1)·U + q₁·γ + (2q₁ + qch + 2)·V` |
| SM-TCR `T_len` (n = 35, 10 blocks) | `tcrLen_bound_128s` | `(q₂+22)·U + q₁·γ + (18·Q² + 2q₁ + (qch+qc)(1+2·max 9 L) + 1)·V`, `Q = q₁+q₂+(qch+qc)(1+max 9 L)+21` |
| SM-TCR `T_k` (n = 14, 4 blocks) | `tcrK_bound_128s` | `(q₂+10)·U + q₁·γ + (18·Q² + …)·V`, `Q = q₁+q₂+(qch+qc)(1+max 3 L)+9` |
| SM-PRE `F` (`wotsPreProblem`) | `wotsPre_bound_128s` | `2(q₂+1)·U + q₁·γ + (2q₁ + (qch+qc)(1+2L) + 2)·V` |
| SM-UD `F` (`wotsUdProblem`), both directions | `wotsUd_bound_128s(_ge)` | `Real ≤ Ideal + q₂·U + 2q₁·γ + 2(2q₁ + (qch+qc)(1+2L) + 1)·V` |
| SM-DSPR `F`, final validity (`forsDsprProblem`) | `forsDspr_bound_128s` | `Success ≤ SPProbability + 2q₁·γ + (4q₁ + 2qch + 3)·V` for `q₂ ≤ 2^126` |
| PRF on `SkAdrs` (`skPrfC`) | `skPrf_bound_128s` | `boolDist ≤ q·U + (q+qO)²·V` (`q` own compression queries, `qO` oracle queries) |
| PRF_msg (`msgPrf`, HMAC), both directions | `msgPrf_bound_128s` | `2q·U + (q + qO·((mlen+24)/64+1) + 2)²·V` |
| ITSR of `H_msg` (`itsrProblem`) | `itsr_bound_128s` | `reuseSum 63 12 14 (q + 2(qs+1)) + (q + (qs+1)((ℓ+56)/64+3))²·V` |

Also the non-tight-cap instances (`tcrArity_bound_128s`, `wotsTcr_bound_128s`, Inst/Tcr128.lean)
and generic theorems for any MD-shaped family (`tcr_bound`, `tcr_bound_multi`, `tcrFV_bound`,
`pre_bound`, `ud_bound`, `dspr_bound`, `prfAdvantageI_le`, `macAdvantageI_le`, `Itsr.itsr_le`).

Remarks on the shapes.
* No multi-target loss: the number of targets / challenger-side evaluations (`qch`, `qc`, up to
  `2^80`) appears only multiplied by `2^-256` (linearly for single-block members, quadratically —
  `18·Q²·V`, internal chaining-value collisions — for `T_len`, `T_k`; `(2^82)²·18/2^256 ≈ 2^-88`).
* Seed hiding is used and needed: the term `q₁·γ` is the chance that a pre-reveal query guesses
  `PK.seed`; without hiding, TCR on a 128-bit truncation would only be birthday-hard.
* In the PRF game the adversary chooses `PK.seed`; the secret is in the message position; the
  bound's `(q+qO)²·V` is collisions among first-block chaining values.
* DSPR: in the ideal model `Success ≤ SPProbability` exactly (up to the hidden-prefix error) as
  long as `q₂ ≤ 2^126`: a second preimage exists with conditional probability `≥ 1/2`.
* ITSR: `reuseSum h a k n` is VCVio's explicit bound for "in `n` independent uniform digests some
  one is covered by the others" (`Covering.lean`); `≤ n·targetCoverBound` (`itsr_bound_128s_closed`).
  The tuple has `q + 2(qs+1)` coordinates, not `q + qs + 1`: the inner and outer SHA-256 calls of
  `H_msg` are not domain separated, so one extra compression call per target is counted
  (Inst/Itsr128.lean header). There is no `q·qs·U` term. **Not evaluated numerically.**

## 5. Composition (`Ideal/Compose.lean`, `Compose128.lean`)

Per table `g` the Reduction's linear headline (`slhdsa_bytes_{suf,euf}_cma_linear`) holds at
`prims := primsG (liftC g)` (`structuralC`, `codecC`; `codecC_compress = codec128s := rfl`,
`bytesAlg_realCF`). `ForgerI` = one byte-level forger program with compression-oracle access;
`sufI S` = its SUF-CMA advantage against `bytesAlg` averaged over a uniform table
(`sufI_eq_cfAvg`). Averaging the linear form is exact (`cfAvg` is linear) — the absolute-value
form would not compose (per-table distinguishing advantages have a `≈ 2^-64` floor).

`suf_ideal_bound` / `euf_ideal_bound`:
`sufI S ≤ ε_prf + ε_msg + εI + (ε_dspr + 3ε_forsTcr) + (ε_F + ε_H + ε_Tlen + ε_Tk) + 14·ε_ud + ε_pre + ε_wotsTcr`,
each `ε` the bound of §4 at the parameters of a **realiser**.

**Named hypotheses (the only unproven content):**
1. Eleven realisability hypotheses `RealizesPrf`, `RealizesMsg`, `RealizesDspr`, `RealizesForsTcr`,
   `RealizesTcr` (×4), `RealizesUd`, `RealizesPre`, `RealizesWotsTcr`: for the Reduction's adversary
   `Bᵢ` applied to the forger instantiated at `g`, there is an ideal-model adversary `Aᵢ` (an
   oracle program with the stated query bounds) with the same experiment distribution for every
   `g`. The Reduction's adversaries evaluate the hash as local pure computation; a realiser makes
   those evaluations explicit compression queries. Not proved for any of them.
2. `hI : itsrSufI S ≤ εI` (table-averaged ITSR advantage of `bItsrL`); `itsr_bound_128s` gives it
   from a twelfth realiser, but that glue lemma and the numeric value of `reuseSum` are not done.

Numeric (`suf_ideal_bound_numeric`, uniform seed): if all realisers' own-query parameters are
`≤ Qc ≤ 2^126`, challenge/collection/PRF-oracle counts `≤ N`, PRF_msg oracle queries `≤ qs` on
messages `≤ 64ℓ` bytes, `L ≤ 10`:
`sufI S ≤ εI + (66·Qc + 40)/2^128 + polyP Qc N qs ℓ / 2^256`.
Proved evaluations at `N = 2^81`, `qs = 2^64`, `ℓ = 2^20`:
* `suf_ideal_bound_2_90` (`Qc = 2^90`): `sufI S ≤ εI + 2^-31`;
* `suf_ideal_bound_2_65` (`Qc = 2^65`): `sufI S ≤ εI + 2^-56`.

Which `Qc` is justified for forger queries `q = qs = 2^64`: a realiser's own queries are the
forger's `q` plus the reduction's own post-seed hash evaluations, `≈ qs·2^21` hash calls of
`≤ 11` blocks (`final_resources_final_128s`), i.e. `Qc ≈ 2^89–2^90` and the bound `εI + 2^-31`.
`Qc = 2^65` would be justified only by bounds that charge solely queries at cells not already
fixed before the seed reveal (the reduction's re-evaluations of honest values hit cached cells and
cannot cause any of the charged events); the per-step lemmas already charge only fresh cells, but
the theorems are stated with syntactic query counts, and this refinement is NOT proved.

## 6. Where it stops / limits

* Realisability (§5.1) is the gap between the composed corollary and an unconditional theorem.
* The `2^-31` vs `2^-56` gap (§5) and the unevaluated `reuseSum` (§4).
* `itsrProblem` / `msgPrf` at `realCF`: equality with the Reduction's problem is proved for the
  hash function (`itsrProblem_realCF_hash`, `msgPrf_eq`), not as a structure equality (kernel
  blow-up comparing sampler instances).
* Single parameter set (128s, n = 16); `γ`-general seed distribution; classical adversaries only.
* **About real SHA-256**: these theorems say that no attack that treats the SHA-256 compression
  function as a black box (generic in the compression function) breaks the twelve assumptions
  beyond the stated bounds, and that the MD/truncation/shared-first-block/HMAC/MGF1 structure
  introduces no generic weakness. They say nothing about attacks exploiting the internal structure
  of the real compression function (which is a fixed public function, not a random table, and is
  Davies–Meyer, hence e.g. has computable fixed points), and they are not a standard-model proof.

## 7. Phase 2 (coordinator items 1–5): state

**Blocker.** Phase-2 proof work was to be delegated; every new subagent launch was refused by the
harness ("Concurrent subagent limit reached … 20 … Do not retry"), so only what could be done
directly was done. Four briefs (ITSR numerics + glue; realisers from `Reduction/Gen`,
`Reduction/Open`; Davies–Meyer transfer; paper reading) are ready and unexecuted.

Done in phase 2:
* **Item 5** — `Ideal/Rust.lean`, `Ideal.rust_ideal_security` (axioms standard): (1) the Rust
  `slh_keygen_internal` / `slh_sign_internal` / `slh_verify_internal` compute `byteKeygen` /
  `byteSign` / `byteVerify` at `Link.prims` (first conjunct of `E2E.rust_security`); (2)
  `bytesAlg` at `primsG (liftC realCF)` is that scheme (`bytesAlg_realCF`); (3) about the
  IDEAL-MODEL scheme only: every `ForgerI` with realisers satisfying
  `R.Le (2^90) (2^81) (2^64) (2^20)` has `sufI ≤ εI + 2^-31`. Realisers and `εI` remain
  hypotheses of conjunct (3).
* **Item 2, repeated randomizers (checked against `Games/Itsr.lean`, not a new theorem).** The
  proof of `itsr_le` never uses freshness or distinctness of the target randomizers. Every
  compression cell first read by a "marked" call — all of the adversary's own calls and two calls
  per hash of the final check — is one coordinate of a log whose digests are dominated by `n`
  i.i.d. uniform digests (`prT_tape_le_marked`); a win exhibits a logged digest covered by OTHER
  logged digests; `reuseSum h a k n` union-bounds over every coordinate as the covered one and
  every assignment of coverers among all `n` coordinates, not only the actual targets. A repeated
  `R` (probability ≈ 1/2 at `qs = 2^64`) therefore needs no separate term: digests the adversary
  computes for a revealed `R` are coordinates like any other, and adaptivity only changes WHICH
  inputs are evaluated. The price is that the adversary's `q` evaluated digests count as potential
  coverers: the bound is the non-adaptive coverage bound with `q + 2(qs+1)` "targets", so it is
  loose when `q ≫ qs` and does not have the `weightedTargetCoverBound … (qs/|Y|)` shape of the
  classical ROM proof. The factor 2 comes from the missing domain separation of the inner and
  outer SHA-256 calls of `H_msg` (a 20-byte message ending in `0^4` makes an inner input of outer
  form) and is an artefact of the proof (removable with one more "fresh value equals already
  fixed bytes" bad event, `≈ Q²/2^256`); at `q = qs = 2^64` it changes `n` from `2^65` to
  `≈ 2^65.6`.
  **Not proved:** any numeric value of `reuseSum`. Unverified estimates (`reuseSum ≤
  n·2^{-ak}·Σ_r S(k,r)(n/2^h)^r`): `≈ 2^-57` at `q = qs = 2^64`; `≈ 2^-111` at `n ≈ 2^60`;
  `≈ 2^-151` at `n ≈ 2^40`. The twelfth realiser glue (`hI` from `itsr_bound_128s`) is not written.
* **Item 4, reading.** Only the ePrint abstract pages were read.
  2026/2624 (Guo, Cheng, Preneel, Wang): forgery attacks on SHA-256-based LMS exploiting the
  chopped Merkle–Damgård structure, and ideal-cipher proofs for additive-Davies–Meyer abstractions,
  with security `≈ 256 − log₂ B̂` bits (M32) and `min{192 − log₂ Γ̂, 256 − log₂ B̂}` (M24), `B̂` the
  number of SHA-256 blocks processed: i.e. a loss governed by the 256-bit chaining value, the same
  kind of term as our `(blocks)²/2^256` and `q·(blocks)/2^256` terms. For 128s (n = 16, output
  half the chaining value) these terms are far below `q/2^128`; the full paper was not read, so
  whether it contains further ideal-cipher-specific terms relevant to our games is unverified.
  2022/1061 (Perlner, Kelsey, Cooper): forgery against category-5 SPHINCS+-SHA-256 via failure of
  multi-target second-preimage resistance on the WOTS+ public-key compression (Antonov's
  technique), ≈ 40 bits lost. In our bounds this is the internal-chaining-value term of the
  multi-block TCR theorem (`tcr_ideal_multi_le`: the adversary hitting a hidden intermediate
  chaining value of some target, `≈ q·(targets·blocks)/|St|`, and `18·Q²/|St|`): with `|St| = 2^256`
  it is negligible against `2^-128` (n = 16; `tcrLen_bound_128s`, `tcrK_bound_128s` are the
  theorems), but it would be the dominant term against a `2^-256` target (n = 32), which is why
  FIPS 205 uses SHA-512 there. No ideal-cipher theorem was proved; see §1 for what changes.

Not done (items 1, 3, and the proofs of 2 and 4):
* **Item 1.** The eleven `Realizes…` hypotheses are still open; `Reduction/Gen`, `Reduction/Open`
  were not examined. What a discharge needs, per adversary `B` of the linear headline, from the
  Reduction side (names free): (N1) an open program `B_open A` over
  `unifSpec + (gameSpec + HSpec prims.core)` — `HSpec` = one query per `Thash` / `PRF` / `PRFmsg` /
  `Hmsg` evaluation — for each phase of `B A`, defined WITHOUT reference to the hash fields of
  `prims` (so that it is the same term for `primsG c` for all `c`), with
  `simulateQ (answer HSpec by prims) (B_open A) = B A` (per phase); (N2) the same for a forger that
  is itself an open program (the forger's own hash oracle forwarded), i.e. `B_open` natural in the
  forger's extra oracle; (N3) `IsQueryBoundP` bounds for the `HSpec` queries by arity, and for
  game queries; (N4) first phases issue no `HSpec` query. On the `Ideal` side the remaining step
  is generic: replace each `HSpec` query by its Merkle–Damgård program of compression queries
  (`primsG_Thash_shape`, `msgPrf_shape`, `hmsg_shape`; `2 + (22+16n+8)/64 ≤ 12` compression
  queries per `Thash` call).
* **Item 3.** No refined theorem. Assessment: the per-step lemmas already charge only fresh cells
  (`prEvent_routeRO_bad_le`, `potential_le_of_step`), so a version with the hypothesis "on every
  run of phase two at most `F` new row cells are created" in place of `ForgeBound q₂` is within
  reach, but that hypothesis is semantic and would have to be proved for each reduction adversary
  (its re-evaluations hit cells created before the reveal) — the same work as realisability. The
  cheaper route is the answer-storing reduction adversaries: with post-seed own hashing
  `≈ qs + 3929` hash calls (≤ 12 compression calls each) the existing theorems give
  `Qc ≈ q + 12·(qs + 3929)`, i.e. `Qc < 2^68` at `q = qs = 2^64` and, by
  `suf_ideal_bound_numeric`, a bound of order `66·2^68/2^128 ≈ 2^-54` plus `εI` (this evaluation is
  not yet a stated theorem; `suf_ideal_bound_2_65` gives `2^-56` at `Qc = 2^65`); with the
  memoising `bTcrArM` (`≈ qs·2^21` hash calls) the proved value stays `εI + 2^-31`.
  Closed numeric headlines for `(q, qs) ∈ {(2^40, 2^20), (2^60, 2^40), (2^64, 2^64)}` are not
  stated.
* **Item 4.** No ideal-cipher theorem. Planned route (unexecuted): simulator turning an
  ideal-cipher adversary into a random-function adversary (forward query `(m, c) ↦ g(c,m) ⊟ c`;
  inverse query `(m, z) ↦` fresh uniform `c`, recorded), transfer
  `Adv_IC(A) ≤ Adv_RF(sim A) + O((q_f + q_b + Q)²)/2^256` (permutation switching; an inverse answer
  is a fresh uniform chaining value, so the cell it defines meets a cell read by the challenger
  only with probability `≈ 2^-256` each), and the instantiation lemma
  `realCF (c, m) = c ⊞ E_real m c` with `E_real m` a permutation (invertibility of `round256`).

## 8. Phase 2, second pass (done directly; delegation still unavailable)

New modules `Ideal/Inst/ItsrNumeric.lean`, `Ideal/ComposeItsr.lean`, `Ideal/ComposeNumeric.lean`
(in `Ideal.lean`; axioms standard; no `sorry`).

* **ITSR numerics (proved).** `reuseSum_le_prod : reuseSum h a k n ≤ n·(2^-a)^k·∏_{i<k}(i + n/2^h)`
  (assignments built one coordinate at a time; an upper bound, looser than the Stirling-number
  form). At (63, 12, 14): `reuseSum_63_12_14_le_big` (`n ≤ 7·2^63` ⇒ `≤ 2^-50`),
  `reuseSum_63_12_14_le_small` (`n ≤ 2^m ≤ 2^63`, `2m + 37 + c ≤ 231` ⇒ `≤ 2^-c`), and
  `reuseSum_q64_qs64 ≤ 2^-50`, `reuseSum_q60_qs40 ≤ 2^-72`, `reuseSum_q40_qs20 ≤ 2^-112`
  (`n = q + 2(qs+1)`). The earlier hand estimates `2^-111`, `2^-151` for the smaller points were
  wrong (the `r ≥ 2` Stirling terms dominate); the proved values supersede them.
* **Twelfth realiser.** `RealizesItsr`, `cfAvg_itsr_le`, `itsrSufI_le` (discharges `hI` of
  `suf_ideal_bound`), `itsrSufI_le_2_64 : itsrSufI ≤ 2^-50 + 2^-86` (messages ≤ 2^26 bytes).
* **Closed headlines** (uniform seed, SUF; conditional on `SufRealizers` + `RealizesItsr` with the
  stated parameters; `N = 2^81`, messages ≤ 2^20 blocks):

  | (q, qs) | realisers' own queries `Qc` | theorem | bound |
  |---|---|---|---|
  | (2^64, 2^64) | `2^90` (memoising `bTcrArM`, ≈ qs·2^21 hash calls) | `suf_closed_2_64_memo` | `2^-50 + 2^-86 + 2^-31` |
  | (2^64, 2^64) | `2^68` (answer-storing, ≈ q + 12(qs+3929)) | `suf_closed_2_64_store` | `2^-50 + 2^-86 + 2^-53` |
  | (2^60, 2^40) | `2^61` | `suf_closed_2_60_2_40` | `2^-72 + 2^-133 + 2^-60` |
  | (2^40, 2^20) | `2^41` | `suf_closed_2_40_2_20` | `2^-112 + 2^-173 + 2^-79` |

  First two summands: ITSR (`reuseSum`, its `Q²/2^256` term); last: the other eleven games
  (`suf_ideal_bound_2_68` is the answer-storing corollary on its own: `εI + 2^-53`). In the last
  row `2^-79` is the structural term `polyP/2^256 ≈ 36·(22·2^81)²/2^256` (challenger-side
  chaining-value collisions over the whole key structure, from the `18·Q²` of T_len/T_k), not a
  `q/2^128` term. The `Qc` values for the two smaller points assume answer-storing adversaries.
* **Repeated randomizers**: explanation now in the docstring of `Itsr.itsr_le`. Comparison with
  `quantum/PQ/QROM/ExactItsr4.lean` (header read only): that proof re-randomises a row at every
  issuance and obtains the covering probability of the `qs` target digests alone (plus a
  reprogramming term), with no randomizer-collision term; ours has no collision term either but
  pays by counting the adversary's `q` digests as potential coverers (`n = q + 2(qs+1)`).
* **Not done in this pass:** removing the `2(qs+1)` artefact; item 2 (reading `Reduction/Gen`,
  `Reduction/Open`; N1–N4 as exact Lean statements; any `Realizes*` discharge; the generic
  hash-query → compression-query step); item 4 (ideal-cipher transfer; full reading of the two
  papers). §7's descriptions of these remain the current state.
