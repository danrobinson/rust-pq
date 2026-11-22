# A direct ideal-compression proof for SLH-DSA-SHA2-128s: design plan

Scope: replace `suf_ideal_closed_tight8` / `euf_ideal_closed_tight8`
(`security/Ideal/Realize/FinalTight8.lean:431`, `:447`) and their context-string forms
`suf_ideal_pure_closed_tight8` / `euf_ideal_pure_closed_tight8`
(`Ideal/Realize/FinalPureTight8.lean:27`, `:44`) with one direct game-based proof. Note the names:
the brief calls the pure form `suf_ideal_closed_pure_tight8`, but the file names it `suf_ideal_pure_closed_tight8`.
The statement is the same game: `sufI S (optRandU oR) ($ᵗ (Bytes 16))` (`Ideal/Compose.lean:196`),
with the forger hypotheses `hqf hqs hlong hout` as in the existing theorem.

Scripts (exact rational arithmetic, NOT machine-checked), next to this file:
- `direct/direct_bounds.py` (output `direct/direct_bounds.out`): the Lean definitions, transcribed
  and evaluated term by term; the generic-attack floor; the predicted direct bound.
- `direct/tiers.py` (output `direct/tiers.out`): the fallback tiers, and how the bound varies with `qs`.

Points (as in the tight8 numeric theorems `FinalTight8.lean:528–582`): ℓ = 2^26 bytes, so
x = ⌊(ℓ+56)/64⌋ = 2^20 message blocks. P20 = (qf ≤ 2^60, qs ≤ 2^20), P40 = (2^64, 2^40),
P64 = (2^64, 2^64).

---------------------------------------------------------------------------------------------

## 1. Where the remaining loss comes from

### 1.1 The definitions evaluated (transcribed exactly)

| symbol | definition | file:line |
|---|---|---|
| `QlinT8 qf qs ℓ` | `27·qf + qs·(16771392 + 14·x) + 29487855 + 13·x` | `Ideal/Realize/FinalTight8.lean:303` |
| `polyP8 Qc N qs ℓ` | `polyP7 Qc N qs ℓ + 3·(Qc + 40·N + 1)` | `FinalTight8.lean:179` |
| `polyP7` | `polyP + 14·(20·N + 1)` | `Ideal/Realize/FinalTight7.lean:203` |
| `polyP` | `(Qc+N)² + (Qc + qs(ℓ+1) + 2)² + 18(2Qc+22N+21)² + 18(2Qc+22N+9)² + 78Qc + 1433N + 47` | `Ideal/Compose128.lean:319` |
| `QcAll` | `qf + (qs+1)(2^25 + 2x)` | `Ideal/Realize/FinalCore.lean:33` |
| `NAll` | `max 2^81 (17920 + 182784·qs)` | `FinalCore.lean:37`, `qOPrf_128s` `PrfReal.lean:328` |
| `ellB ℓ` | `⌊(ℓ+63)/64⌋` (`polyP8` gets `ellB ℓ` in the `ℓ` slot) | `FinalCore.lean:40` |
| `epsItsrF qP cP q qc Lc qs ℓ` | `reuseSum 63 12 14 (qP+cP+2(qs+1)) + (q + qc·Lc + (qs+1)(x+3))²/2^256` | `Ideal/ComposeFinal.lean:77` |
| headline arguments | `qP = qf, cP = 2qs, q = qf, qc = itsrQc qs = 269824 + 2007386·qs, Lc = itsrLc ℓ = max 11 (x+1)` | `FinalTight8.lean:439`, `Realize/Itsr.lean:42,44,51` |
| `reuseSum h a k n` | `Σ_{(j,c) : c i ≠ j} 2^{-h·|im c|}·2^{-a·k}`, closed form `n·Σ_r S(k,r)(n−1)_r 2^{-hr}·2^{-ak}` | `Ideal/Inst/Itsr128.lean:139` |
| `reuseSum_le_prod` | `≤ n·2^{-ak}·∏_{i<k}(i + n/2^h)` (the form the Lean numerics use) | `Ideal/Inst/ItsrNumeric.lean` |

### 1.2 Term by term (log₂, unrounded, at the caps; `direct_bounds.out`)

| term | P20 | P40 | P64 | class |
|---|---|---|---|---|
| I.a ITSR `reuseSum` (prod form; Stirling form in brackets) | −77.91 (−95.52) | −63.75 (−69.73) | −45.69 (−47.13) | **artefact**: `n = qf + 4qs + 2` counts every forger `cB` query and every signer digest twice as a potential *coverer* (L7, L8); the prod form costs 1.4–18 bits (L9) |
| I.b ITSR quadratic | −132.91 | −94.13 | −46.13 | **artefact**: `qc·Lc` charges all `2·10^6·qs` hash calls of the realiser at 2^20+1 blocks (L11) |
| II `27·qf` | **−63.25** | **−59.25** | −59.25 | **artefact of composition** (L6): each forger query is charged once in each of 27 games (PRF 1, PRF_msg 2, FORS TCR 3, class TCR 4, SM-UD 14, PRE 2, WOTS TCR 1). Intrinsic part ≈ 1·qf (key search), ≤ 2·qf provable (§2.5) |
| II `qs·16771392` (re-signing hashing) | −84.00 | −64.00 | **−40.00** | **artefact** (L4): each reduction adversary re-signs every query itself and is charged 2^-128 per compression |
| II `qs·14·x` (message blocks) | −84.19 | −64.19 | **−40.19** | **artefact** (L4): `H_msg`/`PRF_msg` chains of the reduction's own signing, charged in 14 games |
| II one-off `29487855 + 13x` | −102.6 | −102.6 | −102.6 | artefact (key regeneration and the WOTS answer extraction) |
| III `polyP8/2^256` | −79.91 | −79.91 | −70.48 | **artefact** (L12): `18(2Qc+22N)²` = internal `T_len`/`T_k` chaining values over the `N ≥ 2^81` per-game targets, squared |
| **total (current)** | **−63.25** | **−59.15** | **−39.08** | proved points: `2^-77+2^-132+2^-63`, `2^-63+2^-94+2^-59`, `2^-45+2^-46+2^-39` |

At P64 the bound is ≈ 50 % `qs·16771392` and ≈ 45 % `qs·14x`. Both come from charging the
signing oracle's hashing to the adversary, which happens because every reduction re-simulates
the signer. Neither has a matching attack. At P20/P40 the bound is the factor 27 on `qf`.

### 1.3 Intrinsic part, best possible bound, and matching attacks

Generic attacks (`direct_bounds.out`, "generic"):

* **SK.seed exhaustive search**: guess `k`, make one compression `(cv, ADRS_prf ‖ k ‖ pad)` for
  an address whose FORS secret was revealed in a signature, and compare `out16` with that secret.
  Each query succeeds with probability 2^-128, and success recovers the whole key. This gives
  `qf/2^128`: 2^-68, 2^-64, 2^-64. (Every other single-target 128-bit event — a preimage of a
  revealed chain value or node — is also ≈ 2^-128 per query. None of them yields a forgery more
  cheaply.) The tweak (ADRS in the first block after the PK.seed midstate) makes every query
  relevant to exactly one honest value, so there is **no** multi-target amplification across the
  2^64·2·10^6 hash values of the signatures.
* **FORS few-time forgery (ITSR)**: `qf·p(qs)`, with
  `p(qs) = Σ_γ C(qs,γ)2^{-63γ}(1−2^{-63})^{qs−γ}(1−(1−2^{-12})^γ)^{14}`. This gives 2^-151, 2^-127,
  2^-69.75. (A real attack spends ≥ 3 compressions per candidate digest, so this slightly
  over-estimates the attack.)
* Chaining-value collisions (2^-256 scale): no attack at this size matters.

**Best one could hope for**: P20 2^-68.0, P40 2^-64.0, P64 2^-63.97. The current bound is 4.8, 4.9
and 24.9 bits above that.

---------------------------------------------------------------------------------------------

## 2. The direct proof architecture

### 2.0 Idea in one paragraph

Run the real SUF experiment over **one** lazily sampled compression table shared by the forger,
the signer and the verifier. Tag each cell with who read it first (Forger / Honest / Verify) and
with its SHA-256 parse class. Prove a **deterministic extraction** lemma: on the final table,
"strong forgery accepted" implies one of four events. (Coll) a 256-bit chaining event.
(Hit) a cell first read by the forger or the verifier, at tweak `A`, with input ≠ honest input
at `A` and `out16` = honest value at `A`. (Guess) a forger cell equal to an honest cell whose
input was still hidden when the forger made it, or a forged signature value equal to an
unrevealed honest value. (Cover) the forgery's `H_msg` digest is covered by the target digests.
Then bound P[Coll ∨ Hit ∨ Guess] by **one** potential argument in which each forger query is
charged once, according to its parse class, never once per game. Cover gets a separate tape
argument. No standard-model reduction, no re-simulation of the signer, no per-game hidden-prefix
hop: PK.seed is public from the start, so the midstate `cv = g(IV, sb PK.seed)` is just a public
cell.

### 2.1 Games

```
G0  sufI S oR = cfAvg_g Pr[ SUFexp_g ]                      -- the statement (Compose.lean:196)
G1  = Pr[ prfRealI (AprfS S oR) ]                           -- exact: entry lemma (§4, D0)
      one closed program over the table: PRF-game key k = SK.seed; AprfS samples SK.prf,
      PK.seed, runs keygen, the forger, the signing oracle and sufCheck, with every
      Thash / H_msg / PRF_msg / PRF evaluation as explicit compression calls
G2  = G1 run over the lazy table (romImpl), with the tagged logging handler      -- exact
      state: cache κ : St×Blk ⇀ St, first-reader tag τ : dom κ → {F, H, V}, time stamps,
      revealed set Rev (values that occur in a signing answer or in pk)
G3  = G2 followed by the **completion** program: evaluate the whole honest key structure
      (`Reduction.honestCalls`, ≈ 2^80.8 calls) on the same lazy table, tag H     -- exact
      (the completion reads cells only; it changes no output; it only makes "honest value at A"
      a function of the final cache for every A)
Win(G3) ⇒ Coll ∨ Hit ∨ Guess ∨ Cover                          -- deterministic (D3, D4)
Pr[Coll ∨ Hit ∨ Guess] ≤ (2·qf + C0)/2^128 + (Q+2)²/2^257       -- one potential argument (D5, D6)
Pr[Cover ∧ ¬Coll] ≤ (qf+1)·cov(qs·(1+qf/2^128))                  -- tape argument (D7)
```

There is no "identical-until-bad" chain of hops with different games. All bad events live in the
same probability space (G3), so their probabilities add **per query**, not per game. This is what
removes the factor 27 and the re-signing charge.

### 2.2 Invariant on the lazy table

`Inv(κ, τ)` after every step, unless `Coll` has fired:

1. **No 256-bit coincidence**: the values of κ are pairwise distinct, differ from `IV`, and no value
   of κ is the chaining input of a cell that was in κ before that value was sampled (no
   back-link). In addition, no value equals `cv`, except the value of the cell `(IV, sb PK.seed)`.
2. **Unique parse** (follows from 1): every cell `(c, b)` with `c ∈ {IV} ∪ vals κ` has a unique
   *rooted chain* `IV → … → c`, and hence a unique role (§2.3). A cell whose `c` is not rooted
   when it is created stays unrooted forever (by 1).
3. **One honest cell per tweak**: for every tweak `A` of the key structure the honest
   computation reads exactly one *final cell* `fin(A)` (the cell whose `out16` is the honest
   value `y_A`), and one *input* `x_A`. (This needs address injectivity:
   `Concrete.keySeparated_sha2Primitives`, the distinctness of `constructionAddresses` used by
   `Reduction/TCR.lean`, and `tblocks_injective` `Sha/Shape.lean:282`.)
4. **Hidden set** `Hid = {honest values not in Rev and not computable from Rev by public cells}`.
   Concretely: FORS secrets of unopened leaves, WOTS chain values below the lowest revealed
   position of their chain, unrevealed tree nodes, SK.seed, SK.prf, and the two HMAC key midstates.

### 2.3 How the SHA-256 structure is handled (parse classes)

Parse of a forger cell `(c, b)` (disjointness from `Sha/*` shape lemmas):

| class | shape | 128-bit charge per fresh forger cell | why |
|---|---|---|---|
| `Kprf` | `c = IV`, `b = ikey k` or `okey k` (bytes 16..63 all 0x36 / all 0x5c) | 2^-128 (Guess `k = SK.prf`) | `HmacShape.lean`; one candidate per block |
| `Kseed` | `c = cv`, `b = blk128 a k` at a PRF (SK-type) address | 2^-128 (Guess `k = SK.seed`) | `PRF_eq_Thash`, `key_of_tblocks_eq_blk128` (`Inst/SkPrf128Fine.lean`), `sb128_ne_blk128` (`Inst/SkPrf128.lean:83`) |
| `Th1(A)` | `c = cv`, `b = (tblocks A xs).1` with `|xs| ∈ {1,2}` (F, H: one block after the midstate, ADRSc in bytes 0..21) | 2·2^-128 (Guess `xs = x_A` while hidden; Hit `out16 = y_A`, `xs ≠ x_A`) | `thash_shape`; `(22+16n+8)/64 = 0` blocks after the first for n ≤ 2 |
| `ThF(A)` | `c = cv`, first block of `T_len` (n=35, 10 blocks) or `T_k` (n=14, 4 blocks) | 2^-128 (Guess, first 2.6 inputs hidden) | output is a CV; no 128-bit Hit at a first block |
| `ThL(A)` | `c` rooted at depth 9 (resp. 3) of a `T_len` (`T_k`) chain at `A`, `b` = a valid last block | 2^-128 (Hit) | only the first block carries the ADRS; the last cell's *rooted* chaining value identifies `A` (Inv 2). A last block whose `c` is not yet rooted can only become useful by a back-link (Coll) |
| `HmF` | `c` rooted as `g(IV, R ‖ PK.seed ‖ X)`, `b = cB` (`oblocksH_eq`) | Cover only (§2.4) | `HmsgShape.lean` |
| other | anything else (H_msg inner blocks, HMAC message blocks, `(IV, sb PK.seed)`, invalid addresses, unrooted cells) | 0 | Coll only |

The classes are pairwise disjoint (`c = IV` vs `c = cv` vs rooted depth ≥ 2; PRF vs Thash address
types; padding byte 0x80 at byte `22+16n` vs HMAC 0x36/0x5c; ADRS type byte). So
**per forger query the charge is the maximum over classes, 2·2^-128, not the sum over games.**

Multi-block intermediate chaining values. `T_len`/`T_k` intermediate CVs (the
Antonov/Perlner–Kelsey multi-target vector) matter only as 256-bit events: a forger cell's
output equal to an honest intermediate CV is a Coll. So is a back-link that makes an earlier
"last block" query rooted. `H_msg`: inner-digest collisions are Coll. The non-separation of
inner and outer (L8: a 20-byte message ending in 0^4 has inner last block = `cB`) affects only
the full-log Cover tier (§2.4, tier B), not the target-only tier. HMAC: the two key midstates
`g(IV, ikey SK.prf)`, `g(IV, okey SK.prf)` are hidden CVs; hitting them is Coll, guessing SK.prf is `Kprf`.

### 2.4 ITSR / FORS re-use (Cover)

FORS re-use costs **no** 2^-128 charge in this design. The honest structure is deterministic, so a
FORS key signing 2, 3, … messages just reveals more leaves of the same trees. The only price is
the coverage event:

`Cover := ∃ candidate cell C of class HmF, first read by F or V, not a target cell, whose digest's
FORS key and 14 indices are covered by digests of target cells` (target cell = the `HmF` cell
of a signing answer).

* **Tier C (target-only coverers, the goal).** Union bound over (candidate cell, map of the 14
  indices to target *ordinals*). A fresh target cell's digest is drawn after the decision that it
  is a target (the signer's `R` is fresh: `R = out16` of an HMAC final cell keyed by a hidden CV),
  so target colours are *predictable* and the digests are i.i.d. uniform. A target cell that the
  forger had already queried (it guessed `R`, `M`) makes the colouring non-predictable. Charge it
  as a coverer with weight `P[forger cell D becomes a target] ≤ qs/2^128`: `R_j` is independent of
  every `cB`-cell digest. The effective number of coverers is `qs·(1 + qf/2^128)`.
  `Cover ≤ (qf+1)·2^{-168}·Σ_{r=1}^{14} S(14,r)·(qs(1+qf/2^128))^r·2^{-63r}`
  = 2^-151, 2^-127, **2^-69.73** — the intrinsic `qf·p(qs)` up to 0.02 bit.
* **Tier B (fallback; reuses `Games/ItsrTape.lean` unchanged).** Log every `cB` cell first read
  by F, by the signer's outer-final call, or by V, and use `prT_tape_le_marked` + `prT_tape_cov_le`
  (`Inst/Itsr128.lean`) with `n = qf + qs + 2` (each cell counted once). This needs one extra
  2^-256 event so that a signer's inner-final `cB` cell is never a candidate or target:
  `≤ Q·qs/2^256`. Otherwise `n = qf + 2qs + 2`. Result: P64 **2^-60.83** (Stirling form; 2^-57.25
  with `reuseSum_le_prod`).

### 2.5 Hit and Guess: where "2" comes from, and why not 1

For a `Th1(A)` query whose input position is hidden but whose output `y_A` is revealed (the WOTS
position just below the revealed one), both `xs = x_A` (prob 2^-128) and `out16 = y_A`,
`xs ≠ x_A` (prob 2^-128) give a preimage of `y_A`. A preimage of an *image point* of a random
function costs `2/2^128` per query, and that is tight for the preimage event. So the per-query
argument cannot give a coefficient below 2. A coefficient of 1 would need an argument that a
single preimage does not yield a forgery (WOTS checksum, FORS needing 14 leaves): a global
argument, not attempted here. So expect `2·qf`, one bit above the key-search attack.

**Hit, either order.** If the honest final cell `fin(A)` is sampled *after* a forger cell at
`A` (during signing or during completion), the honest sample collides with that cell's `out16`
with probability `(#forger cells at A)/2^128`. Summed over all honest samples this is
`≤ qf/2^128` (one honest cell per tweak, Inv 3). Use the potential
`Φ = 2^-128·#{forger cells at tweaks A with fin(A) not yet sampled}` (`potential_le_of_step`,
`Core/HiddenInput.lean:347`). This is the same 2^-128 as the forger-after-honest order; a forger
cell pays it once, in whichever order.

**Guess (the deferral).** When a forger cell at `A` is made while `x_A ∈ Hid`, `x_A` is uniform
given the forger's view, up to the ≤ `qf` values excluded by its own failed queries.
Tool: a **swap lemma** on the eager table. For a hidden honest value `u = out16(g C)` and a
candidate `u'`, the involution that swaps the 128-bit prefix of `g C` between `u` and `u'` and
swaps the cells keyed by `u` and by `u'` at the next tweak is measure-preserving. It fixes the
forger's view up to time `t` unless the forger read `C` or one of the swapped cells, or `u` was
revealed before `t`. Averaging over `u'` gives `P[forger cell at time t keyed by x_A] ≤ 2^-128`.
Alternative: a generalisation of `run_romImpl_patch` / `prT_run_romImpl_patch_le`
(`Core/HiddenInput.lean:170`) from private-row cells to cells keyed by a hidden value. The
standard-model analogue of the swap argument is the fibre-preserving permutation of
`Reduction/ForsTight.lean`.

**Verification and forged values.** Cells first read by V are at most `verifyHashes = 3928`
final cells (`Reduction/TcrMemo.lean:704`; the extra `T_len`/`T_k` blocks are not final cells),
each a potential Hit. The forged signature has `14 + 7·35 = 259` values that can equal hidden
honest values (HiddenEq, 2^-128 each by the same swap lemma). Seed/IV events: a constant. So
`C0 = 3928 + 259 + 64`.

### 2.6 EUF and SUF together

Deterministic extraction (D3), on the final table and over the abstract tweakable hash:

1. **Fresh pair** `(M*, R*)` not among the signed pairs: `Reduction.classify` (`Games.lean:209`)
   gives `itsr` (→ Cover), `openpre` (forged FORS secret hits an unopened leaf image → it equals
   the hidden secret (Guess/HiddenEq) or it is a collision at the leaf tweak (Hit)), `wots`
   (`Reduction/WotsFinal.lean:181 win_cases`: a preimage of a revealed chain value at position
   b−1 — walk down the verifier's chain to the first matching position: Hit, or HiddenEq at the
   bottom — or a collision above b: Hit), or `tcr` (`col_collision_of_classify`,
   `Reduction/TCR.lean:922`: a verification call colliding with an honest call at the same
   tweak on a different input: Hit).
2. **Same pair, different signature** (SUF only): `sameRandomizer_collision`
   (`Reduction/SufCollision.lean:421`; uses `suf_chain_collision` `:82` and
   `suf_climb_collision` `:154`) gives a WOTS layer with the same chain ends and a different message
   (→ as in `wots`) or a verification/honest collision at one tweak (Hit).

So SUF costs nothing extra. EUF is the special case with no same-pair branch.
`verifyCalls_idealSign_subset` (`TCR.lean:2075`) makes the honest calls of a signing answer a
subset of the honest structure, which is what lets the completion (G3) serve as the reference.

**Lift** (D4): "verification call at `A` with input ≠ `x_A` and output = `y_A`" ⇒ (¬Coll) its
final cell is a cell with that property. That cell was first read by F (charged in its class) or
by V (in `C0`), never by H (an honest cell at `A` has input `x_A`; Inv 3). Tool: the
Merkle–Damgård walk-back `md_inj` (`Games/Itsr.lean:94`) and `chainVal`
(`Games/TcrMultiBasic.lean`).

### 2.7 The quadratic term

`Coll ≤ (Q+2)²/2^257`, with `Q` = all distinct cells read in G3, which includes the signer's cells:
`Q ≤ qf + 2.92·10^5 + qs·(2.22·10^6 + 2x) + 4·10^3 + x` plus the completion (≈ 2^81.6 cells,
negligible next to 2^86). Values: P20 2^-137, P40 2^-128.3, **P64 2^-84.9**. Charging the
signer's cells is harmless at 2^-256. Restricting the term to `(qf + qs·c)²` with the signer's
`c ≈ 4.3·10^6` is what this gives; nothing smaller is needed. The current leg III (L12,
`18(2Qc+22N)²`, 2^-70.5 at P64) disappears: there are no per-game target lists.

### 2.8 Comparison with the literature

* SPHINCS+ round-3.1 submission §9.3.4 (read from the local copy `scratchpad/txt/sphincs-r3.1.txt`,
  lines 2240–2290). Classical generic estimate `10(q_hash+1)/2^{8n} + ITSR(H_msg; q_hash)`, with
  ITSR in the ROM `q·Σ_γ …` (the `p(qs)` above). That analysis rests on the earlier WOTS
  argument the submission itself marks flawed.
* Hülsing–Kudinov, ePrint 2022/346 (only the abstract page was readable here: the PDF returned
  HTTP 403; constants below are recalled, not re-read). It recovers a tight bound
  `PRF + PRF_msg + ITSR + SM-TCR(F,H,T) + SM-DSPR/UD-type terms`, with a factor-`w` loss in
  WOTS-TW. Barbosa et al., ePrint 2024/910 (EasyCrypt), fix the WOTS-TW step with
  `(w−2)·SM-UD + SM-PRE + SM-TCR`. Their ROM instantiation is `≈ c·q/2^{8n} + q·p(qs)` with `c`
  of the order of our 27 (`Reduction/HeadlineFinal.lean` has the same structure). All of these:
  (i) model the tweakable hash as one random oracle (no Merkle–Damgård, no midstate, no
  multi-block intermediate CVs, no HMAC); (ii) let the challenger answer signing queries, so `qs`
  enters only through `p(qs)`; (iii) compose per-property bounds, so the constant is a sum.
  The direct design keeps (ii), replaces (i) by §2.3, and replaces the sum in (iii) by a
  per-query maximum, giving `2·q/2^{8n} + q·p(qs) + Q²/2^{256}`. That is better than any
  composed bound and matches the classical intuition behind the submission's "generic attack"
  estimates.

---------------------------------------------------------------------------------------------

## 3. Predicted bound

```
sufI S (optRandU oR) ($ᵗ (Bytes 16))  ≤  epsDirect qf qs ℓ :=
    (2·qf + 4251) / 2^128
  + (qf + 1) · 2^-168 · Σ_{r=1}^{14} S(14,r) · (qs + ⌈qf·qs/2^128⌉)^r / 2^(63 r)      -- tier C
  + (Qd qf qs ℓ + 2)^2 / 2^257
Qd qf qs ℓ = qf + 292353 + qs·(2222444 + 2x) + 3997 + x + 2^82                   -- (+ completion)
```
(same for `eufI`; the pure interface at `ℓ + 257` through `sufP_le_sufI`, `PureForger.lean`).

| | P20 | P40 | P64 |
|---|---|---|---|
| current (proved, sum) | 2^-62.99 | 2^-58.9 | 2^-38.7 |
| current (unrounded formula) | 2^-63.25 | 2^-59.15 | 2^-39.08 |
| **direct, tier C** | **2^-67.00** | **2^-63.00** | **2^-62.99** (2^-63.00 + 2^-69.73 + 2^-84.9) |
| direct, tier B′ (ItsrTape, `n=qf+qs+2`, Stirling form) | 2^-67.00 | 2^-62.99 | 2^-60.54 |
| direct, tier A′ (same, `reuseSum_le_prod`) | 2^-67.00 | 2^-62.33 | 2^-57.22 |
| direct, tier A (`n=qf+2qs+2`, prod form) | 2^-67.00 | 2^-62.33 | 2^-52.57 |
| generic floor | 2^-68.00 | 2^-64.00 | 2^-63.97 |
| gain (tier C over current) | 3.8 bits | 3.9 bits | 23.9 bits |
| gap left (tier C vs floor) | 1.0 | 1.0 | 1.0 |

Stated point forms one could prove: P20 `2^-67 + 2^-150 + 2^-136`, P40 `2^-63 + 2^-126 + 2^-128`,
P64 `2^-63 + 2^-69 + 2^-84`. Sensitivity in `tiers.out`: tier B′ equals tier C to 0.1 bit up to
`qs = 2^62`; the target-only tape matters only near `qs ≈ 2^64` (2.5 bits there). Both degrade
past `qs ≈ 2^65` (FORS re-use becomes real: at `qs = 2^66` the floor itself is 2^-52.7).

---------------------------------------------------------------------------------------------

## 4. Reuse map

**Reused as is.**
* Statement objects: `ForgerI`, `sufI`, `eufI`, `cfAvg*`, `cfAdvantage` (`Ideal/Compose.lean`);
  `optRandU`; `ForgerP`, `sufP_le_sufI`, `eufP_le_eufI`, `toI_*` (`Realize/PureForger.lean`) for
  the context-string corollaries; the Rust/API wrappers pattern of `RustFinalClosedTight8.lean`
  (if that file is deleted, the pattern is the same as `RustFinalClosed.lean`).
* Entry point (G0 = G1): `Reduction.prfRealPr_bPrfWC` (`Reduction/Linear.lean:367`), the SUF and
  `expW` link used at `Linear.lean:741`, and the PRF realiser `Prf.realizesPrfSuf` / `…Euf`
  (`Realize/PrfReal.lean`; program `AprfS = chainP (bPrfWCOpenP …)`, `PrfPort.lean`, transport
  `PrfTr.lean`, `Transport/*`). This gives, at every table, the SUF experiment as an explicit
  compression program, with the core transport (the old blocker) already solved. Also
  `Ideal/Games/PrfDefs.lean` (`prfF`, `prfSchemeI`). The PRF game is used **only** for its real
  side, as a wrapper: no PRF bound is charged.
* Counts: `Realize/Chain.lean` (`thashC`, `hmsgC`, `prfMsgC`, `chainImpl`, `thashCost`),
  `Reduction/Lazy/Open.lean` (`keygenHashes`, `signHashes`, `qb_*`), `Reduction/Resources.lean`
  (`signReads_128s`), `Reduction/TcrMemo.lean:704` (`verifyHashes_128s`), `Realize/ForsL5.lean`,
  `WotsL5.lean` (per-arity, long-`Thash` counts) for `Qd`.
* SHA-256 shapes: `Sha/Generic.lean`, `Instantiate.lean` (`liftC_realCF`), `Shape.lean`
  (`thash_shape`, `tblocks_injective:282`, `padL`), `HmsgShape.lean` (`hmsg_shape`, `oblocksH`),
  `HmacShape.lean` (`msgPrf_shape`, `ikey`, `okey`), `Inst/SkPrf128.lean`
  (`sb128_ne_blk128:83`), `Inst/SkPrf128Fine.lean` (`key_of_tblocks_eq_blk128`),
  `Ideal.sb128_not_keyBlk`, `tblocks_not_keyBlk` (PRF_msg marking), `ComposeFinal.lean:341`
  (`tblocks_one_ne_cB`), `Realize/WotsUdFine.lean:82` (`iblocksH_head_ne`, `oblocksH_head_ne`).
* Lazy-table machinery: `Core/LazyLemmas.lean` (`prEvent_bad_le_of_step:37`, `romImpl`),
  `Core/HiddenInput.lean` (`potential_le_of_step:347`, `patch`, `run_romImpl_patch`,
  `prT_run_romImpl_patch_le:170`, `evalDistEq_run_of_intertwine`), `Core/ChainFine.lean`
  (`free_fold:212`, `routeRO_potential_fine:257`, as templates for rooted/unrooted chains),
  `Games/UdFine.lean:83` (`prEvent_bad_le_of_step_ok`), `Games/TcrMultiPhase2.lean:42`
  (`prEvent_bad_le_of_step_cap`).
* ITSR: `Games/ItsrTape.lean` (`prT_tape_le_marked:307`, `prT_tape_bad_le`, `logM`),
  `Games/Itsr.lean` (`md_inj:94`, `covB`), `Inst/Itsr128.lean` (`reuseSum`, `reuseSum_le`,
  `prT_tape_cov_le`, `coveringDigest`), `Inst/ItsrNumeric.lean` (`reuseSum_le_prod`, tier A).
* Deterministic scheme lemmas: `Reduction.classify`, `ForgeryClass` (`Games.lean:130,209`),
  `classify_itsr` (`ITSR.lean:335`), `col_collision_of_classify` (`TCR.lean:922`),
  `col_fors_collision:626`, `col_xmss_collision:708`, `verifyCalls:66`,
  `verifyCalls_idealSign_subset:2075`, `honestCalls`, `sameRandomizer_collision`
  (`SufCollision.lean:421`), `WotsFinal.win_cases:181`, `Concrete.keySeparated_sha2Primitives`,
  VCVio `GeneralScheme.*_pred` (address types ≤ 4).

**Not needed.** The hidden-prefix hop (`Core/HP*`, `HiddenPrefix.lean`): PK.seed is public in
the SUF game. All eleven per-game bounds (`Games/{Tcr*,Ud*,Pre*,Dspr*,Prf*,MsgPrf*}`) and their
realisers, except the PRF realiser used as the entry wrapper. `Compose*.lean`, `Final*Tight*`.

**New.** The tagged lazy handler and the parse classes; the completion; the abstract-hash
extraction (gluing the existing classification lemmas into one total statement with HiddenEq);
the lift to cells; the swap/deferral lemma; the single potential argument; the two-colour tape
(tier C); the Stirling evaluation of `reuseSum` (tier B); the headline.

---------------------------------------------------------------------------------------------

## 5. Work breakdown (dependency order; new directory `security/Ideal/Direct/`)

| # | file | key statement (Lean-like) | lines | main risk |
|---|---|---|---|---|
| M0 | `Direct/Toy.lean` (milestone, §5.1) | see below | 400–700 | the swap lemma on a DAG of hidden values |
| M0b | `Direct/TwoColour.lean` (milestone for tier C) | see below | 300–500 | predictable colouring when a coloured cell may be pre-read |
| D0 | `Direct/Entry.lean` | `sufI S (optRandU oR) ($ᵗ _) = cfAvg fun g => Pr[(skPrfC ..).prfRealExperiment ((AprfS S oR _).inst g)]` and the EUF twin; plus `AprfS = chainP (keygenO >>= runForgerSigO >>= sufCheckO)`, split so that the three phases are visible | 400–700 | kernel/elaborator SHA-256 unfolding (TIGHT §8.1: abstract-bundle lemmas, `kexact`) |
| D1 | `Direct/Tagged.lean` | `tagImpl : QueryImpl (hS_F + hS_H + hS_V) (StateT (Cache × Tag) ProbComp)`; `untag_eq : 𝒟[run tagImpl Xtag] = 𝒟[run romImpl X]` with `X` = the D0 program, F = port queries, H = keygen/sign/PRF-oracle chains, V = sufCheck chains; counts `#F ≤ qf`, `#H ≤ Kc + qs·Sc`, `#V ≤ Vc` | 600–900 | threading tags through `chainP` and the PRF-game wrapper |
| D2 | `Direct/Parse.lean` | `role : Cache → St × Blk → Role` with `Role = Kprf ∣ Kseed ∣ Th1 A ∣ ThF A ∣ ThL A ∣ HmF ∣ Other`; `role_unique (h : ¬Coll κ)`; disjointness lemmas; `honestFin A`, `honestIn A`, `fin_unique` (Inv 3) | 900–1300 | address injectivity over all tweakable-hash calls (from existing `_pred` and `keySeparated` facts) |
| D3 | `Direct/Extract.lean` | `extract (T : Thash) (σs : signed) (h : verify pk M* σ* ∧ (M*,σ*) ∉ Q) : CoverE ∨ (∃ A x, x ≠ honestIn A ∧ T A x = honestVal A ∧ (A,x) ∈ verifyCalls pk M* σ*) ∨ HiddenEqE` over abstract `Thash`, `H_msg` | 800–1200 | gluing `classify`, `win_cases`, `sameRandomizer_collision` into one total statement; the WOTS "walk down to the first match" lemma is new (≈ 300) |
| D4 | `Direct/Lift.lean` | `¬Coll κ → verifyCall at A with input ≠ x_A and value y_A → ∃ cell ∈ κ, role = Th1 A ∨ ThL A, τ cell ∈ {F, V}, out16 = y_A, input ≠ x_A` | 600–900 | MD walk-back for 10-block `T_len` and the cache form of `chainVal` |
| D5 | `Direct/Hide.lean` | `prEvent_guess_le : Pr[Guess] ≤ #F/2^128 + 259/2^128` (swap lemma `swapTbl u u'`, `measurePreserving_swapTbl`, `run_swap_eq_until`) | 1500–2500 | **main risk**: dynamic `Hid` (values revealed later), adaptivity of the tweak `A_t` |
| D6 | `Direct/Bad.lean` | `prEvent_bad_le : Pr[Coll ∨ Hit ∨ Guess] ≤ (2·#F + C0)/2^128 + (Q+2)²/2^257` (`potential_le_of_step` with `Φ = Σ_{F cells at A, fin A unsampled} 2^-128 + 2^-127·[class] + …`) | 1000–1500 | per-class ε inside one potential (generalising `prEvent_bad_le_of_step` to class-dependent ε) |
| D7a | `Direct/CoverB.lean` | `Pr[Cover ∧ ¬Coll] ≤ reuseSum 63 12 14 (qf + qs + 2)` via `prT_tape_le_marked` | 500–800 | the extra 2^-256 event for inner-final `cB` cells |
| D7b | `Direct/Stirling.lean` | `reuseSum 63 12 14 n ≤ n·2^-168·Σ_r S(14,r)·n^r·2^{-63r}` and its evaluation at the points (`reuseSum_le` + `targetCoverBound` closed form; Stirling numbers by a `decide`d recurrence) | 300–500 | VCVio's `targetCoverBound` form |
| D7c | `Direct/CoverC.lean` | `Pr[Cover ∧ ¬Coll ∧ ¬Kprf] ≤ (qf+1)·cov(qs·(1+qf/2^128))` (from M0b) plus `R` freshness (HMAC final cell keyed by a hidden CV) | 900–1400 | pre-read targets; deterministic `opt_rand` (same `(opt_rand, M)` gives the same target cell) |
| D8 | `Direct/Final.lean`, `Direct/FinalPure.lean`, `Direct/Rust.lean` | `suf_ideal_closed_direct S oR hqf hqs hlong hout : sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsDirect qf qs ℓ`, `euf_…`, points `…_direct_2_20/_2_40/_2_64`, pure forms at `ℓ+257` | 500–800 | numerics in `ℝ≥0∞` (pattern of `FinalTight8`) |

Total ≈ 8–12k lines (tier B: drop D7c and M0b, ≈ 7–10k). The per-leg plan of TIGHT §4.2 was
estimated at 8–12k for a P64 result of ≈ 2^-59, capped by ITSR at 2^-45.7 unless L7 is also done.

### 5.1 First milestone (small; falsifies the approach early)

`Direct/Toy.lean`, a generic game over a lazy table `g : St × Blk → St` with a public `cv`:
secret `k`; `m` chains, with `v_{a,0} = out(g(cv, P(a,k)))` and
`v_{a,j+1} = out(g(cv, F(a,j,v_{a,j})))` for `j < w`, with injective, disjoint block maps `P`, `F`.
The adversary has `q` compression queries and adaptive reveal queries `reveal a b` (returns
`v_{a,b}`; several per chain allowed). It wins with `(a, j, x)` such that `j < min revealed(a)` and
the chain from `x` at position `j` reaches `v_{a, w}`.

```
theorem toy_le : Pr[win] ≤ (2*q + 1)/|Y| + (q + m*(w+1) + 2)^2/(2*|St|)
```
The bound must **not** contain `m·q`, `w·q`, or `(#reveals)·q`. This exercises, at small scale,
everything that could break: the shape-disjoint per-query maximum (PRF vs chain blocks), the
swap/deferral over a DAG of hidden values with reveals that move down the chain over time, Hit
in both orders through one potential, the first-match walk (a toy `win_cases`), and Coll.
If this cannot be proved in ≈ 700 lines with the existing `LazyLemmas`/`HiddenInput` tools,
D5 is too expensive and the plan should fall back (§5.3).

M0b, `Direct/TwoColour.lean`: an adaptive reader of a uniform table with a colour bit that is
decided before the cell's first read (except a "pre-read" set whose colour switch has
probability `≤ ρ` independent of the values):
`Pr[∃ uncoloured i covered by coloured cells] ≤ n_u·Σ_r S(k,r)(n_c(1+ρ'))^r 2^{-hr}2^{-ak}`.
300–500 lines, independent of SLH-DSA.

### 5.2 Order

M0 → (go/no-go) → D0 → D1 → D2 → D3 ∥ D4 → D5 → D6 → D7a + D7b → D8 (tier B headline:
P64 2^-60.5) → M0b → D7c → D8 update (tier C: P64 2^-63). D3 and D7b can be written at any
time (pure, no probability).

### 5.3 Fallbacks that still gain bits

* **F1 (if D5 stalls).** Drop the deferral: charge a forger query at a hidden input with the
  existing hidden-input tools only where they apply directly (SK.seed and FORS secrets via the
  `patch` lemma: inputs drawn independently), and handle WOTS chains by the standard SM-UD hybrid
  inside the single game. This costs up to `w−2 = 14` extra per-query charges, but only for the
  `Th1` WOTS class. Since the classes are disjoint, the coefficient becomes `max(2, 15) = 15`
  instead of 27, and the re-signing charge is still gone: P64 ≈ 2^-60.1 (tier B′ ITSR: 2^-59.7),
  P20 ≈ 2^-64.1. Not computed by script; estimate `log2(15·2^64/2^128) = −60.09`.
* **F2 (dominant term at P64 only).** Keep the per-leg composition for `27·qf`, but do the direct
  argument for the *signing oracle's* charge: one game in which the per-leg adversaries share
  the challenger's signer, so the signer's cells are honest cells (the `H` tag) rather than
  adversary queries. That is the class-TCR answer-storing idea of TIGHT §8.1 generalised through
  D1. Expected P64: leg II → `27·qf/2^128 ≈ 2^-59.25` plus ITSR. With the existing ITSR leg this
  gives ≈ 2^-45.7; with D7a + D7b instead, ≈ 2^-59.1.
* **F3 (cheapest ITSR gain, any time).** D7b alone (Stirling form) applied to the existing
  `epsItsrF`: I.a at P64 −45.69 → −47.13. Not useful until leg II is below 2^-47.

---------------------------------------------------------------------------------------------

## 6. What I am unsure of, and what is a guess

The bound arithmetic is exact (scripts), but every probability claim in §2 is a proof sketch,
not a proof. The parts I am least sure of:

(i) **The swap/deferral lemma (D5) and its size.** Hidden values form a DAG whose hidden part
shrinks over time as signatures reveal lower chain positions. The forger's queries are adaptive
in the tweak. I believe the per-query 2^-128 is right (it is the classical ROM argument), but the
Lean shape of the involution, and the "until time `t`" invariance, are guesses. 1.5–2.5k lines
is an estimate with wide error bars; that is why M0 comes first.

(ii) **Tier C's pre-read targets** (`R` guessed by the forger before signing). I argued that the
effective coverer count is `qs(1+qf/2^128)`, using independence of `R_j` from every `cB` digest.
I have not checked the joint (multi-coverer) version carefully. If it fails, tier B′ (2^-60.5 at
P64) is the fallback, and it reuses proved machinery.

(iii) **C0 and Q are upper estimates from the existing counts**, not proved caps. They are
numerically irrelevant (C0 enters at 2^-116, Q at 2^-85).

(iv) The **entry lemma (D0)**: I checked that the PRF-real equality and the PRF realiser exist
(`prfRealPr_bPrfWC`, `RealizesPrf.real`). I did not check that the realiser's program exposes
keygen / signing / verification as separable phases for tagging. If it does not, D1 needs its
own open program (≈ +1k lines, reusing `Reduction/Open/Prf.lean`'s `openKeygenP`,
`prf_runForgerSig`, `sufCheckOpen` named in `PrfTr.lean`).

(v) **"2·qf is the best a per-query proof can do"** is my argument (preimage of an image point),
not a theorem. Whether a coefficient-1 bound holds (or a 2·qf/2^128 attack exists) is open. The
1-bit gap to the floor is therefore not claimed to be intrinsic.

(vi) **Literature constants** (HK22, 2024/910) are recalled: the HK22 PDF could not be fetched
(HTTP 403). The SPHINCS+ round-3.1 numbers were read from the local text.

(vii) F1's figure (coefficient 15) is an estimate, not computed in the scripts. The F2
expectation depends on reusing D1 inside per-leg games, which I have not designed in detail.
