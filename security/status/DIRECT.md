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

---------------------------------------------------------------------------------------------

## 7. 2026-11-22: milestones M0 and M0b in Lean (`Ideal/Direct/`, built, standard axioms)

### 7.1 Files

| file | lines | content |
|---|---|---|
| `Ideal/Direct/Engine.lean` | 274 | generic: `ex` (expectation; VCVio's `wp` is in `ProgramLogic`, not built here), `ex_hz_le_of_step:140` (**pending-charge supermartingale**: a step may defer its charge to a later sample), `prEvent_le_untilBad:195` (identical until a monotone bad event, two state types), list union bound, single-fresh-sample step |
| `Ideal/Direct/ToyDefs.lean` | 147 | the toy game: `Params` (`m`, `w`, `cv`, `out`, `P`, `F`, a parser making `P`/`F` injective and disjoint), `realProg:131` (lazy table, adaptive reveals), `realWin:142` |
| `Ideal/Direct/ToySwap.lean` | 242 | lazy = eager (`realWin_eq_eager`); **re-randomisation** `Psi g0 s k` (honest cells replaced by an independent table `s` of honest values), `reRand_bijective`, `realWin_eq_Psi:221` |
| `Ideal/Direct/ToyDefer.lean` | 448 | the deferred game `G2P` (hidden honest values never sampled while hidden; secret drawn last), `G2_eq_eager`, `untilBad_agree`, first-match walk `walk_hit:375`, coupling `realWin_le_G2:410` |
| `Ideal/Direct/ToyRom.lean` | 567 | hazards/pending charges on the lazy tables; `fresh_g`, `fresh_s` (an honest-value sample is charge-neutral), `rom_run_le:547` |
| `Ideal/Direct/ToyBound.lean` | 695 | support facts, query counts, fused handler `comb`, `comb_step:373` (per-query maximum), `G2_le:619`, **`toy_le:663`**, `toy_le_card:672` |
| `Ideal/Direct/TwoColour.lean` | 371 | `prT_tape2_le:217` (two-colour tape domination), `prT_tape2_cov_le:295`, **`twoColour_le:349`** |

Seven `import` lines appended to `Ideal.lean`; no existing file changed. `#print axioms` of every
headline: `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/`native_decide`/`bv_decide`.

### 7.2 M0 (the falsification test): proved

```
theorem toy_le (A : OracleComp T.advSpec (Fin T.m × ℕ × Y)) (q : ℕ)
    (hq : IsQueryBoundP A (fun t => T.isHash t = true) q) (δ : ℝ≥0∞)
    (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ δ) :
    T.realWin A ≤ q * max (2 * δ) (Fintype.card K : ℝ≥0∞)⁻¹ + (T.w + 1) * δ

theorem toy_le_card (A …) (q : ℕ) (hq …) [Fintype Y]
    (hδ : ∀ y, Pr{let u ← ($ᵗ St : ProbComp St)}[T.out u = y] ≤ (Fintype.card Y : ℝ≥0∞)⁻¹)
    (hKY : (Fintype.card Y : ℝ≥0∞) ≤ 2 * Fintype.card K) :
    T.realWin A ≤ (2 * q + T.w + 1) / Fintype.card Y
```
(`ToyBound.lean:663`, `:672`; finite `St Blk K Y`, decidable equality.) The game (`realProg`,
`ToyDefs.lean:131`): `k ← $K`; the adversary gets compression queries (lazy table) and any
number of adaptive `reveal (a, b)` (answer `v a (min b w)`, computed by compression queries);
it outputs `(a, j, x)`; the experiment evaluates the chain from `x` at `j` by compression
queries and wins iff `j <` every revealed position of chain `a` and the chain reaches
`v a w`. `q` counts only the adversary's compression queries; reveals and coins are free.

**No `m·q`, `w·q` or `#reveals·q` term.** Each query is charged once: `2δ` for a chain block
(guess of the hidden input + hit on the next honest value, each charged now or deferred to the
later sample of the honest value: either order), `1/|K|` for a secret-keyed block, `0` otherwise.

**Differences from the plan's statement** `(2q+1)/|Y| + (q + m(w+1) + 2)²/(2|St|)`:
1. **`w + 1` instead of `1`, and the plan's statement is false.** The experiment's own chain
   evaluation from the forged value makes `w` fresh cells, each of which can land on the next
   honest value. With `q = 0`, `w = 1`, no reveals, outputting a random `(a, 0, x)` wins with
   probability `≈ 2/|Y|` (`x = v a 0`, or the one verifier cell hits `v a 1`), above
   `1/|Y| + 8/|St|`. In general a `q = 0` adversary wins with `≈ (w+1)/|Y|`, so `(w+1)δ` is
   tight. **No damage to §3**: `C0 = 3928 + 259 + 64` already charges every verifier final cell
   once and every forged value once; the toy's `(w+1)` is exactly that accounting (verifier cells
   are charged `δ`, not `2δ`: the guess part of a verifier cell is covered by the first-match
   walk, `walk_hit`).
2. **No 2^-256 term.** All toy cells are single-block cells in row `cv`, so no chaining-value
   coincidence matters; the bound is stronger than asked, but M0 therefore does **not** test the
   Coll/rooted-chain part of D2/D6.
3. Per-query maximum `max (2δ) (1/|K|)` (shape disjointness through the parser), as planned.

**How it was proved (the route D5/D6 should take).** The plan's swap lemma (§2.5) was replaced by
a **re-randomisation**: `Psi g0 s k` overwrites each honest cell with an independent honest value
`s(a, j)` (the honest positions depend on `s` itself), and `(g0, s) ↦ (Psi g0 s k, g0 at the
honest cells)` is a bijection (`reRand_bijective`, 70 lines). Under `Psi` the DAG of hidden values
becomes a table of i.i.d. values, read lazily only when revealed. Then (i) identical-until-bad
against the deferred game, where `bad` is "the adversary queried an honest cell of a hidden
position", which the deferred handler logs so that it is a hazard of the final state;
(ii) lazy = eager (VCVio `completeTable`) for both games; (iii) one pending-charge supermartingale
over the deferred game's lazy tables in which a sample of an honest value resolves exactly the
pending candidates it can fire (`fresh_s`: charge-neutral) and a fresh adversary chain cell fires
a hit or adds a pending one (`fresh_g`); (iv) the first-match walk for the win condition. The
dynamic hidden set and the adaptivity of the tweak (§6 (i)) caused no difficulty.

**Effort signal.** 2370 lines (Engine 274 of them generic and reusable) against the planned
400–700: a factor ≈ 4. The probability steps were each routine once the method was fixed; the
bulk was bookkeeping: support/invariant lemmas through three handler levels (adversary handler,
lazy tables, fused handler), query counts, `ℝ≥0∞` arithmetic over `List.countP`/`Finset.card`
pending counts, and instance mismatches (`Decidable`, `MeasurableSpace`). Builds are fast
(< 1 min per file).

### 7.3 M0b (two-colour tape): proved for predictable colouring (ρ = 0) only

```
theorem twoColour_le (h a k : ℕ) [DecidableEq C] {ι} {spec : OracleSpec ι} [Finite C]
    [SampleableType V] [SampleableType (C → V)]
    (cell : ι → C) (lg₀ lg₁ : ι → Bool) (hdis : ∀ t, ¬ (lg₀ t = true ∧ lg₁ t = true))
    (ans : (C → V) → (t : ι) → spec.Range t)
    (hans : ∀ g g' t, g (cell t) = g' (cell t) → ans g t = ans g' t)
    (out : V → Digest h a k)
    (hout : ∀ p, Pr{let u ← $ᵗ V}[p (out u)] = Pr{let y ← $ᵗ (Digest h a k)}[p y])
    (oa : OracleComp (unifSpec + spec) α) (n₀ n₁ : ℕ)
    (hn₀ : IsQueryBoundP oa (fun i => lgB lg₀ i = true) n₀)
    (hn₁ : IsQueryBoundP oa (fun i => lgB lg₁ i = true) n₁) :
    prT ($ᵗ (C → V) >>= fun g =>
        (simulateQ (stImpl (ans g) (logM2 cell lg₀ lg₁)) oa).run ([], [], []) >>= fun z =>
          pure (covW h a k (z.2.2.1.map fun c => out (g c)) (z.2.2.2.map fun c => out (g c)))) ≤
      n₀ * targetCoverBound h a k n₁
```
(`TwoColour.lean:349`.) A cell takes the colour of its first read (candidate `lg₀`, coverer
`lg₁`); `covW` = some candidate digest has each of its `k` digits matched at its own leaf by
some coverer digest. `targetCoverBound h a k n = Σ_{r≤k} C(n,r)·#surj(k,r)·2^{-hr}·2^{-ak}
= Σ_r S(k,r)(n)_r 2^{-hr}2^{-ak}`, at most the plan's `Σ_r S(k,r) n^r 2^{-hr}2^{-ak}`.
Proof: `prT_tape2_le` (the marked-tape induction of `Games/ItsrTape.lean` with two marks: the two
colour classes' values are dominated by two independent tapes) and VCVio's split witness bound
(`evalDist_answerTape_tapeCoveredSplit_le_mul_targetCoverBound`). 371 lines.

**Not done: the pre-read part (ρ > 0).** A target cell first read by the forger (the forger
guessed `R_j`) is a coverer whose colour is decided after its value was seen. This is the case
§6 (ii) flags, and the reason tier C needs more than the predictable lemma: a separate union
bound costs `qs·qf/2^128` (≈ 1 at P64). What the right statement is, as far as I can see now:
model a target query as "the challenger samples `R ← $ᵗ R`, reads cell `κ m R` as coverer"
(`κ m` injective); bound `n₀ · weightedTargetCoverBound h a k n_T n_R (n_T/|R|)` (`n_R` = reads
that can be pre-read); VCVio already has the combinatorics
(`sum_pow_card_image_eq_weightedTargetCoverBound`), so the missing part is the probabilistic
witness bound `P[witness] ≤ 2^{-h·|im f|}·2^{-ak}·w^{#weighted coverers}` for an adaptive reader,
which mixes table values and the fresh `R`'s and is not a tape-domination statement (the
pre-read values are old, the adversary chooses the target messages after seeing them). Estimate
600–1000 lines (by the M0 factor, not the plan's 300–500). The multi-coverer joint version that
§6 (ii) says was not checked is exactly this witness bound; I believe it holds (each `R_j` is
independent of everything before it, so each weighted coverer pays `1/|R|` per target on top of
its value factor), but it is not proved. Tier B′ (`n = qf + qs + 2`, existing machinery) remains
the fallback.

### 7.4 Does the plan survive?

Yes, with changes.
* **D5 (the main risk) is retired at toy scale**: hidden values under adaptive, repeated,
  downward-moving reveals stay uniform with each query charged once, via re-randomisation +
  one deferred game + one supermartingale, all with existing VCVio/`Core` tools plus the 274-line
  engine. Replace "swap lemma" in §2.5/§5 by the re-randomisation of the honest structure; in the
  real scheme the bijection must re-randomise every honest cell, including the intermediate
  cells of `T_len`/`T_k` chains and the HMAC/`H_msg` cells (the toy had only final cells).
* **Constants**: §3's `C0` is right in kind (verifier cells once, forged values once); the toy
  bound's `+1` in §5.1 should read `+ (w+1)`.
* **Not yet tested by M0**: Coll / rooted chains / back-links (D2, D6): the supermartingale engine
  handles target-hitting events; collision events need the budgeted form (VCVio
  `FreshAnswer.lean` scope note) or a separate tape-collision argument (`prT_tape_bad_le`).
* **Tier C** needs the weighted pre-read witness lemma (7.3), not yet done.

**Updated cost estimate.** Apply the observed factor ≈ 4 to the probabilistic parts (D1, D5, D6,
D7c) and ≈ 1.5 to the deterministic ones (D0, D2–D4, D7a/b, D8): D0 0.6–1k, D1 1.5–2.5k,
D2 1.2–2k, D3 1–1.8k, D4 0.8–1.4k, D5+D6 (now one development, toy route) 5–8k, D7a+b 0.8–1.3k,
D8 0.6–1k: **≈ 12–19k lines for tier B** (plan: 7–10k), plus M0b-pre-read 0.6–1k and D7c 2–4k
for tier C (**≈ 15–24k total**, plan 8–12k). The engine and the re-randomisation pattern are
reusable as they stand.

---------------------------------------------------------------------------------------------

## 8. 2026-11-22 (second session): tier B main development, steps 1–2 (partial)

Brief: tier B′ (ITSR via `Games/ItsrTape`, no pre-read coverer lemma), in dependency order.
Four new files under `Ideal/Direct/`, imported from `Ideal.lean` (four `import` lines appended);
no existing Lean file changed; every headline `#print axioms` is
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`axiom`/`native_decide`/`bv_decide`.

### 8.1 Files and statements proved

| file | lines | content |
|---|---|---|
| `Ideal/Direct/Entry.lean` | 172 | D0: the SUF/EUF experiment as one compression program per table |
| `Ideal/Direct/Tagged.lean` | 454 | D1: tags F/H/V, phase split, tagged programs, F-count, tagged lazy table |
| `Ideal/Direct/Parse.lean` | 169 | D2 (block-level part): parse classes by tweak bytes |
| `Ideal/Direct/Extract.lean` | 174 | D3 (FORS part): `sufWin ⇒ Cover ∨ Hit ∨ HiddenEq_FORS ∨ evWots`; first-match walk |

**D0 (`Entry.lean`).**  `prfOI k` (`:36`) answers the `PRF`-game oracle at key `k` by its two
compression calls `out16 (g (g (IV, sb128 pk), blk128 a k))`; `progOf A` (`:47`) samples `k` and
runs `A` under it; `progS S oR pkSeedDist := progOf (AprfS S oR pkSeedDist)` (`:75`), `progE` (`:80`).
```
theorem prfReal_eq_progOf (g) (A) :                                              -- Entry.lean:63
    (Reduction.skPrfC Link.vp (primsG (liftC g))).prfRealExperiment (A.inst g) =
      simulateQ (instImpl₀ g) (progOf A)
theorem sufI_le_progS :                                                          -- Entry.lean:116
    sufI S (optRandU oR) pkSeedDist ≤ cfAdvantage fun g => simulateQ (instImpl₀ g) (progS S oR pkSeedDist)
theorem sufI_le_lazy :                                                           -- Entry.lean:155
    sufI S (optRandU oR) pkSeedDist ≤ HP.prT ((simulateQ (hS St Blk).romImpl (progS S oR pkSeedDist)).run' ∅)
```
and `eufI_le_progE` (`:123`), `eufI_le_lazy` (`:161`), `cfAdvantage_eq_lazy` (`:149`, generic form
`:134`: proved over abstract table types, because the kernel otherwise unfolds `Fintype.card`
of the concrete 2^768-element domain: "deep recursion").  This is `sufI`/`eufI` of the SAME game
objects as `suf_ideal_pure_closed_tight8` (via `sufP_le_sufI` for the pure interface); the
inequality comes only from the existing byte-to-typed transfer `bytes_strong_advantage_le`.  The
`PRF` game is used only on its real side (no `PRF` bound charged).

**D1 (`Tagged.lean`).**  `Tag = F | H | V` (`:39`), tagged oracle `hT`, `untagI`, `tagWith`;
`fullH k` (`:111`, `chainP` then `prfOI k`), `fullT k τ` (`:122`; port queries `F`, `PRF`-game
queries `H`, hash chains `τ`).  The phases are made visible by `bRestWOpenP_split` (`:165`)
/ `bRestOpenP_split` (`:191`): `bRestWOpenP … pkSeed = runWP … pkSeed >>= chkWP wO pkSeed`
(key generation + forger run, then the final check).  `progTS` (`:211`), `progTE` (`:219`):
first phase tagged `H`, check tagged `V`.
```
theorem untag_progTS : simulateQ untagI (progTS S oR pkSeedDist) = progS S oR pkSeedDist  -- :266
theorem progTS_F (hqf hqs hlong hout) :                                                  -- :338
    IsQueryBoundP (progTS S oR pkSeedDist) (fun i => isTag .F i = true) qf
theorem untag_eq (X : OracleComp TSpec α) (s : TCache) :                                 -- :412
    (fun z => (z.1, z.2.1)) <$> (simulateQ tagRom X).run s =
      (simulateQ (hS St Blk).romImpl (simulateQ untagI X)).run s.1
theorem sufI_le_tag :                                                                    -- :431
    sufI S (optRandU oR) pkSeedDist ≤
      HP.prT ((simulateQ tagRom (progTS S oR pkSeedDist)).run' (∅, fun _ => none))
```
(`untag_progTE` `:275`, `progTE_F` `:351`, `eufI_le_tag` `:439`).  `tagRom` (`:376`) is the lazy
table whose state is `(cache, first-reader tag)`; a fresh cell records the tag of its first
reader.  So every later probability argument can be run on ONE table with first-reader tags.
Not yet proved: the H and V counts (`#V ≤ Vc` in the plan's D1).  They follow from the existing
`bPrfWCOpenP_*` count lemmas exactly as `progTS_F` follows from `bPrfWCOpenP_port`, but are not
needed before D6.

**D2, block-level part (`Parse.lean`).**  `Role = kprf | kseed a k | th1 A xs | thF A | other`
(`:45`), `role cv aty q` (`:84`) classifies a cell by its chaining value (`IV`, `cv`) and its
tweak bytes `btw128 b` through a classifier `aty : Bytes 22 → AdKind` (prf/short/long/none).
`role_blk128` (`:96`: the honest `PRF` cell is `kseed a k`), `role_short` (`:110`), `role_th1_iff`
(`:129`: `role = th1 A xs ↔ c = cv ∧ aty A = short ∧ xs short ∧ b = (tblocks A xs).1`),
`blk_short_unique` (`:59`), `kprf_not_short` (`:64`), `kprf_not_seed` (`:70`).

**D3, first part (`Extract.lean`, namespace `Reduction.Direct`, over any `Primitives` and any
secret table).**
```
def evHidF pkSeed tbl z : Prop :=                                                       -- :75
  ∃ i : Fin k, (forsAdrs, leafIndex parts i) ∉ openedLeaves pk (signed z.2) ∧
    (z.1.2.fors[i]).sk = ((refSig pkSeed tbl z).fors[i]).sk
theorem evOpen_cases (hS) : evOpen pkSeed tbl z = true → evHidF pkSeed tbl z ∨ evColl pkSeed tbl z = true  -- :94
theorem suf_extract (hS) (h : sufWin pkSeed tbl z = true) :                             -- :116
    evItsr pkSeed tbl z = true ∨ evColl pkSeed tbl z = true ∨ evHidF pkSeed tbl z ∨ evWots pkSeed tbl z = true
theorem fresh_extract (hS) (h : freshWin pkSeed tbl z = true) : (same four)              -- :132
theorem chain_walk (F : ℕ → Y → Y) (v y : ℕ → Y) (a n) (steps) (v (a+n) = y (a+n)) :     -- :148
    v a = y a ∨ ∃ p, a ≤ p ∧ p < a + n ∧ v p ≠ y p ∧ F p (v p) = F p (y p)
```
`evItsr` = Cover, `evColl` = Hit (a verification call colliding with an honest call at its
tweak), `evHidF` = HiddenEq at a FORS leaf.  New helper: `fors_leaf_verify_mem` (`:63`, the
forged leaf call is a verification call).

### 8.2 Deviations from the plan

1. **Parse classes are not disjoint by block shape** (§2.3 claims they are).  The first block of
   a 35-value `T_len` input has data in bytes `22..63`, so it can equal the first block of a
   one-value `Thash` call at the same tweak (data `x ‖ 0x80 ‖ 0^17 ‖ len64(816)` in bytes
   `22..63`).  No damage: the class is decided by the tweak bytes, an honest tweak is of exactly
   one kind (address type inside `ADRSc`), and `role` classifies by tweak (`aty`).  The bound
   does not change.  (Not machine-checked as a counterexample; the byte layout is
   `tbytes A xs = A ‖ flat xs ‖ tailL (86 + 16·|xs|)`, `Sha/Shape.lean:240`.)
2. **Extraction is stated at the `G2` level** (secret table `tbl`, `idealPk`/`idealSign`), quantified
   over all tables, as the existing case analysis is.  The direct program `progTS` runs the real
   key generation and signing with `PRF(SK.seed, ·)` and HMAC randomisers; the bridge
   "real key generation / signing at `SK.seed` = `idealPk`/`idealSign` at the `PRF` table" exists
   in `Reduction` (it is what makes the `G0 = G1` hop of the PRF game exact) but is not yet
   instantiated for `progTS`'s final-state variables.  Part of step 3 (D4 lift).
3. **The V tag is obtained from a phase split**, not from the query: the forger run and the
   check are separated syntactically (`bRestWOpenP_split`) and tagged by two different handlers;
   the forger count then needs a continuation-transfer lemma (`fullT_bind_F`).

### 8.3 What remains (exact statements)

* **D3, WOTS+ part.**  With `parts = digestParts pk z.1.2.randomness z.1.1`, `ref = refSig pkSeed tbl z`,
  `m_j`/`m'_j` the forged/reference layer messages and `σ_j`, `ρ_j` the WOTS+ signatures at layer
  `j`, `b_i = chainStepsCore m'_j i`, `a_i = chainStepsCore m_j i`, `A_{j,i}(p)` the chain tweak:
  ```
  def evHidW pkSeed tbl z : Prop := ∃ j i, a_i < b_i ∧ σ_j[i] = chain pk A_{j,i} (secret_{j,i}) 0 a_i
  theorem evWots_cases (hS) (h : evWots pkSeed tbl z = true) : evHidW pkSeed tbl z ∨ evColl pkSeed tbl z = true
  ```
  Proof: `wotsPkFromSigTops_cases` (VCVio `HashSig/SLHDSA/Security/WotsWitnesses.lean:240`) gives
  chain `i` with `a_i < b_i` and either an `F`-preimage of `ρ_j[i]` at position `b_i − 1` (then
  `chain_walk` from `a_i` to `b_i`: HiddenEq at `a_i` or a collision at some `p ∈ [a_i, b_i)`) or
  a collision at `t ≥ b_i`.  Missing: two membership lemmas, (i) the forged chain call at
  `(A_{j,i}(p), [v_p])`, `p ∈ [a_i, w−1)`, is in `verifyCalls pk msg sig` (through `col_pkFromSig`,
  `col_layerProg`, `xmssPkFromSigM`, `wotsPkFromSigM`), and (ii) the honest chain call at
  `(A_{j,i}(p), [y_p])`, every `p < w − 1`, is in `honestCalls tbl pkSeed` (through
  `sub_honestCalls_eq`, `sub_xmss_spec`, `sub_wots_spec`, `sub_chain_spec`, `Reduction/TCR.lean:1468–1797`).
  Estimate 400–700 lines.
* **D4 (lift), D5/D6 (re-randomisation and the single supermartingale over `tagRom`), D7a/b
  (ITSR tier B′), D8 (composition, numerics, comparison with tight8)**: not started.  Their
  statements are those of §5 with the corrections of §7 (C0 charges each verifier final cell
  `δ` and each forged value once; `(w+1)δ` per toy chain).
* **Collision / rooted-chain part (step 4): not reached.**  The form I would choose: the
  *budgeted* form, i.e. `Coll` as a hazard of the same pending-charge supermartingale
  (`Engine.ex_hz_le_of_step`), each fresh sample charged `(#cache)/2^256 ≤ Q/2^256` under a
  state-carried cell counter bounded by the program's total compression count `Q`
  (= `qf` + the H and V counts of D1), giving `Q²/2^256`; the alternative `prT_tape_bad_le`
  (tape collision) needs the whole run as one tape and does not compose with the tag
  bookkeeping.  Untested.

### 8.4 Updated estimate and predicted bounds

Done this session: ≈ 970 lines (D0 complete, D1 complete except the H/V counts, D2 block-level,
D3 FORS part).  D0 cost 172 lines against the planned 400–700 (the realiser's equations were
reusable as they stand); D1 454 against 600–900 (before the factor-4 correction).  Remaining for
tier B: D1 counts 0.2k, D2 rooted classes 0.8–1.5k, D3 WOTS 0.4–0.7k, D4 0.8–1.4k, D5+D6
5–8k, D7a+b 0.8–1.3k, D8 0.6–1k: **≈ 9–14k lines** (the §7.4 estimate 12–19k less what is done,
and less the D0/D1 savings).

Predicted bounds unchanged (nothing proved this session changes them): tier B′
P20 `2^-67.00`, P40 `2^-62.99`, P64 `2^-60.54` (§3), against tight8 `2^-63`, `2^-59`, `2^-39`
(rounded proved points).

---------------------------------------------------------------------------------------------

## 9. 2026-11-22 (third session): deterministic part finished (SUF), generic probabilistic tools

Seven new files under `Ideal/Direct/` (1731 lines), seven `import` lines appended to
`Ideal.lean`; no existing Lean file changed.  `lake build Ideal`: success (7425 jobs).  Every
headline `#print axioms` is `[propext, Classical.choice, Quot.sound]` (three small lemmas
`[propext, Quot.sound]`); no `sorry`/`axiom`/`native_decide`/`bv_decide`.  **The final theorem
(tier B′ headline) is NOT proved; nothing below is a bound on `sufI`.**

### 9.1 Statements proved

| file | lines | content |
|---|---|---|
| `Direct/ExtractWots.lean` | 345 | D3, WOTS+ part (§8.3), and the full extraction |
| `Direct/Counts.lean` | 147 | D1 counts: total tagged queries |
| `Direct/Bridge.lean` | 437 | the real experiment at the `PRF` table, pathwise extraction |
| `Direct/EntryBridge.lean` | 44 | `sufI` ≤ table average of the extraction events |
| `Direct/DagSwap.lean` | 339 | generic re-randomisation of an honest DAG, with collisions |
| `Direct/Rooted.lean` | 204 | rooted chains in a cache, classes `ThL`, `HmF`, uniqueness |
| `Direct/CollBudget.lean` | 215 | Coll as a budgeted hazard of the supermartingale |

**D3 complete (SUF and EUF).**
```
def evHidW pkSeed tbl z : Prop :=                                      -- ExtractWots.lean:187
  ∃ (j : Fin d) (i : Fin len), chainStepsCore (fLayerMsg pkSeed tbl z j) i <
      chainStepsCore (hMsgA tbl pkSeed (layerWotsAdrs parts j)) i ∧
    (z.1.2.hypertree[j]).wots[i] = chain prims pkSeed (wotsChainAdrs (layerWotsAdrs parts j) i)
      (secretOf vp prims tbl (wotsSkAdrs (layerWotsAdrs parts j) i)) 0 (chainStepsCore (fLayerMsg …) i)
theorem evWots_cases (hS) (h : evWots pkSeed tbl z = true) :           -- :217
    evHidW pkSeed tbl z ∨ evColl pkSeed tbl z = true
theorem suf_extract_full (hS) (h : sufWin pkSeed tbl z = true) :       -- :312
    evItsr pkSeed tbl z = true ∨ evColl pkSeed tbl z = true ∨ evHidF pkSeed tbl z ∨ evHidW pkSeed tbl z
theorem fresh_extract_full (hS) (h : freshWin pkSeed tbl z = true) : (same)   -- :325
```
The two membership lemmas: `wots_chain_verify_mem` (`:61`; every step `t ∈ [a, w−1)` of the
forged chain at layer `j`, chain `i`, is in `verifyCalls`) and `wots_chain_honest_mem` (`:131`;
every step `p < w−1` of every honest chain on the path is in `honestCalls`).  The reference
signature's layer values come from the existing `y_idealSign_layer` (`Reduction/WotsEmbed.lean:1191`).

**Counts.**  `qb_of_untag` (`Counts.lean:38`), `progS_comp` (`:103`), and
```
theorem progTS_all (hqf hqs hlong hout) :                                -- Counts.lean:125
    IsQueryBoundP (progTS S oR pkSeedDist) (fun i => i.isRight = true) (qPrf qf qs ℓ + 2 * qOPrf qs)
```
(`progTE_all` `:134`): the cell budget `Q` of the collision term (all tags).  **Not done: the
`V` count.**  The bound `(1 + verifyHashes)·11 + hmsgCost ℓ` needs the forged-message length
`≤ ℓ` on the support of the first phase; and for the charge only the verifier's `Thash` cells
matter (`≤ 3928·11`, independent of `ℓ`), which the tags cannot separate from its `H_msg` cells.
Deferred to D6, where the charged class is decided.  The `H` count is subsumed by `progTS_all`.

**Bridge (D3 → the real program).**  Over any `Structural` bundle:
```
noncomputable def prfTbl pkSeed k : SecretTable := idx ↦ PRF(pkSeed, k, canonical preimage of idx)
theorem secretOf_prfTbl … (ha : a.isCanonical) : secretOf (prfTbl pkSeed k) a = PRF pkSeed k a  -- Bridge.lean:54
theorem expW_real_eq_prfTbl (hS) (w) (A) :                               -- :289  (exact, no PRF charge)
    prTrue (expW realAlg w A) = prTrue (pkSeed ← pkSeedDist; k ← $; SK.prf ← $;
      z ← tableAlg.runWithSigningOracle (idealPk (prfTbl pkSeed k) pkSeed) (prfTbl pkSeed k, SK.prf) …; w …)
theorem suf_real_eq_sufWin (hS) (A) :                                    -- :400
    prTrue (expW realAlg sufCheck A) = prTrue (pkSeed ← pkSeedDist; k ← $; SK.prf ← $;
      z ← g1Run A (prfTbl pkSeed k) (idealPk …) SK.prf; pure (sufWin pkSeed (prfTbl pkSeed k) z))
theorem suf_real_le_extract (hS) (A) : prTrue (expW realAlg sufCheck A) ≤
    prTrue (…; z ← g1Run …; pure (decide (evItsr ∨ evColl ∨ evHidF ∨ evHidW at prfTbl pkSeed k)))  -- :416
theorem sufI_le_extract :  sufI S (optRandU oR) pkSeedDist ≤ cfAvg fun g =>   -- EntryBridge.lean:26
    prTrue (… g1Run (S.typedS (optRandU oR) pkSeedDist g) (prfTbl pkSeed k) … ; extraction events)
```
`g1Run` (`:335`): the forger against the table signer with `R = PRF_msg(SK.prf, opt_rand, M)`,
transcript `(M, opt_rand, R)` as a `G2Log`; `g1Run_proj` (`:348`) projects it to
`tableAlg.runWithSigningOracle`.  **Copied code**: `keygen_sim`, `sign_sim`, `run_eq`,
`rest_sim`, `bSign`, `bRest`, `canonical_of_secretChild`, `queriesIn_bRest` of
`Reduction/SufHopPrf.lean` are private there and are copied into `Bridge.lean` (suffix `B`,
`queriesIn` restated for the canonical-address set without the seed condition).
**Not done: the EUF twin** (`expW` with an EUF check, through `prfRealPr_bPrfC`); it is the same
proof with `fresh_extract_full`.  `sufI_le_extract` is the entry the probabilistic core starts
from: the events are about `Thash_g` at the table `g` and the secret table `prfTbl`, and no hop
has been charged.

**Re-randomisation with collisions (generic, item 2).**  `DagS C V I` (`DagSwap.lean`): ranks,
cells `pos g s i` depending on lower-rank honest values and on `g` at public cells `P` (the
midstate cell).  `hv D g` (honest values, `hv_eq :82`), `Psi D g0 s` (`:109`), `Good`
(honest cells pairwise distinct and outside `P`).
```
theorem hv_Psi (h : Good D g0 s) : hv D (Psi D g0 s) = s                 -- DagSwap.lean:138
theorem ex_le_Psi (f : (C → V) → ℝ≥0∞) (hf : ∀ g, f g ≤ 1) :             -- :263
    ex ($ᵗ (C → V)) f ≤ ex ($ᵗ (C → V)) (fun g0 => ex ($ᵗ (I → V)) fun s => f (Psi D g0 s)) +
      ex ($ᵗ (C → V)) (fun g0 => ex ($ᵗ (I → V)) fun s => propInd (¬ Good D g0 s))
```
This is the toy's `realWin_eq_Psi` for an arbitrary honest DAG: intermediate `T_len`/`T_k` cells
(chaining value = full value of the previous honest cell) are allowed; the price is the
probability that two honest cells coincide (then `(g0, s) ↦ (Psi, g0∘pos)` is not injective),
`≤ #I²/2^256 ≈ 2^-94` for SLH-DSA (estimate, the instance is not built).

**Rooted chains (item 1 / D2).**  `mdC κ c bs` (iteration through a cache), `NoCollC c₀ κ`,
`rooted_unique` (`Rooted.lean:88`: under `NoCollC`, a value is reached from `c₀` by one block
list only), `rootOf`, `IsThL pk κ q A xs` (the last cell of `Thash(pk, A, xs)`, any length),
`isThL_unique` (`:154`), `isThL_value` (`:168`: its value through a total table extending the
cache is the `Thash` chaining value), `IsHmF κ q R pk s` (the `H_msg` outer final cell),
`isHmF_unique` (`:185`).

**Collisions in the same supermartingale (item 3).**  `ex_hz_le_of_step_cap`
(`CollBudget.lean:36`: the engine with a state size growing by ≤ 1 per charged step and the step
bound needed only below the cap `Q`), `CollZ`, `collZ_update`, `prEvent_fresh_coll_le` (`:165`:
`≤ (|Z| + size)/|V|`), `ex_hz_fresh_coll_le` (`:194`: one fresh sample with `CollZ ∨ P` as the
hazard).  So the budgeted form works as proposed: `Q` charged samples cost `Q(Q+|Z|)/2^256`.
**One addition is needed (not a failure):** `CollZ` sees value coincidences only; the
**back-link** event (a fresh value equal to the chaining input of an earlier cached cell) is a
property of the order of samples, so the state must record it.  It costs the same `≤ size/|V|`
per sample (`Engine.ex_hz_fresh_le` with the set of cached chaining inputs), but needs a state
with a flag or a sample order (an extension of `tagRom`, which keeps none).

### 9.2 Not done (exact remaining statements)

* **EUF bridge** (`eufI_le_extract`), and the `V` count (above).
* **Tier B′ needs a marking change.**  With the present tags (`F`/`H`/`V` by phase), the
  signer's *inner*-final `H_msg` cell has block `cB` whenever `|M| = 20` with `M[16..19] = 0`
  (L8), so marking all `cB` cells gives `n = qf + 2qs + 2`: P64 **2^-55.04** (tier "B" of
  `tiers.out`) instead of 2^-60.54.  For `n = qf + qs + 2` the signer's outer-final call needs its
  own tag (a change of `qTag`/`fullT` and of the chain interpretation of an `H_msg` query) or the
  extra 2^-256 event of §2.4.
* **The probabilistic core (D4–D6) is not started beyond the generic tools.**  Remaining, in
  order: (a) the `DagS` instance of SLH-DSA-128s (index = ledger address × block, plus secret
  addresses; children from VCVio's `childAdrs`, `HashSig/SLHDSA/Security/NodeGraph.lean:95`) and
  `Pr[¬Good] ≤ #I²/2^256`; (b) honest values of `Psi` = `idealPk`/`idealSign` at `prfTbl` in
  terms of `s`; (c) the deferred SUF game (signer reads `s` at the signature's indices, routing of
  compression queries at cells with known parents); (d) identical-until-bad against `g1Run` at
  `Psi g0 s` (`Engine.prEvent_le_untilBad`); (e) lazy = eager for the deferred game; (f) the
  supermartingale with the per-class charges (`Parse.role`, `IsThL`), `CollZ` + back-link
  budget, Kseed; (g) `sufI_le_extract`'s events ⇒ the deferred hazards; (h) ITSR tier B′ via
  `prT_tape_le_marked`; (i) composition and the three points.  Estimate unchanged: 7–9k lines.

### 9.3 A cheaper route found while doing this (recommended re-plan, not started)

VCVio already proves, at the **three-oracle** level (tweakable hash, `H_msg`, `PRF_msg` as random
oracles, `PRF` as `F` at secret-key addresses — the same shape as SHA2's `PRF`), exactly the bound
this plan targets: `strongUnforgeableAdvantage_romScheme_le_securityBound`
(`HashSig/SLHDSA/Security/CoverageBound.lean:361`), `securityBound p |Y| 2 1 qh qs =
(qh+1)·weightedTargetCoverBound h a k qs qh (qs/|Y|) + (2qh + 2V)/|Y|` (`Target.lean:243`): the
**tier C** bound (P64 ≈ 2^-62.98), with the per-query coefficient 2, hidden-value deferral and
pre-read coverers all done.  The compression model reduces to it by a Merkle–Damgård
indifferentiability simulator: a forger `B` against `romScheme` at the SHA2-128s core runs `S`,
answers its compression queries from a lazy table and, when a query completes a rooted chain
(`Rooted.lean`: `IsThL`, `IsHmF`, and the analogous HMAC class), answers the final cell from the
matching oracle (`qh ≤ qf`, one oracle query per completing cell, by `isThL_unique`); its error is
collision/back-link only (`CollBudget.lean`), `O(Q²/2^256)`, no 2^-128 term.  What it needs: the
coupling of `progS` (honest hashing by compression chains) with `romScheme` (honest hashing by
oracle queries) until a collision — the standard "intermediate honest cells are fresh either way"
argument — plus `ByteLaws`/`KeyDiscipline` of the SHA2-128s core (VCVio discharges them at every
FIPS 205 bundle; the repository has `Concrete.keySeparated_sha2Primitives`).  Estimate 3–5k lines
(the generic MD/HMAC coupling is most of it), against 7–9k for D4–D8 here, for a better bound
(tier C instead of B′).  Not attempted this session; it should be decided before more of §9.2 is
built (`Bridge.lean`, `Rooted.lean`, `CollBudget.lean` serve both routes; `DagSwap.lean` only the
direct one).

### 9.4 Bounds

No change to the predicted bounds (nothing proved bounds `sufI`): tier B′ P20 2^-67.00, P40
2^-62.99, P64 2^-60.54 — or 2^-55.04 at P64 with the present tags (9.2); the route of 9.3 would
give tier C (2^-67.00, 2^-63.00, 2^-62.98).  Proved bounds remain tight8's: 2^-63, 2^-59, 2^-39.

---------------------------------------------------------------------------------------------

## 10. 2026-11-22 (fourth session): the ROM-reduction route of §9.3

Decision taken (brief): reduce the compression game to VCVio's three-oracle theorem through a
Merkle–Damgård simulator.  Script `direct/rom_route.py` (output `direct/rom_route.out`; exact
rationals, NOT machine-checked).

### 10.1 Question 1: the true error of the simulation hop

**Setting.**  `G_real` = the compression game of `sufI` (one lazy table `g` read by the forger,
the signer and the verifier; `Entry.sufI_le_lazy`).  `G_rom` = VCVio's SUF experiment of
`romScheme prims.core (Equiv.refl _) optRand pkSeedDist` (`Thash`, `H_msg`, `PRF_msg` lazy random
oracles, `PRF` = `F` at secret-key addresses) against the adversary `B = Sim ∘ S`.  `Sim` keeps its
own table `T` for the forger's compression queries; on a fresh cell `(c, b)` it answers
`O(Q) ‖ ext` (`ext` fresh) iff the cell is the **final cell of a `T`-rooted chain of a relevant
query** `Q`, and a fresh 256-bit value otherwise.  Rootedness is **dynamic** (with respect to the
current `T`: `Rooted.lean`'s `mdC`, `rootOf`).  **Relevant** (this is a design decision forced by
the analysis below):

* `Thash(ps, key, xs)` with `ps = PK.seed` and `|xs| = arity(key)` (arity read from the type and
  tree-height fields of `ADRSc`: 1 for WOTS hash/WOTS_PRF/FORS_PRF/FORS leaf, 2 for tree nodes,
  35 for WOTS_PK, 14 for FORS_ROOTS).  The secret-key `PRF` cell is the arity-1 `Thash` cell at a
  PRF address, exactly VCVio's `oracleSecret` (`Link.hprf_dom`).
* `H_msg(R, ps, pr, M)` with `ps = PK.seed`, `pr = PK.root`: the outer final cell
  `(T(IV, R‖ps‖X), cB)` with `X` the `T`-value of the final cell of the `T`-rooted inner chain
  of `R‖ps‖pr‖M`.  Inner finals are never oracle-answered.
* `PRF_msg(k, o, M)` for **every** key `k` (the simulator does not know `SK.prf`): the outer
  HMAC final `(T(IV, okey k), X‖pad)` with `X` the `T`-value of the inner chain of
  `ikey k ‖ o ‖ M`.

Parse classes are disjoint by the first block (`ps‖0^48` / `okey`/`ikey` / anything else, under
no 256-bit coincidence), and a cell is the final of at most one query of each kind
(`isThL_unique`, `isHmF_unique`; message recovered from the block list by the MD padding).

**The events, one by one** (per forger compression query unless said otherwise).

(a) *Chaining input equal to an honest state the forger has not computed.*
* Internal state (any `T_len`/`T_k`, `H_msg`-inner, HMAC-inner intermediate CV, the HMAC key
  midstates, the `PK.seed` midstate before the forger reads it): fully hidden 256-bit value,
  `≤ N_hon/2^256` per query, inside the collision term below.
* Final untruncated state of an honest **Thash/PRF/PRF_msg** cell (`y ‖ z`, `y` revealed, `z` 128
  hidden bits): the forger guesses `z` with probability `2^-128·mult(y)` per query.  **This is
  not charged**: the forger's cell `(y‖z, b')` is fresh in both games, and the chain it extends
  is a query of the *same* key at a *larger* arity (`Thash`), or not a query at all (HMAC outer
  has exactly two blocks), so it is never relevant and never read by the signer or verifier.  In
  `G_rom` the same situation is a back-link in `T` when the simulator later samples `ext = z`;
  with dynamic rootedness and narrow relevance this back-link creates no new relevant final, so
  `T` and `O` stay consistent on every query anyone else reads.  With a *wide* relevance (all
  arities) it would cost `+qf/2^128` (0.58 bit at P20).  No attack: the extension values are
  computable by the forger anyway.
* Final untruncated state of an honest **`H_msg` outer** cell: only `2` bytes beyond the 30-byte
  digest (the signature reveals 231 of the digest's 240 bits; the forger can in any case compute
  the whole chain, all inputs are public).  Guessing costs `2^-16` per query, so this event must
  not be a bad event.  It is harmless for the same reason as above **except** when the extension
  is itself a relevant `H_msg` query: the chain `IV → R_i‖PK.seed‖X_i → cB → b' …` parses as the
  inner chain of `H_msg(R_i, PK.seed, X_i[0..16), …)`, relevant iff **`X_i[0..16) = PK.root`**.
  That is the only honest-on-honest extension in SLH-DSA-SHA2-128s:
  **`E_root := ∃ signing query i, X_i[0..16) = PK.root`** (`X_i` the signer's inner digest), of
  probability `≤ qs/2^128` (each `X_i` is a fresh 256-bit sample drawn after `PK.root`).  On
  `E_root` the forger can (by `2^16` guesses) make the simulator answer the verifier's
  `H_msg(R_i, PK.seed, PK.root, M*)` inconsistently.  No forgery results (the forger could
  compute that value honestly), so `E_root` is an **artefact** of this simulator; a simulator
  that pre-computes each signing query's `H_msg` (one oracle query per signature, `qh = qf + qs`)
  avoids it but pays `2qs/2^128`, which is worse (P64 `2^-61.99` instead of `2^-62.41`).
  All other honest/verifier-on-honest extensions need `PK.seed`/`PK.root` to equal fixed
  patterns (`0^16`, `0x5c^16`, `0x36^16`) or a 256-bit match: `≤ 2^-255` in total.

(b) *`PRF` and `PRF_msg` as keyed oracles.*  A forger cell `(cv, ADRSc_sk ‖ k ‖ pad)` is
relevant (arity 1 at a PRF address) and becomes the oracle query `F(PK.seed, ADRSc_sk, [k])`;
`k = SK.seed` is VCVio's hidden-value hit, charged inside its `2·qh/|Y|`.  An HMAC chain under a
guessed key `k` becomes `PRF_msg(k, o, M)`; `k = SK.prf` is charged inside the same `2·qh/|Y|`
(hypothesis `|Y| ≤ |SK.prf|`).  The `PK.seed` midstate shared by the `PRF` cells and the public
`Thash` cells is a public cell of `T` (drawn when the forger first reads `(IV, sb PK.seed)`);
the honest key midstates `g(IV, ikey SK.prf)`, `g(IV, okey SK.prf)` are hidden 256-bit values
(collision term).  So the shape-marking of `Realize/{PrfMark,MsgMark}.lean` (the per-game
`1·qf` and `2·qf` legs of tight8) has no counterpart: those queries are just oracle queries of
`B`, each charged once, at the per-query rate 2 shared with every other class.

(c) *HMAC inner/outer, two-stage `H_msg`.*  Inner finals are internal cells of the simulator
(fresh values), outer finals are the only oracle-answered cells; one oracle query per outer
final.  The inner message is recovered from the unique `T`-rooted block list.

(d) *The §9.4 coincidence* (a 20-byte signed message with `M[16..19] = 0` has inner last block
`cB`).  Irrelevant here: the simulator classifies by rooted parse, not by block shape.  For the
signer's inner final cell to also be an outer final it must be rooted as `R‖PK.seed‖X` with `X`
an inner digest: `X = PK.root ‖ M_i[0..16)`, which needs `X[0..16) = PK.root` *and* the fresh
`R_i` equal to the `R` of a chain computed before: `≤ 2^-256` per pair, collision term.

(e) *256-bit events* (collisions among all cells, a value equal to `IV`, back-links among fully
fresh samples, a forger key equal to an unseen honest internal value, the dual parses above):
`≤ 4·(Q+1)²/2^256` with `Q = QcAll qf qs ℓ + 2·qOPrf qs` (every cell of the real run; the
`Counts.lean` budget).

**Error formula.**
```
ε_hop(qf, qs, ℓ) = (Q + 1)² / 2^254 + qs / 2^128,      Q = QcAll qf qs ℓ + 2·qOPrf qs
sufI S (optRandU oR) ($ᵗ) ≤ securityBound p 2^128 2 1 qf qs + ε_hop(qf, qs, ℓ)
securityBound p |Y| 2 1 qh qs = (qh+1)·wTCB(63,12,14; qs, qh, qs/|Y|) + (2·qh + 2·3929)/|Y|
```
| | P20 | P40 | P64 |
|---|---|---|---|
| coverage `(qh+1)·wTCB` | 2^-151.00 | 2^-127.00 | 2^-69.73 |
| `2(qh+V)/|Y|` | 2^-67.00 | 2^-63.00 | 2^-63.00 |
| hop: 256-bit | 2^-134.0 | 2^-122.7 | 2^-75.8 |
| hop: `E_root` | 2^-108 | 2^-88 | 2^-64 |
| **total** | **2^-67.00** | **2^-63.00** | **2^-62.41** |
| total, coverage with `surj(14,r) ≤ r^14` (the Lean form) | 2^-67.00 | 2^-63.00 | 2^-62.35 |
| tight8 (proved) | 2^-63.00 | 2^-58.91 | 2^-38.97 |
| generic floor (§1.3) | 2^-68.00 | 2^-64.00 | 2^-63.97 |

So the honest answer is **better than tier B** (2^-67 / 2^-63 / 2^-60.5) and equal to tier C up
to the `E_root` artefact at P64 (2^-62.41 against 2^-62.99).  The hop's error is
"collisions plus one `qs/2^128` coincidence", not "only collisions": the brief's doubt was right
in kind (truncation and plain MD do create 2^-128 and even 2^-16 per-query events), but with
dynamic rootedness and narrow relevance all of them are harmless except `E_root`.

### 10.2 Question 2: does the game match?

Yes.  After the hop the game is VCVio's `strongUnforgeableExperiment B` for
`romScheme core (Equiv.refl _) (fun pk => oR pk.pkSeed pk.pkRoot) ($ᵗ (Bytes 16))`, at
`core = Link.prims.core` or, as built in 10.4, at the repository's table-independent reference
core `core₀` (same carriers, `adrsToKey`, `yToBytes`; trivial `PRF`/`PRFmsg` fields, which
`romScheme` never reads), which is
literally `sufI`'s scheme with the hash functions replaced by oracles: the repository already
proves `romScheme_map_romAnswer_128s` (`Link/Security.lean:260`: that scheme with the oracles
answered by SHA-2 is `internalAlg vp prims`, the typed scheme under `bytesView`), and the
compression model's `primsG (liftC g)` has the same carriers (`Bytes 16`, `AdrsKey = Bytes 22`),
the same `adrsToKey = sha2AdrsKey`, `yToBytes = id`; only its `PRF`/`PRFmsg` fields (unused by
`romScheme`) differ.  Every hypothesis of the VCVio theorem is already discharged in the
repository: **`Link.security_128s`** (`Link/Security.lean:46`) is
`strongUnforgeableAdvantage (rom (hashSpec prims.core)) adv ≤ securityBound vp.params (256^16) 2 1 qh qs`
for every `e`, `optRand`, `pkSeedDist` (via `SLHDSA.CoverageBoundTest.strongUnforgeableAdvantage_sha2_le`
with `fipsApprovedAddressBounds S128`: `ByteLaws` is `yToBytes = id` injective,
`KeyDiscipline` is `keyDiscipline_sha2Primitives`, `hcard` is `2^128 ≤ 2^128`, `e = Equiv.refl`);
`Link.security_128s_euf` is the EUF form.  At `core₀` the same four hypotheses are
`RomSim.byteLaws₀`, `keyDiscipline₀` (the fields of `keyDiscipline_sha2Primitives`, by
definitional unfolding of `adrsToKey`), `le_rfl`, `Equiv.refl`.  The quantum integration uses the same objects
(`DigestTransport`).  Hedged randomness `optRandU oR = fun g pk => oR pk.pkSeed pk.pkRoot` does
not depend on `g`, so it is one `optRand` of `romScheme`.

### 10.3 Question 3: query accounting

`qh(B) ≤ qf`: `B` makes a hash query only on a **fresh** forger cell that is a relevant final,
and then exactly one; cache hits, internal cells and non-relevant finals make none.  Signing:
`qs(B) = qs` (one typed signing query per byte signing query, `Coded.signingImpl`).  No
message-length term enters `qh` (a long `H_msg`/`PRF_msg` costs the forger one compression query
per block but `B` one oracle query in total); `ℓ` enters only the 256-bit term through `Q` (the
signer's and verifier's `H_msg`/HMAC chains on messages of `≤ ℓ` bytes), which is why `hlong`
and `hout` stay hypotheses.

### 10.4 Statements proved (Lean, `lake build Ideal` passes; headline axioms `propext, Classical.choice, Quot.sound`)

Three new files, imported from `Ideal.lean` (three `import` lines appended); no other existing Lean
file changed; no `sorry`/`axiom`/`native_decide`/`bv_decide`.

| file | lines | content |
|---|---|---|
| `Ideal/Direct/RomSim.lean` | 373 | the simulator, the ROM adversary, its budget, VCVio's bound for it |
| `Ideal/Direct/RomCompose.lean` | 120 | `epsHop`, the hop as a named statement, conditional composition |
| `Ideal/Direct/RomNumerics.lean` | 468 | coverage simplification, the three points, comparison with tight8 |

**The ROM side (unconditional).**  `Cr := core₀` (the repository's table-independent reference
core, `Realize/Chain.lean`; `Link.prims.core` would also do for VCVio but the realisers' open
programs, which the hop must be compared with, live over `core₀`).
`romS oR pkSeedDist := romScheme core₀ (Equiv.refl _) (optRandR oR) pkSeedDist` (`RomSim.lean:78`).
`IsRel` (`:104`), `relQ` (`:115`), `simStep` (`:157`), `simImpl` (`:172`), `simAdv` (`:186`) as
in §10.1 (dynamic rootedness through `Rooted.mdC`, narrow relevance, `arityOf` `:88`).
```
theorem simAdv_romQueryBound (S : ForgerI) (oR) (pkSeedDist) {qf qs : ℕ}            -- RomSim.lean:291
    (hqf : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isPortQ i = true) qf)
    (hqs : ∀ pk, IsQueryBoundP (S.main pk) (fun i => isSignQ i = true) qs) :
    (simAdv S oR pkSeedDist).RomQueryBound qf qs
theorem simAdv_suf_le … :                                                            -- RomSim.lean:346
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec Cr)) (simAdv S oR pkSeedDist) ≤
      securityBound Link.vp.params (256 ^ 16) 2 1 qf qs
theorem simAdv_euf_le … : unforgeableAdvantage (rom (hashSpec Cr)) (simAdvE S oR pkSeedDist) ≤ (same)
```
(`byteLaws₀`, `keyDiscipline₀` from `Concrete.keyDiscipline_sha2Primitives`, `natCard₀`.)

**Composition, conditional on the hop.**
```
def QAll qf qs ℓ := QcAll qf qs ℓ + 2 * Prf.qOPrf qs                                  -- RomCompose.lean:33
def epsHop qf qs ℓ := ((QAll qf qs ℓ + 1)^2 : ℕ) / 2^254 + qs / 2^128                -- :37
def MDHopSuf : Prop := ∀ S oR qf qs ℓ, hqf → hqs → hlong → hout →                     -- :41
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤
      strongUnforgeableAdvantage (rom (hashSpec Cr)) (simAdv S oR ($ᵗ (Bytes 16))) + epsHop qf qs ℓ
def MDHopEuf : Prop := (the same with eufI, unforgeableAdvantage, simAdvE)            -- :52
def epsRom qf qs ℓ := securityBound Link.vp.params (256^16) 2 1 qf qs + epsHop qf qs ℓ -- :63
theorem suf_rom_of_hop (hop : MDHopSuf) (S : ForgerI) oR hqf hqs hlong hout :          -- :67
    sufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ
theorem euf_rom_of_hop (hop : MDHopEuf) … : eufI S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs ℓ   -- :78
theorem sufP_rom_of_hop (hop : MDHopSuf) (S : ForgerP) … :                             -- :90
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ epsRom qf qs (ℓ + 257)
theorem eufP_rom_of_hop (hop : MDHopEuf) (S : ForgerP) … : eufP … ≤ epsRom qf qs (ℓ + 257)   -- :103
```
Same game objects and the same forger hypotheses (`hqf hqs hlong hout`) as
`suf_ideal_closed_tight8` / `suf_ideal_pure_closed_tight8`.

**Numerics (unconditional).**
```
theorem wTCB_le_simple (qs qw) (w) (hw : qw * w ≤ 1) :                                -- RomNumerics.lean:85
    weightedTargetCoverBound h a k qs qw w ≤ Σ_{r ≤ k} (r^k (qs+1)^r) / r! · 2^{-hr} 2^{-ak}
theorem epsRom_2_20 (hf : qf ≤ 2^60) (hs : qs ≤ 2^20) (hℓ : ℓ ≤ 2^26) :               -- :299
    epsRom qf qs ℓ ≤ (2^67)⁻¹ + (2^107)⁻¹
theorem epsRom_2_40 (hf : qf ≤ 2^64) (hs : qs ≤ 2^40) (hℓ) : epsRom … ≤ (2^63)⁻¹ + (2^87)⁻¹          -- :306
theorem epsRom_2_64 (hf : qf ≤ 2^64) (hs : qs ≤ 2^64) (hℓ) :                           -- :313
    epsRom … ≤ (2^63)⁻¹ + (2^64)⁻¹ + (2^66)⁻¹
theorem rom_lt_tight8_2_20 : (2^67)⁻¹ + (2^107)⁻¹ < (2^77)⁻¹ + (2^132)⁻¹ + (2^63)⁻¹   -- :332
theorem rom_lt_tight8_2_40 : (2^63)⁻¹ + (2^87)⁻¹ < (2^63)⁻¹ + (2^94)⁻¹ + (2^59)⁻¹     -- :341
theorem rom_lt_tight8_2_64 : (2^63)⁻¹ + (2^64)⁻¹ + (2^66)⁻¹ < (2^45)⁻¹ + (2^46)⁻¹ + (2^39)⁻¹  -- :350
```
and the point bounds under the hop: `suf_rom_2_20/_2_40/_2_64` (`:373–383`),
`euf_rom_2_*` (`:389–399`), `sufP_rom_2_*`, `eufP_rom_2_*` (`:417–448`, message parts
`ℓ + 257 ≤ 2^26`), e.g.
```
theorem sufP_rom_2_64 (S : ForgerP) oR hqf hqs hlong hout (hop : MDHopSuf)
    (hf : qf ≤ 2^64) (hs : qs ≤ 2^64) (hℓ : ℓ + 257 ≤ 2^26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ (2^63)⁻¹ + (2^64)⁻¹ + (2^66)⁻¹
```
**Every bound on `sufI`/`eufI`/`sufP`/`eufP` here takes `hop : MDHopSuf` (or `MDHopEuf`) as a
hypothesis.  The final theorem of the route is NOT proved.**  The proved (unconditional) bounds on
these games remain tight8's: 2^-63, 2^-59, 2^-39.

### 10.5 What remains: the hop `MDHopSuf` / `MDHopEuf`

Not started beyond the simulator.  Findings that fix its shape:

1. **No per-step coupling exists.**  In the real game the signer's internal chain cells are drawn
   at signing time and read by the forger later; in the ROM game they are drawn when the forger
   reads them.  A per-step until-bad (`Engine.prEvent_le_untilBad`, VCVio `UntilBad`) needs the
   projected steps to agree pointwise; a cached-but-unseen value against a fresh draw never does.
   The hop needs a **deferral** (lazy-sampling swap) argument.
2. **VCVio has that argument, but not for Merkle–Damgård.**
   `VCVio/OracleComp/QueryTracking/RandomOracle/Relabel.lean` (by-node relabelling of a lazy
   oracle, `prEvent_idealImpl_le_relabelImpl`, bad event `Conflict`) and `Defer.lean` (deferred
   touches, `prEvent_eagerImpl_le_deferredImpl`, via the commutation of lazy-oracle queries) are
   exactly the two steps needed, with nodes = rooted block lists and labels = chaining values.
   But `CanonicalGraph.pt_inj` requires distinct nodes to have distinct points **at all children
   values**; for MD, `pt (bs ++ [b]) [v] = (v, b) = pt (bs' ++ [b]) [v]`, so it fails.  The
   MD version must replace `pt_inj` by "no collision among drawn labels" and add the 256-bit events
   to `Conflict`.  Estimate 1.5–3k lines (VCVio's two files are 1.4k lines for the injective case).
3. **Core transport.**  The real game at table `g` is typed over `(primsG (liftC g)).core`
   (`PublicKeyCore`, `SignatureCore` are structures indexed by the core, so these types differ
   from `core₀`'s).  The repository already crossed this once: `Entry.sufI_le_lazy` gives the real
   game as ONE table-independent compression program `progS = progOf (chainP (bPrfWCOpenP …))`
   whose hash queries are those of an open program over `core₀` interpreted by
   `Realize/Chain.lean`'s chains.  So the hop should start from `progS`, not from `sufI`.

Decomposition (exact remaining statements, all over `core₀`):
```
H1 (exact; plumbing):  Pr[(simulateQ (hS St Blk).romImpl (progS S oR $ᵗ)).run' ∅] =
     Pr[ X S oR  under  (coins, port ↦ lazy table, hash queries ↦ chain evaluation in the SAME
         lazy table, PRF-oracle (pk, a) ↦ chain of thash pk (key a) [k]) ]
   where X S oR is the open SUF program (`bPrfWCOpenP` with its PRF key k drawn first).
H2 (the MD relabel/deferral core, generic in X):
   Pr_real[E] ≤ Pr_ideal[E] + Pr_real[Coll ∨ Ext]
   ideal = (coins, port ↦ simStep with T, hash queries ↦ lazy O, PRF-oracle ↦ O(thash … [k])),
   hypotheses: every hash query of the honest part of X is relevant for the pk it returns
   (`IsRel`: correct arity at PK.seed; `H_msg` at (PK.seed, PK.root); any `PRF_msg`), and the port
   is used only by the forger.  `Coll`: 256-bit events among the real run's cells;
   `Ext`: an honest/verifier relevant query whose block list extends the final cell of an earlier
   relevant query answered to the forger.
H3 (exact; plumbing): Pr_ideal[win] = strongUnforgeableAdvantage (rom (hashSpec core₀)) (simAdv S oR $ᵗ),
   through VCVio's `GeneralScheme.*_natural` lemmas (the open programs are the GeneralScheme
   programs read through a query morphism) and `romScheme_sign`/`_keygen`/`_verify`.
H4 (probability): Pr_real[Coll] ≤ (QAll+1)²/2^254 (budgeted hazard, `CollBudget.lean`, with the
   back-link flag of §9.1), Pr_real[Ext] ≤ qs/2^128 (`E_root`; each signer inner digest is a
   fresh 256-bit draw after PK.root; all other extensions need PK.seed/PK.root patterns, 2^-256).
```
`MDHopSuf` = `sufI_le_lazy` + H1 + H2 + H3 + H4; EUF the same with `progE` / `fresh_extract`
(no extraction is needed on this route: the win events are compared directly).

### 10.6 Updated estimate

Done this session: the analysis (10.1–10.3) and 961 lines of Lean (simulator, budget, VCVio
application, conditional composition, numerics, comparison).  Remaining for the unconditional
theorem: H1 0.4–0.8k, H2 2–3.5k (generic, reusable), H3 0.5–1k, H4 0.6–1k: **≈ 3.5–6k lines**,
below the 7–9k of the direct route's D4–D8 (§9.2) for a better bound.  `DagSwap.lean`,
`Extract*.lean` and `Bridge.lean` are not needed by this route; `Rooted.lean`, `CollBudget.lean`,
`Tagged.lean` (first-reader tags for `Coll`), `Engine.lean` are.

### 10.7 Bounds

| | P20 | P40 | P64 |
|---|---|---|---|
| proved (tight8, unconditional) | 2^-63 | 2^-59 | 2^-39 |
| proved **under `MDHopSuf`** (Lean point forms) | 2^-67 + 2^-107 | 2^-63 + 2^-87 | 2^-63 + 2^-64 + 2^-66 (= 2^-62.35) |
| exact formula (script, true surjection counts) | 2^-67.00 | 2^-63.00 | 2^-62.41 |
| generic floor | 2^-68.00 | 2^-64.00 | 2^-63.97 |

### 10.8 Verification (this session)

`lake build Ideal`: success.  `scripts/check.sh` (all default targets, generators, forbidden
tokens, axioms): `CHECK PASSED`, exit 0, no `FAIL` line.  `grep` for `sorry|axiom |native_decide|bv_decide`
in the three new files: only the `#print axioms` lines.  Every `#print axioms` of the new files:
`[propext, Classical.choice, Quot.sound]`.

---------------------------------------------------------------------------------------------

## 11. 2026-11-22 (fifth session): H1 and the Merkle–Damgård relabel/deferral core (H2, first half)

Six new files under `Ideal/Direct/` (1738 lines), six `import` lines appended to `Ideal.lean`; no
existing Lean file changed.
`lake build Ideal`: success (7443 jobs).  Every `#print axioms` of the new files:
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`axiom`/`native_decide`/`bv_decide`.
**`MDHopSuf` / `MDHopEuf` are NOT proved.  They are reduced to four smaller named statements
(11.3); no unconditional bound on `sufI`/`eufI`/`sufP`/`eufP` beyond tight8's is proved.**

### 11.1 Files

| file | lines | content |
|---|---|---|
| `Direct/LRelabel.lean` | 519 | VCVio's `CanonicalGraph` relabelling **without `pt_inj`** (copied from `VCVio/.../RandomOracle/Relabel.lean`, Apache 2.0, and generalised) |
| `Direct/LDefer.lean` | 334 | VCVio's touch deferral for the same graphs (copied from `.../RandomOracle/Defer.lean`, generalised) |
| `Direct/MDCore.lean` | 445 | the Merkle–Damgård graph, walks, **`md_core`**, what `Bad` means for MD |
| `Direct/MDToy.lean` | 49 | the core at `St = Blk = Bool` (small instance) |
| `Direct/MDSha.lean` | 178 | **H1**: `progS`/`progE` are walk programs answered by compression chains |
| `Direct/MDHop.lean` | 213 | `sufI ≤ deferred + 2·Bad`; the remaining statements; `MDHopSuf` from them |

Copied code: the graph part of VCVio's `Relabel.lean` (`childVals`…, `merge`, `Conflict`,
`LabelsComplete`, `relabelImpl`, the four step lemmas, the domination) and of `Defer.lean`
(`eagerImpl`, `deferredImpl`, `maskedImpl`, run equations, `intertwines_maskedFill`, the
domination, the deferral theorems).  The graph-independent state-level parts (`RelabelState`,
`drawCell`, `labelImpl`, `mask`, `revealCell`, `endFill`, `maskedFill`,
`evalDist_drawCell_bind_maskedFill`) are imported from VCVio, not copied.

### 11.2 Statements proved (file:line)

**Relabelling with non-injective points (generic).**  `LGraph pub X K R` (`LRelabel.lean:39`) is
`CanonicalGraph` with `pt_inj` replaced by `root_inj` (childless nodes have distinct points).
`PtColl st` (`:92`): two distinct nodes with drawn children have the same point; `Bad = Conflict ∨
PtColl` (`:192`), monotone (`Bad.mono :194`), false at `(∅, ∅)` (`not_bad_empty :198`).
```
theorem LGraph.dominatedUntilBad_relabelImpl :                                         -- LRelabel.lean:475
    QueryImpl.DominatedUntilBad G.relabelImpl (SecretEncoding.idealImpl pub X R) G.toSplitCache
      G.LabelsComplete G.Bad
theorem LGraph.prEvent_idealImpl_le_relabelImpl (oa) (P) :                            -- :502
    Pr{let z ← (simulateQ (SecretEncoding.idealImpl pub X R) oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.relabelImpl oa).run (∅, ∅)}[P (z.1, G.toSplitCache z.2) ∨ G.Bad z.2]
theorem LGraph.intertwines_maskedFill :                                                -- LDefer.lean:144
    QueryImpl.Intertwines RelabelState.maskedFill G.deferredImpl G.maskedImpl     -- exact, no hypothesis
theorem LGraph.prEvent_eagerImpl_le_deferredImpl_empty (oa) (P) :                     -- :321
    Pr{let z ← (simulateQ G.eagerImpl oa).run (∅, ∅)}[P z] ≤
      Pr{let z ← (simulateQ G.deferredImpl oa).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[P (z.1, st) ∨ G.Bad st]
```
Every use of `pt_inj` in VCVio's proofs is at a state off `PtColl` (the pre-state of a
`DominatedUntilBad` step, or a post-state restricted to `¬ Bad`).  The intertwining needs no
injectivity at all: the deferred and masked games choose the node at a point among the nodes
with drawn children of the same state, hence the same `Classical.choose`.

**The Merkle–Damgård core (H2, first half; generic in `St`, `Blk`, `IV`).**  Program interface
`OSp St Blk = unifSpec + Cell + WSp` (`MDCore.lean:56`): coins, compression queries, and **walk
queries** `List Blk →ₒ St` (an honest MD evaluation from `IV`, answered by the full final
chaining value).  `mdG IV` (`:74`): nodes `(b, rev)` = the block list `rev.reverse ++ [b]`, parent
`rev`, point `(label of the parent or IV, b)`.  `cellsR` (`:129`): walks by compression chains in
one lazy table; `labI` (`:140`): walks as label operations (`touch` every proper prefix, `read`
the full list, `walkL :123`).
```
theorem MD.walk_agree … :                                                              -- MDCore.lean:225
    (in the eager game, from a state off Bad with the walk's parent drawn)
    Pr{z ← eager-run (walkC c bs)}[Q z ∧ ¬Bad z.2] = Pr{z ← eager-run (walkL IV rev bs)}[Q z ∧ ¬Bad z.2]
theorem MD.real_eq_ideal (Y) (C D) :                                                  -- :273
    (simulateQ (SecretEncoding.idealImpl (Cell St Blk) Empty St)
        (simulateQ ((Cell St Blk).withDerivationsLift Empty St) Y)).run (C, D) =
      (fun z ↦ (z.1, (z.2, D))) <$> (simulateQ (Cell St Blk).romImpl Y).run C
theorem MD.md_core (X : OracleComp (OSp St Blk) α) (P : α → Prop) :                  -- :324
    Pr{let z ← (simulateQ (Cell St Blk).romImpl (simulateQ (cellsR IV) X)).run' ∅}[P z] ≤
      Pr{let z ← (simulateQ (mdG IV).deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
         let _st ← RelabelState.endFill z.2}[P z.1] + 2 *
      Pr{let z ← (simulateQ (mdG IV).deferredImpl (simulateQ (labI IV) X)).run ((∅, ∅), [])
         let st ← RelabelState.endFill z.2}[(mdG IV).Bad st]
theorem MD.ptColl_imp (h : (mdG IV).PtColl st) :                                     -- :407
    (∃ k k' v, k ≠ k' ∧ st.2 (.inr k) = some v ∧ st.2 (.inr k') = some v) ∨ ∃ k, st.2 (.inr k) = some IV
theorem MD.conflict_imp (h : (mdG IV).Conflict st) :                                  -- :430
    (∃ k v b, st.2 (.inr k) = some v ∧ (st.1 (v, b)).isSome) ∨ ∃ b, (st.1 (IV, b)).isSome
theorem MD.Toy.toy_core : … (md_core at St = Blk = Bool, a two-block honest walk and two
    forger queries)                                                                    -- MDToy.lean:36
```
Proof of `md_core`: real = VCVio's ideal (lazy) game with no derivations; relabelling
(`LRelabel`); the relabelled run of the compression chains equals the eager run of the label
operations until a point collision (`walk_agree`, VCVio's `AgreeUntilBad`); touch deferral
(`LDefer`).  The factor 2: one `Bad` from the agreement step, one from relabel + deferral.  One
statement covers every honest hash of SLH-DSA-SHA2: a two-stage hash (`H_msg`, HMAC) is a program
that issues its second walk on a block list computed from the first walk's answer.

**H1 (exact, proved).**
```
theorem Rom.progOf_chainA_eq (P : OracleComp (QSpec Rd Dsk) Bool) :                  -- MDSha.lean:140
    progOf (chainA P) = simulateQ (MD.cellsR IV128) (walkProg P)
theorem Rom.h1_suf : progS S oR pkSeedDist = simulateQ (MD.cellsR IV128) (XS S oR pkSeedDist)   -- :164
theorem Rom.h1_euf : progE S oR pkSeedDist = simulateQ (MD.cellsR IV128) (XE S oR pkSeedDist)   -- :170
```
An equality of programs (not only of distributions).  `XS` (`:72`) = the realisers' port program
`PprfS` with the PRF key drawn first and `Thash` = `out16` of the walk `sb128 pk :: tblocks a xs`,
`H_msg` = `dig30` of the walk `oblocksH R pk s`, `s` the walk `iblocksH R pk root M`, `PRF_msg` =
`out16` of the walk `[okey k, oblock s]`, `s` the walk `ikey k :: iblocks r M`, the PRF oracle =
`out16` of the walk `[sb128 pk, blk128 a k]` (`hashW :41`, `prfW :49`, `chainW :60`).

**Composition (proved).**
```
theorem Rom.suf_le_deferred (S oR pkSeedDist) :                                       -- MDHop.lean:60
    sufI S (optRandU oR) pkSeedDist ≤
      Pr{let w ← defRun (XS S oR pkSeedDist)}[w.1 = true] + 2 * Pr{let w ← defRun (XS …)}[Gs.Bad w.2]
theorem Rom.euf_le_deferred … (the same with eufI, XE)                                 -- :70
theorem Rom.epsHalf_add : epsHalf + epsHalf + qs/2^128 = epsHop                         -- :84
theorem Rom.mdHopSuf_of (hD : DeferSimSuf) (hB : BadSuf) : MDHopSuf                     -- :135
theorem Rom.mdHopEuf_of (hD : DeferSimEuf) (hB : BadEuf) : MDHopEuf                     -- :145
theorem Rom.suf_rom_of_parts, euf_rom_of_parts, sufP_rom_of_parts, eufP_rom_of_parts,
    sufP_rom_2_64_of_parts                                                              -- :157–194
```
(`defRun X` (`:40`) = the deferred game of `labI IV128 X` followed by the end fill; `Gs = mdG IV128`.)

### 11.3 Exact remaining statements (named `Prop`s in `Direct/MDHop.lean`, used as hypotheses)

```
def epsHalf qf qs ℓ := ((QAll qf qs ℓ + 1)^2 : ℕ) / 2^255                               -- MDHop.lean:82
def DeferSimSuf : Prop := ∀ S oR qf qs ℓ, hqf → hqs → hlong → hout →                     -- :94
    Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[w.1 = true] ≤
      strongUnforgeableAdvantage (rom (hashSpec Cr)) (simAdv S oR ($ᵗ (Bytes 16)))
        + epsHalf qf qs ℓ + qs / 2^128
def BadSuf : Prop := ∀ S oR qf qs ℓ, hqf → hqs → hlong → hout →                          -- :105
    2 * Pr{let w ← defRun (XS S oR ($ᵗ (Bytes 16)))}[Gs.Bad w.2] ≤ epsHalf qf qs ℓ
def DeferSimEuf, BadEuf : the same with XE, unforgeableAdvantage, simAdvE              -- :114, :125
```
In the decomposition of §10.5: H1 is proved; H2 is proved up to the deferred game (`md_core`);
what remains of H2 together with H3 is `DeferSimSuf`; H4 is `BadSuf` (collisions) plus the
`qs/2^128` (`E_root`) and the 256-bit residue inside `DeferSimSuf`.

* **`DeferSimSuf` (G4 + H3)**: the deferred game against VCVio's experiment of `simAdv`.  The
  deferred game still holds hidden information the ROM game does not: the full labels of
  honest-**read** nodes (the inner digests `X` of `H_msg` and HMAC, and the 128 / 16 hidden bits
  of every honest final label).  The forger's compression queries route through such a label
  (a guess) to a node, where the simulator sees an unrooted cell.  Both answer a fresh value; the
  correspondence breaks only when an honest walk later extends that node (`Ext`, §10.1: `E_root`,
  `qs/2^128`) or by a 256-bit coincidence.  The proof needs (i) a fill kernel from the ROM state
  to the deferred state that samples the hidden tails and inner digests (an `IntertwinesOn`, as
  in `LDefer`, but with partially revealed labels), (ii) the node ↔ cell correspondence of the
  simulator's dynamic rootedness (`Rooted.mdC`) with the drawn labels, (iii) the overlay
  `ovl(O(t), u)` ↔ final label, (iv) VCVio's `GeneralScheme` naturality lemmas for the game
  match (H3).  The budget `epsHalf + qs/2^128` is an allocation (half of epsHop's 256-bit term),
  NOT a derived value; the analysis of §10.1 predicts ≤ 2(Q+1)²/2^256 + qs/2^128 for this part.
* **`BadSuf` (H4, collisions)**: by `ptColl_imp`/`conflict_imp`, `Bad` at the filled state is a
  label collision, a label equal to `IV`, or a label equal to the chaining input of a cached
  non-node cell.  Every label is one fresh uniform 256-bit draw (in the deferred run or in the
  end fill), so the per-draw hazard is ≤ (#labels + #public cells + 1)/2^256 and `Pr[Bad] ≤
  (N+1)²/2^257` with `N` the number of cells, `2·Pr[Bad] ≤ (N+1)²/2^256 ≤ epsHalf` if `N ≤ QAll`.
  Needs: the budgeted-hazard engine (`CollBudget.ex_hz_le_of_step_cap`) on `deferredImpl` and on
  `endFill`, and the count `N ≤ QAll` transferred from `progS` (`Counts.lean`) to `defRun (XS …)`
  (each walk of `k` blocks draws at most `k` labels).

`epsHop` is unchanged (`epsHop = epsHalf + epsHalf + qs/2^128`, `epsHalf_add`), so
`RomNumerics.lean` is unchanged; no deviation from the predicted numbers.

### 11.4 Deviations

* H2 is split at the deferred game, not at the ROM game: the generic core is "real ≤ deferred +
  2·Bad", with `Bad` of the relabelling; the rest of H2 (the deferred game against the
  simulator) is merged with H3 in `DeferSimSuf`, because both compare the deferred state with the
  simulator's state `(T, O)`.
* `md_core` is generic in the honest computation: honest hashes are arbitrary programs over walk
  queries, so the two-stage `H_msg`/HMAC need no special case (§10.5 item 2 asked for an abstract
  "relevant final cell" predicate; relevance does not appear until `DeferSimSuf`).
* No `toy_real` evaluation: the small instance checks that `md_core` instantiates (`MDToy`); an
  attempted direct computation of the toy's real-game probability was abandoned (support
  bookkeeping of `randomOracle`, not informative).

### 11.5 Updated estimate

Done this session: 1738 lines (relabel/defer generalisation 853, MD core 445, H1 178,
composition 213, toy 49).  Remaining: `BadSuf`/`BadEuf` 0.5–0.9k (hazard engine on the deferred
game and the end fill, cell count transfer); `DeferSimSuf`/`DeferSimEuf` 1.5–3k (fill kernel for
the partially revealed labels, routing correspondence, overlay, `Ext`/`E_root` bound, game match
H3): **≈ 2–4k lines**.

### 11.6 Bounds

Unchanged.  Proved unconditional bounds: tight8's (2^-63, 2^-59, 2^-39).  Under `DeferSimSuf` and
`BadSuf` (instead of `MDHopSuf`): the §10.7 numbers (P20 2^-67 + 2^-107, P40 2^-63 + 2^-87, P64
2^-63 + 2^-64 + 2^-66 ≈ 2^-62.35), e.g. `sufP_rom_2_64_of_parts` (`MDHop.lean:194`).

### 11.7 Verification (this session)

`lake build Ideal`: success (7443 jobs).  `grep -nE "sorry|axiom |native_decide|bv_decide"` in the
six new files: only `#print axioms` lines.  All 22 `#print axioms` lines of the new files:
`[propext, Classical.choice, Quot.sound]`.  `scripts/check.sh` (all default targets, generators, forbidden
tokens, axioms, headline lists): `CHECK PASSED`, exit 0, no `FAIL` line.

---------------------------------------------------------------------------------------------

## 12. 2026-11-22 (sixth session): `BadSuf`/`BadEuf` proved, H3 proved, the remaining core isolated

Six new files under `Ideal/Direct/` (2525 lines), six `import` lines appended to `Ideal.lean`; no
existing Lean file changed.  `lake build Ideal`: success (7455 jobs).  No `sorry`/`axiom`/
`native_decide`/`bv_decide` in the new files (only `#print axioms` lines); every `#print axioms`
of the new files is `[propext, Classical.choice, Quot.sound]` except `MD.qb_labI`
(`[propext, Quot.sound]`).  `scripts/check.sh`: `CHECK PASSED`, exit 0, no `FAIL` line.

**Of the four named statements of §11.3, `BadSuf` and `BadEuf` are proved; `DeferSimSuf` and
`DeferSimEuf` are NOT proved.  They are replaced by strictly weaker statements, and those are
reduced (H3 proved) to two named statements `DeferCoreSuf`/`DeferCoreEuf`, which remain
hypotheses of every composed bound.  No unconditional bound on `sufI`/`eufI`/`sufP`/`eufP` beyond
tight8's is proved.**

### 12.1 Files

| file | lines | content |
|---|---|---|
| `Direct/MDBad.lean` | 648 | `BadSuf`, `BadEuf` (worst-case charge): bad sets, one draw, end fill, deferred game, query count |
| `Direct/MDBadSharp.lean` | 541 | sharp charge `Σ (i+1)/2^256`: `3·Pr[Bad] ≤ epsHalf`; `DeferSimSufNB`; hop from it |
| `Direct/RomGame.lean` | 366 | the tagged program `PprfST`, `untag_PprfST`, the ROM handler `romH`, `Yrom`; H3 and the core as `Prop`s |
| `Direct/RomMatch.lean` | 685 | **H3 proved** (`romGameSuf`, `romGameEuf`) |
| `Direct/RomFinal.lean` | 154 | the hop and all composed bounds under `DeferCoreSuf` / `DeferCoreEuf` |
| `Direct/RomCore.lean` | 131 | the core as one program under two handlers (`DeferCoreSufH`), equivalent |

### 12.2 Statements proved (file:line)

**H4, collisions (§11.3 `BadSuf`, `BadEuf`), proved.**
```
theorem MD.not_bad_draw (hb : ¬ Bad st) (k) (hu : u ∉ labV st) (hIV : u ≠ IV) (hc : u ∉ cfV st) :
    ¬ Bad (st.1, st.2.cacheQuery (.inr k) u)                                        -- MDBad.lean:182
theorem MD.not_bad_ro (hb : ¬ Bad st) (ht : ¬∃ k vs, childVals st k = some vs ∧ pt k vs = t) u :
    ¬ Bad (st.1.cacheQuery t u, st.2)                                               -- MDBad.lean:221
theorem MD.prEvent_draw_bad (hb : ¬ Bad st) c :
    Pr[Bad after drawCell c] ≤ (nV st + 1)/|St|                                     -- MDBad.lean:255
theorem MD.qb_labI X n : IsQueryBoundP (simulateQ (cellsR IV) X) isRight n →
    IsQueryBoundP (simulateQ (labI IV) X) isNU n                                    -- MDBad.lean:410
theorem MD.prBad_defRun_le X Q n (hn) (hnQ : n ≤ Q) : Pr[Bad] ≤ n · Q/|St|           -- MDBad.lean:546
theorem Rom.badSuf : BadSuf                                                         -- MDBad.lean:621
theorem Rom.badEuf : BadEuf                                                         -- MDBad.lean:629
```
(`nV st` = number of drawn label values + number of chaining inputs of cached public cells; a draw
fires `Bad` only on a value in `labV ∪ {IV} ∪ cfV`; cached public cells off the node points
create no `Bad`.  The end fill is charged through the pending charge of the capped
supermartingale `CollBudget.ex_hz_le_of_step_cap`.)

**Sharp form.**
```
theorem ex_hz_le_of_step_size … : ex (run) (hz P Ψ) ≤ hz P Ψ s + Σ_{i<n} ε (size s + i)   -- MDBadSharp.lean:34
theorem MD.prEvent_endFill_bad_sharp l st (hb) :
    Pr[Bad after endFill (st, l)] ≤ (Σ_{j<|l|} (nV st + j + 1))/|St|                -- MDBadSharp.lean:134
theorem MD.prBad_defRun_sharp X n (hn) : Pr[Bad] ≤ (Σ_{i<n} (i + 1))/|St|            -- MDBadSharp.lean:261
theorem Rom.bad3Suf … : 3 * Pr{let w ← defRun (XS S oR $ᵗ)}[Gs.Bad w.2] ≤ epsHalf qf qs ℓ   -- :332
theorem Rom.bad3Euf … (the same for XE)                                             -- :343
```
(pending charge `Σ_{j < #pending} (nV + j + 1)/|St|` = what the end fill costs from the current
state; every operation, touch or draw, costs `(dSize + 1)/|St|`, `dSize = nV + #pending`.)

**The remaining statement weakened (no change of `epsHop`).**
```
def DeferSimSufNB : Prop := ∀ S oR qf qs ℓ, hqf → hqs → hlong → hout →              -- MDBadSharp.lean:356
    Pr{let w ← defRun (XS S oR $ᵗ)}[w.1 = true ∧ ¬ Gs.Bad w.2] ≤
      strongUnforgeableAdvantage (rom (hashSpec Cr)) (simAdv S oR $ᵗ) + epsHalf qf qs ℓ + qs/2^128
theorem deferSimSufNB_of : DeferSimSuf → DeferSimSufNB                              -- :377
theorem mdHopSuf_of_nb : DeferSimSufNB → MDHopSuf                                   -- :389
theorem mdHopEuf_of_nb : DeferSimEufNB → MDHopEuf                                   -- :408
```
(`sufI ≤ Pr[win] + 2 Pr[Bad] ≤ Pr[win ∧ ¬Bad] + 3 Pr[Bad]`; `3 Pr[Bad] ≤ 3Q(Q+1)/2^257 ≤
(Q+1)²/2^255 = epsHalf`.)

**One typed program for both sides (RomGame.lean).**  `PprfST oR pkSeedDist S` (`:174`) is the
realisers' SUF port program with the forger's port tagged by the public key of the run
(`portQT pk q`); `untag_PprfST : simulateQ untagT (PprfST …) = PprfS …` (`:203`, an equality of
programs), so `XS = walkProg (simulateQ untagT PprfST)` (`XS_eq_untag :248`).  `romH k` (`:284`):
coins forwarded, `(pk, q) ↦ simStepR pk q` (the simulator's step on its table), PRF-game
`(PK.seed, a) ↦ Thash oracle (PK.seed, key a, [k])`, hash and `PRF_msg` queries to the oracles.
`Yrom S oR := k ← $; (simulateQ (romH k) (PprfST oR $ᵗ S)).run' ∅` (`:297`).

**H3, proved (RomMatch.lean).**
```
theorem Rom.keygen_romO k pkSeed : simulateQ (romO k) (openKeygenP Rd pkSeed) =
    keygenInternalWithSecretM Cr (oracleSecret Cr (Equiv.refl _) pkSeed k) pkSeed     -- RomMatch.lean:204
theorem Rom.sign_romO k skPrf oR pk m : simulateQ (romO k) (openSignP (optRand₀ oR) pk skPrf m) =
    (romS oR $ᵗ).sign pk ⟨k, skPrf, pk.pkSeed, pk.pkRoot⟩ m                             -- :215
theorem Rom.verify_romO …                                                            -- :233
theorem Rom.forger_phase … (the harness with the tagged port under romH = VCVio's logging signing
    run of the simulator, the two states swapped: swap_nest :254)                     -- :409
theorem Rom.romGameSuf : RomGameSuf                                                  -- :515
    -- ∀ S oR, strongUnforgeableAdvantage (rom (hashSpec Cr)) (simAdv S oR $ᵗ) =
    --          (rom (hashSpec Cr)).evalDist (Yrom S oR) {true}
theorem Rom.romGameEuf : RomGameEuf                                                  -- :669
```
(ledger congruence `keygenWS_congr :152`, `signWS_congr :170`: the honest programs read secrets
only at secret children of ledger addresses, which are in `SkDom`, where the restricted PRF game
and `oracleSecret` agree; the sample order `PK.seed, SK.seed` vs `SK.seed, PK.seed` by
`rom_swap :497`.)

**Composition (RomFinal.lean, RomGame.lean, RomCore.lean).**
```
theorem deferSimSufNB_of_parts : RomGameSuf → DeferCoreSuf → DeferSimSufNB          -- RomGame.lean:350
theorem mdHopSuf_of_core : DeferCoreSuf → MDHopSuf                                   -- RomFinal.lean:34
theorem mdHopEuf_of_core : DeferCoreEuf → MDHopEuf                                   -- RomFinal.lean:38
theorem suf_rom_core, euf_rom_core, sufP_rom_core, eufP_rom_core                     -- RomFinal.lean:50–105
theorem {suf,euf,sufP,eufP}_rom_2_{20,40,64}_core                                    -- RomFinal.lean:58–135
theorem defRun_eq_defH P s : deferred run of walkProg (untag P) = k ← $; (simulateQ (defH k) P).run s
                                                                                     -- RomCore.lean:70
theorem deferCoreSuf_iff_H : DeferCoreSuf ↔ DeferCoreSufH                            -- RomCore.lean:117
```
e.g.
```
theorem sufP_rom_2_64_core (S : ForgerP) oR hqf hqs hlong hout (hc : DeferCoreSuf)
    (hf : qf ≤ 2^64) (hs : qs ≤ 2^64) (hℓ : ℓ + 257 ≤ 2^26) :
    sufP S (optRandU oR) ($ᵗ (Bytes 16)) ≤ (2^63)⁻¹ + (2^64)⁻¹ + (2^66)⁻¹
```
**Every such bound takes `DeferCoreSuf` (or `DeferCoreEuf`) as a hypothesis; NOT the final theorem.**

### 12.3 Exact remaining statements

```
def DeferCoreSuf : Prop := ∀ S oR qf qs ℓ, hqf → hqs → hlong → hout →                -- RomGame.lean:327
    Pr{let w ← defRun (walkProg (simulateQ untagT (PprfST oR ($ᵗ (Bytes 16)) S)))}[
        w.1 = true ∧ ¬ Gs.Bad w.2] ≤
      (ProbCompRuntime.rom (hashSpec Cr)).evalDist (Yrom S oR) {true} + epsHalf qf qs ℓ + qs/2^128
def DeferCoreEuf : Prop := (the same with PprfET, YromE)                              -- RomGame.lean:339
```
Equivalently (`deferCoreSuf_iff_H`) `DeferCoreSufH` (`RomCore.lean:88`): ONE program `PprfST`
under the two handlers `defH k = deferredImpl ∘ labI ∘ chainW k ∘ untagT` (deferred labels) and
`romH k` (lazy oracles + simulator), the end fill on the deferred side, `k ← $` on both.
Given the proved H3, `DeferCoreSuf` is equivalent to `DeferSimSufNB`, which is implied by §11's
`DeferSimSuf`.  It contains exactly the probabilistic content of §11.3 items (i)–(iii) and the
`Ext`/`E_root` bound; the game match (iv) is done.

What its proof needs (unchanged from §11.3 except (iv)): a coupling of `defH k` with `romH k` on
the same program — most naturally `Engine.prEvent_le_untilBad` with `h₁ = defH k` and
`h₂ = romH k` extended by a ghost copy of the hidden label parts (tails of honest final labels:
16 bytes for `Thash`/`PRF_msg`, 2 for `H_msg`; full inner digests), the simulator's fresh value
replaced by the ghost value when it fills an honest node; then ghost elimination (an
intertwining as in `LDefer`) to recover `romH k`.  Bad events beyond `Gs.Bad` (which may now be
assumed false, monotone): 256-bit coincidences of the simulator's table values with labels
(within `epsHalf`), and `E_root` (`qs/2^128`).

### 12.4 Deviations

* `BadSuf` is proved twice: worst-case (`MDBad.badSuf`, the §11 statement) and sharp
  (`MDBadSharp.bad3Suf`, `3·Pr[Bad] ≤ epsHalf`).  The sharp form pays for the `¬Bad` conjunct in
  the remaining statement at no cost in `epsHop`.
* **`epsHalf`, `epsHop` are unchanged** (so `RomNumerics.lean` and its numbers are unchanged).
  The collision part's true value is `Pr[Bad] ≤ Q(Q+1)/2^257` (Q = `QAll`), a quarter of the
  `epsHop` allocation `(Q+1)²/2^254`; the derived split is now `3·Pr[Bad] ≤ (Q+1)²/2^255` plus
  the core's `(Q+1)²/2^255 + qs/2^128` (still an allocation for the core, not a derived value).
* The ROM-side simulator is unchanged (`simAdv`); the ROM-side game `Yrom` is the tagged realiser
  program under `romH`, and H3 shows it IS VCVio's experiment (no inequality).
* The remaining statement is now about `walkProg (untag PprfST)` (= `XS`, an equality of
  programs) rather than `XS`, so that both sides are one program.

### 12.5 Updated estimate

Done this session: 2525 lines (collision bound 1189, tagged program and H3 1051, composition and
the two-handler form 285).  Remaining: `DeferCoreSuf`, `DeferCoreEuf`: the coupling of `defH`
with `romH` (state relation between the deferred labels and the simulator's table under dynamic
rootedness; the ghost tails and inner digests and their elimination; the per-query step for
the four honest query kinds and the tagged port; `E_root`; SLH-DSA block-structure facts:
honest walks do not extend honest final nodes except `E_root`) — **≈ 2–3.5k lines**, the EUF twin
a few hundred more by reuse (same handlers; only the final check differs).

### 12.6 Bounds

Unchanged.  Proved unconditional: tight8's (2^-63, 2^-59, 2^-39).  Under `DeferCoreSuf` alone:
P20 2^-67 + 2^-107, P40 2^-63 + 2^-87, P64 2^-63 + 2^-64 + 2^-66 (≈ 2^-62.35), each below tight8
(`rom_lt_tight8_2_20/_40/_64`, `RomNumerics.lean:332–350`).

### 12.7 Verification (this session)

`lake build Ideal`: success (7455 jobs).  `grep -nE "sorry|axiom |native_decide|bv_decide"` in the
six new files: only `#print axioms` lines.  `#print axioms` of the new files: all
`[propext, Classical.choice, Quot.sound]` (`MD.qb_labI`: `[propext, Quot.sound]`).
`scripts/check.sh` (all default targets, generators, forbidden tokens, axioms, headline lists):
`CHECK PASSED`, exit 0, no `FAIL` line.
