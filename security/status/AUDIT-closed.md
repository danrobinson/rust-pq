# AUDIT-closed — independent audit of the closed ideal-compression headlines

Scope: `Ideal.suf_ideal_closed`, `Ideal.euf_ideal_closed`, the six numeric corollaries
(`Ideal/Realize/Final.lean:74-195`) and `Ideal.rust_ideal_security_closed`
(`Ideal/RustFinalClosed.lean:34-89`). I checked statements and definitions, not proofs (the
kernel checks those). Scratch files: `scratch/ideal/audit/A1.lean` to `A4.lean`. All compile with
`lake env lean`. Every `.olean` in `Ideal/ Reduction/ Link/ E2E/` is newer than its source, and the
VCVio checkout is clean at `a10530a`.

**Verdict: the claim holds as stated, with the caveats below. I found no category-A finding.**

## 1. The game (checked)

- `sufI S optRand pkSeedDist = cfAdvantage fun g => strongUnforgeableExperiment (S.sufInst … g)`
  (`Compose.lean:196`). `cfAdvantage X = 𝒟[do g ← $ᵗ (CF St Blk); X g] {true}`
  (`Inst/WotsPre128.lean:102`). So the probability is over a fresh table **and** the game's coins.
- The table is uniform. `CF St Blk = Bytes 32 × Bytes 64 → Bytes 32` (`Core/Defs.lean:28`,
  `Sha/Instantiate.lean:21-31`). VCVio's `SampleableType` class has a proof field
  `evalDist_selectElem_eq_uniform` (`VCVio/…/SampleableType/Basic.lean:51-57`), so *any* instance is
  uniform. The instance used is `Ideal.instSampleableTypeCFStBlk` (A1 `#synth`; A3 `#check`).
- The forger and the scheme use the same table. `sufInst g` has
  `main pk := simulateQ (instImpl g) (S.main pk)` (`Compose.lean:174-176`, `rfl` in A3).
  `instImpl g` answers `.inr (.inl q)` with `pure (g q)` and forwards everything else
  (`Core/Defs.lean:54-58`). The scheme is
  `bytesAlg Link.vp (primsG (liftC g)) (codecG g) …`. Here `sha2PrimitivesG c` evaluates every
  SHA-256 call through `c` (Thash, PRF, HMAC-based PRF_msg, MGF1/H_msg;
  `Sha/Generic.lean:24-123`), and `liftC g st m base = decSt (g (encSt st, blkAt m base))`
  (`Instantiate.lean:109`). `ForgerI` (`Compose.lean:163-165`) is a single program with no `g` in
  its type.
- Signing and verification are the real scheme over `g`. `bytesAlg.sign` draws
  `addrnd ← optRand k` and returns `byteSign m sk addrnd`. `verify` is `byteVerify`
  (`Reduction/Bytes.lean:441-454`). The scheme is perfectly complete at every table (A3:
  `Reduction.bytesAlg_perfectlyComplete` at `primsG (liftC g)`), so verification is not trivially
  false.
- The winning conditions are VCVio's standard ones (`SignatureAlg.lean:222-227, 338-344`):
  - SUF: `!signingLogContains log msg σ && verified`;
  - EUF: `!log.wasQueried msg && verified`.
- The keys are distributed correctly. `pkSeedDist = $ᵗ (Bytes 16)` is uniform. `SK.seed` and
  `SK.prf` are drawn with `$ᵗ` over `Bytes 16`.
- `optRandU oR g pk = oR pk.pkSeed pk.pkRoot` (`ComposeFinal.lean:314`), with `oR` fixed and
  independent of `g`. It covers the deterministic variant (`fun s _ => pure s`) and the hedged
  variant (`fun _ _ => $ᵗ _`). It cannot depend on `SK` or the message.

## 2. The hypotheses (checked)

- `isPortQ`, `isSignQ` and `isLongQ ℓ` (`Realize/Port.lean:94-106`) match the compression index,
  any signing index, and a signing index with `ℓ < m.length`, respectively.
- `IsQueryBoundP` (`VCVio/…/QueryBound/Basic.lean:230`) is a syntactic, worst-case bound over
  every path of the free-monad tree, with every possible oracle answer.
- `hout` quantifies over `support (S.main pk)`, which also ranges over all oracle answers.
- `#check` with `pp.explicit` (A4) shows no instance or typeclass binders, and none of the
  definitions takes a default argument.
- `hQ : QcAll qf qs ℓ ≤ 2^126` is plain arithmetic, with
  `QcAll = qf + (qs+1)(2^25 + 2⌊(ℓ+56)/64⌋)` (`FinalCore.lean:33`).
- Uniform-sampling queries of the forger are unbounded, as is standard. The forger is
  computationally unbounded; only its oracle queries are counted.

## 3. Non-vacuity (done; `scratch/ideal/audit/A1.lean`, `A2.lean`)

- `F0` has `main _ := pure ([], [])`. `suf_ideal_closed_2_20` applies at `qf = qs = ℓ = 0`.
- `F1` makes one compression query at `(0, 0)`. It then makes one signing query on the 1-byte
  message `[c[0]!]`, which depends on the answer `c`, and outputs `([1], s)`.
  - All four hypotheses are proved at `qf = qs = ℓ = 1`.
  - `suf_ideal_closed_2_20`, `euf_ideal_closed_2_64` (with `oR = fun s _ => pure s`) and the
    general `suf_ideal_closed` (with `hQ` by `norm_num`) all apply.
- Sanity checks (A2): the counts are real.
  - `¬ IsQueryBoundP (F1.main pk) isPortQ 0` and `¬ … isSignQ 0` are provable.
  - A signing query on a 2-byte message is provably not `isLongQ 1`-free.

## 4. The bound

I computed the bound exactly in Python. The ITSR `reuseSum 63 12 14 n` is evaluated through
Stirling numbers.

| point | ITSR reuse | ITSR sq. | `66·QcAll/2^128` | `polyP/2^256` | total | stated |
|---|---|---|---|---|---|---|
| `qf=2^60−2^46, qs=2^20, ℓ=2^26` | 2^-95.5 | 2^-132.9 | 2^-62.0 | 2^-79.9 | 2^-62.0 | 2^-70+2^-128+2^-61 |
| `qf=2^64, qs=2^40, ℓ=2^26` | 2^-69.7 | 2^-94.1 | 2^-56.3 | 2^-79.9 | 2^-56.3 | 2^-50+2^-88+2^-41 |
| `qf=2^64, qs=2^64, ℓ=2^26` | 2^-47.1 | 2^-46.1 | 2^-32.9 | 2^-70.5 | 2^-32.9 | 2^-44+2^-43+2^-31 |
| `qf=qs=ℓ=0` | — | — | 2^-97 | 2^-79.9 | 2^-79.9 | — |

- **The numeric corollaries match the informal table.** For example, `hf : qf + 2^46 ≤ 2^60` is
  `qf ≤ 2^60 − 2^46`. Each stated number is at least the exact general bound.
- **The bound is far below 1 at all three points.**
- **Where it becomes vacuous:**
  - The ITSR leg exceeds 1 once `qf + 2qs ≳ 2^69.9` (for example, 2^0.96 at `qf = 2^70`).
  - The class-TCR leg exceeds 1 once `QcAll ≳ 2^122`.
  - Because `QcAll ≥ (qs+1)·2^25`, the signing count enters every leg.

## 5. The realisers (spot-checked; not soundness-critical)

The headline's statement mentions only `sufI` and arithmetic. The realisers are constructed terms
inside the proof, not hypotheses, so they cannot weaken the statement. I still spot-checked two:

- **Class TCR (`Realize/TcrCount.lean:266-278`):**
  - `A := advT S oR pkSeedDist n` is built with no `g` in scope.
  - `instRT A g` answers queries via `simulateQ (instImpl g)` / `instImpl₀ g`
    (`Inst/TcrTight128.lean:79-84`).
- **ITSR:** `RealizesItsrF.A` is a structure field outside `∀ g` (`ComposeFinal.lean:64`).
  `instImplF IV g` answers raw queries by `g q` and chain queries by `mdFold g IV bs`
  (`Games/ItsrFine.lean:57-63`).
  - Raw and chain queries are bounded separately: `hq` and `hqP` with `qf`, `hqc` with
    `itsrQc qs`, and `hLc` caps the chain length.
  - The bound charges chain queries via `qc·Lc` and the `secondP` ones via `cP = 2qs`.

In both, `g` reaches the program only through the oracle.

## 6. The Rust link (`RustFinalClosed.lean:34-78`)

- **Conjunct 1:** the Aeneas `slh_keygen_internal`, `slh_sign_internal` and
  `slh_verify_internal` equal `byteKeygen`, `byteSign` and `byteVerify` at `Link.prims` (real
  SHA-256), under `Room m.length 152` (`len + 152 ≤ Usize.max ∧ < 2^61`).
- **Conjunct 2:** `bytesAlg … (primsG (liftC realCF)) (codecG realCF) (optRandU oR realCF)` equals
  `bytesAlg … Link.prims codec128s (fun pk => oR pk.pkSeed pk.pkRoot)`.
- **Conjunct 3:** the ideal-model bounds hold for the family `g ↦ bytesAlg … (primsG (liftC g))`.

**What this connects.** The scheme in conjunct 3 is the same family that conjunct 2 evaluates at
`g = realCF`, and conjunct 1 is about the cores of that scheme at `realCF`.

**What it does not connect.**
- Conjunct 3 averages over uniform `g`. `realCF` is one point of measure about `2^-(2^776)`.
  Nothing is said about the real SHA-256.
- Seed sampling and `opt_rand` sampling are not Rust code. The Rust functions take
  `sk_seed`, `sk_prf`, `pk_seed` and `addrnd` as inputs.
- Only the `_internal` Rust functions are linked.

## 7. Axioms and placeholders

- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all nine headline names
  (A1). This excludes `sorryAx`, `Lean.ofReduceBool` (so no `native_decide` or `bv_decide`) and
  any custom axiom in the whole cone.
- A grep of `Ideal/ Reduction/ Link/ E2E/ ../lean/Slhdsa` for `sorry`, `axiom`, `unsafe`,
  `implemented_by`, `@[extern]`, `opaque`, `notation`, `macro`, `syntax` and `elab_rules` found
  only `local notation "Abase"` / `"Aset"` in `Ideal/Transport/Adv*.lean`. Those are proof-side
  files, not used in any headline statement. It also found `maxRecDepth 2048` in the Aeneas
  extraction, which is harmless.
- The headline statements were re-elaborated from my own file (A4, `pp.explicit`) and use only
  VCVio's standard `$ᵗ` and `𝒟[·]`.

## Findings

**(A) False or materially overstated: none.**

**(B) Caveats the claim should carry.**

1. **Internal interface only; context-based pure mode is not covered.**
   - The scheme is `Reduction.bytesAlg`, the internal interface (Alg. 18-20), where the forger
     signs arbitrary `M'` (`Bytes.lean:441`).
   - `pureBytesAlg` (Alg. 22/24, with context) does not appear anywhere in `Ideal/`, and only the
     `_internal` Rust functions are linked.
   - If "pure mode" is read as `slh_sign`/`slh_verify` with `ctx`, no theorem covers it, although
     it would follow by an easy injective-encoding reduction.
2. **The model is a random function on `St × Blk`, which is stronger than SHA-256 actually is.**
   SHA-256's compression is Davies–Meyer over a block cipher, which has easily found fixed
   points. The model excludes such structure, so conjunct 3 is a heuristic statement about
   real SHA-256 (as the file says, `RustFinalClosed.lean:21`).
3. **Output length cap.** `hout` excludes forgers that output a message longer than `ℓ`. The
   numeric points cap `ℓ` at `2^26` bytes. Longer forgeries need the general theorem at a larger
   `ℓ`, which enlarges `QcAll`.
4. **The bound at many signatures is weak.**
   - At `qs = 2^64` the bound is about `2^-31`, dominated by `66·QcAll/2^128` with
     `QcAll ≈ 2^89`: every signature is charged `2^25` compression calls.
   - The bound never drops below about `2^-80`, even for a forger that makes no queries
     (`NAll ≥ 2^81` in `polyP`).
   - It is vacuous once `qf + 2qs ≳ 2^70`.
5. **Randomness and the wrapper are not covered by the Rust link.** Key-seed generation and
   `opt_rand` sampling are modelled (uniform seeds, `oR`), not verified Rust code (see §6).

**(C) Cosmetic.**
- `Ideal.lean` does not import `Ideal.Realize.Final` or `Ideal.RustFinalClosed`, so the default
  `lake build` does not check the headlines (`R-final.md`). The `.olean` files are present and
  fresh.
- `IDEAL_STATUS.md` and `Ideal/HANDOFF.md` still describe the twelve realiser hypotheses.
- `hout`, `hqf`, `hqs` and `hlong` hold over all oracle answers, including answers inconsistent
  with any table. This is stronger than needed but harmless.

## What is proved, in plain English

Let the SHA-256 compression function be replaced by a uniformly random function
`g : {0,1}^256 × {0,1}^512 → {0,1}^256`, used for every SHA-256 call of SLH-DSA-SHA2-128s
(Thash, PRF, HMAC-SHA-256 PRF_msg, MGF1-SHA-256 H_msg).

Fix any `opt_rand` sampler `oR(PK.seed, PK.root)` that does not use `g`. Take any computationally
unbounded forger, given as one oracle program, that receives the 32-byte public key and:

- on every execution path makes at most `qf` queries to `g` and at most `qs` signing queries,
  each signing query on a message of at most `ℓ` bytes, to the **internal** byte-level signing
  oracle (`slh_sign_internal` semantics, `addrnd ← oR`);
- outputs a message of at most `ℓ` bytes together with a byte string.

The probability is taken over `g`, uniform `PK.seed`, `SK.seed` and `SK.prf`, the sampled
`opt_rand` values and the forger's coins. The forger's output must verify under `byteVerify`
over `g`. The SUF (resp. EUF) probability is that the output (message, signature) pair (resp.
message) was never returned by (resp. submitted to) the signing oracle. That probability is at
most

`epsItsrF … + (66·QcAll+40)/2^128 + polyP(…)/2^256`, provided `QcAll ≤ 2^126`.

In particular:

| forger caps | SUF and EUF bound |
|---|---|
| `qs ≤ 2^20`, `qf ≤ 2^60 − 2^46`, `ℓ ≤ 2^26` | `2^-70 + 2^-128 + 2^-61` |
| `qs ≤ 2^40`, `qf ≤ 2^64`, `ℓ ≤ 2^26` | `2^-50 + 2^-88 + 2^-41` |
| `qs ≤ 2^64`, `qf ≤ 2^64`, `ℓ ≤ 2^26` | `2^-44 + 2^-43 + 2^-31` |

Separately:
- the Aeneas translations of the Rust `_internal` functions compute this scheme's deterministic
  cores at the **real** compression function, for messages with `len + 152 < 2^61`;
- the ideal-model family evaluated at the real compression table is that real scheme.

Nothing is proved about the real compression function's security, nor about the context-based
`slh_sign`/`slh_verify` interface.

## What I did not check

- Proofs (left to the kernel).
- That the Aeneas extraction faithfully reflects the Rust source.
- That `Link.prims` and `byteSign`/`byteVerify` match FIPS 205 byte for byte. Earlier audits
  covered this; I relied on `sha2PrimitivesG_compress` being `rfl` to VCVio's FIPS bundle and did
  not re-read that bundle.
- That VCVio's `evalDist` semantics are correct.
- The ten realisers other than class TCR and ITSR (not soundness-relevant, see §5).
- Tightness of the bound.


> **Coordinator note (2026-11-21).** The category-C point above that `Ideal.lean` does not import
> `Ideal.Realize.Final` or `Ideal.RustFinalClosed` is not accurate: both are imported
> (`Ideal.lean` lines 90 and 122) and were covered by the full `lake build` (8035 jobs).
