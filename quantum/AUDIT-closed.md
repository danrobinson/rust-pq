# Audit: `slhdsa_sha2_128s_pure_bytes_{suf,euf}_cma_qrom_enc_closed` (and `_num`)

Auditor's scope: the statements and definitions only. Lean's kernel checks the proofs. Everything
here was read from source. The claims about axioms, instance arguments and non-vacuity were also
checked by compiling scratch files: `quantum/scratch/audit/Axioms.lean` and
`quantum/scratch/audit/NonVac.lean`. Both were compiled with plain `lean` against the existing
integration oleans; no olean was written, and none of those oleans is older than its source.

## Verdict

The informal claim is **correct as stated**. I found no category-A problem: nothing is false or
materially overstated. There are several category-B caveats that a careful statement should
carry; they are listed below.

## The statement that is actually proved (as elaborated, `#check @…`)

```
∀ {E : Type} [Fintype E] [DecidableEq E] (c : Caps)
  (optRand₀ : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (pkSeedDist₀ : ProbComp (Bytes 16))
  (F : PortForger (EncX c) EncY E) (q qs : ℕ),
  (∀ pk, CountBound isPort (F.main pk) q) → (∀ pk, CountBound isSign (F.main pk) qs) →
  (∀ pk, AllQueries (capIdx c) (capOut c) (F.main pk)) → 35 ≤ c.tl →
  avΩ c (fun ω ↦ qStrongUnforgeableAdvantage (F.at (encΩ ω) (algΩ c optRand₀ pkSeedDist₀ ω)))
    ≤ composedBoundFinal q qs (openCounts128s qs).noPrfMsg
```

The EUF version is the same with `qUnforgeableAdvantage`. The only binders are the ones shown.
They come from the section variables `{E} [Fintype E] [DecidableEq E] (c) (optRand₀)
(pkSeedDist₀)` at `SlhDsaComposedClosed.lean:47-49`, and the theorem arguments at `:64-71` and
`:93-100`. No hypothesis is hidden in a structure field: the only `Prop` fields of `PortForger`
are `posSemidef` and `trace_eq_one` of the initial state. Global instances are used, but they
carry data, not assumptions:

- `encXDecEq`, which is `Classical.decEq`, at `SlhDsaBridgePrf.lean:72`;
- `bytesGroup`, bytewise addition mod 256, at `:56`;
- the classical `Fintype (FinFns p c)` at `SlhDsaRandomFinite.lean:84`.

Axioms of the four headline names and of `Num.composedBoundFinal_num` are exactly `[propext,
Classical.choice, Quot.sound]`. This was checked in `scratch/audit/Axioms.lean`.

### Unfolding the left-hand side

- **`avΩ c f = ∑ ω, (card Ω128 c)⁻¹ * f ω`** (`SlhDsaComposed.lean:70`). `Ω128 c = FinFns
  Link.vp.params c` (`SlhDsaRandomFinite.lean:148`). That type is a structure of four function
  fields (`:64-68`):
  - `thash : Bytes 16 → Bytes 22 → BList (Bytes 16) c.tl → Bytes 16`
  - `hmsg : Bytes 16 → Bytes 16 → Bytes 16 → BList Byte c.ml → Bytes 30`
  - `prf : Bytes 16 → Bytes 16 → Bytes 22 → Bytes 16`
  - `prfMsg : Bytes 16 → Bytes 16 → BList Byte c.ml → Bytes 16`

  Its `Fintype` instance is transported from the product of the four function spaces (`:71-93`).
  So the uniform average over it is four independent uniformly random functions on these bounded
  domains.
- **The scheme at world ω.** `algΩ c optRand₀ pkSeedDist₀ ω = pureBytesAlg Link.vp (primsΩ ω)
  (codecR ω.toRand) (optRandOf c optRand₀ ω) pkSeedDist₀` (`SlhDsaComposed.lean:402-403`).
  - `primsΩ ω = randPrims ω.toRand` (`SlhDsaRandomFinite.lean:151`).
  - `randPrims f` (`SlhDsaRandom.lean:50-61`) is field-for-field VCVio's `sha2Primitives`
    (`.tools/VCVio-upstream/HashSig/SLHDSA/Concrete/FIPS.lean:282-293`): the same carriers
    (`Bytes n`), `adrsToKey = sha2AdrsKey`, `yToBytes = id`. Only `Thash`, `PRF`, `PRFmsg` and
    `Hmsg` are replaced.
  - `codecR` is `codec128s`, field by field (`SlhDsaRandom.lean:70-71`).
  - `pureBytesAlg` (`security/Reduction/Bytes.lean:467-488`) is the same generic definition that
    the standard-model theorem `slhdsa_pure_bytes_suf_cma` (`Bytes.lean:905`) instantiates at
    `Link.prims`. Key generation is `PK.seed ← pkSeedDist₀`, with `SK.seed` and `SK.prf` uniform
    (`$ᵗ`, uniform by the `SampleableType` class). Signing of `(M, ctx)` returns `none` if
    `|ctx| > 255`; otherwise it draws `opt_rand ← optRand₀ PK.seed PK.root` and returns
    `byteSignPure`. Verification is `byteVerifyPure` on `some sig`, and `none` is rejected.
  - So "pure bytes" means FIPS 205 Alg. 21/22/24 (external pure interface, context strings,
    `M' = 0 ‖ |ctx| ‖ ctx ‖ M`) on byte strings with the FIPS 205 wire codec. This is the
    `security/` scheme, not a simplified variant.
- **The experiment.** `qStrongUnforgeableAdvantage Q = qWeight (· = true)
  (qStrongUnforgeableExperiment Q) Q.ρ₀` (`PQ/Interactive/EUFCMA.lean:109`). The experiment
  (`qSigExperiment`, `:87-92`) runs as follows:
  1. classical key generation;
  2. the quantum machine runs against `signImpl` (`:28-31`), where uniform sampling is forwarded
     and each signing query is answered by `sigAlg.sign pk sk m` and logged;
  3. classical verification;
  4. freshness: SUF requires `!signingLogContains log msg σ`, EUF requires `!log.wasQueried msg`.

  The win condition is the standard SUF / EUF one with the real verifier, and messages are
  `(M, ctx)` pairs. `qUnforgeableAdvantage_eq` (`:146`) shows this equals VCVio's classical
  `unforgeableAdvantage` for forgers with rational Born probabilities. That is a sanity anchor
  for the semantics.
- **The forger.** `PortForger X Y E` (`SlhDsaComposed.lean:367-376`) has three parts:
  - `main : List Byte → QOC ((X×Y)×E) (portSpec + (unifSpec + ((List Byte × List Byte) →ₒ Option
    (List Byte)))) ((List Byte × List Byte) × Option (List Byte))`;
  - an arbitrary initial density matrix `ρ₀` on `WS X Y E = ((X×Y)×E) × Unit`;
  - `E` is an arbitrary finite type.

  `QOC` nodes are arbitrary lossless instruments on the workspace (`Model.lean:37-46`), port
  calls, uniform sampling, and classical signing queries.

  `F.at H` (`SlhDsaComposed.lean:379-387`) sets `main pk := compileQ H (F.main pk)`.
  `compileQ` (`QromBridgeSpec.lean:28-39`) replaces each port call by `portIdx H` and frames the
  instruments; signing and sampling queries are kept. `F` is one syntactic object: nothing in it
  depends on ω. So the forger's only access to ω is the port unitary and the signing oracle.

### The oracle model

- **One port call is `portStep H`** (`QromBridge.lean:166-186`), which is VCVio's
  `additiveOracleRuntime H` `queryStep`. That is `oracleUnitary H = basisMatrix (m ↦ (m.1, m.2 +
  H m.1))` (`QuantumFoundations/Oracle/Unitary.lean:52-97`), acting on the `X × Y` factor:
  `|x, y⟩ ↦ |x, y + H x⟩`.
- **The combined function is `H = encΩ ω`** (`SlhDsaBridgePrf.lean:66-83`). `EncX c` is the
  disjoint union of the four bounded domains, so one call can be in superposition across all
  four components. `EncY = Bytes 16 × Bytes 30`, where `+` is bytewise addition mod 256. The
  `n`-byte components are written to the first coordinate and `H_msg` to the second; the other
  coordinate gets `+0`.
- **Outside the caps.** `FinFns.toRand` (`SlhDsaRandomFinite.lean:100-104`) extends `thash`,
  `hmsg` and `prfMsg` by `default` (a constant) outside the caps, and precomposes `prf` with
  `sha2AdrsKey`. So the scheme at ω is "SLH-DSA with random functions within the caps and fixed
  constants outside". The forger's port covers exactly the random part; it knows the constant
  part.

### The hypotheses

`CountBound` and `AllQueries` (`QromBridgeSpec.lean:42-54`) are defined by structural recursion
over the control tree. They quantify over every answer at every node, so they hold "on every
path, whatever the answers":

- `isPort` holds exactly at port calls (`:56-58`).
- `isSign` holds exactly at signing queries (`SlhDsaComposed.lean:346-348`).
- `capIdx c` requires `|M| + |ctx| + 2 ≤ c.ml` on each signing query (`:356-358`).
- `capOut c` requires the same of the forgery's `(M, ctx)` (`:361-362`).

Uniform-sampling nodes and instrument nodes are not counted. `c.ml` is otherwise arbitrary, and
`c.tl` only needs `35 ≤ c.tl`. 35 is the largest `Thash` arity of the parameter set:
`len = 35`, `k = 14`.

### The bound

- **Definition.** `composedBoundFinal q qs r` (`SlhDsaComposedFinal.lean:375-381`) is
  `epsPrf(q+r.prf) + epsPrf(q+r.msg) + epsItsr(q+r.itsr, qs) + epsDsprTight(q+r.dspr) +
  3·epsTcr0(q+r.tcrFv) + epsTcr0 at tcr1, tcr2, tcrLen and tcrK + 14·epsUdTight(q+r.ud) +
  epsPre0(q+r.pre) + epsTcr0(q+r.tcrT)`. Here `w − 2 = 14`.
- **The term shapes:**

  | term | formula | source |
  |---|---|---|
  | `epsPrf`, `epsUdTight` | `8q²/2^128` | `SlhDsaComposed.lean:128`; `SlhDsaComposedFinal.lean:268` |
  | `epsDsprTight` | `168q²/2^128` | `SlhDsaComposedFinal.lean:264` |
  | `epsTcr0` | `(2q+1)²/2^128` | `SlhDsaComposedFinal.lean:260` |
  | `epsPre0` | `2·(2q+1)²/2^128` | `SlhDsaComposedFinal.lean:271` |
  | `epsItsr` | `(√((2q+1)²·Cov(qs)) + 2q·√(qs/2^128))²`, with `Cov` the binomial cover sum (`h=63, a=12, k=14`) | `SlhDsaComposed.lean:158-163` |

- **The counts.** `RedCounts.noPrfMsg` sets `prf` and `msg` to 0 (`SlhDsaComposedEnc2Msg.lean:68`).
  `openCounts128s` is pure numerals (`SlhDsaComposedFinal.lean:359-371`). For the statement's
  truth it does not matter where they come from. Their link to the proof is by theorems:
  - `itsrHashes_openCounts128s` (`SlhDsaBridgeMachItsr.lean:149`);
  - `tcrMHashes_openCounts128s` (`SlhDsaBridgeMach.lean:577`);
  - `forsMHashes_openCounts128s` (`SlhDsaBridgeMachFors.lean:620`);
  - `qmWots{TcrT,Ud,Pre}Hashes_openCounts128s` (`SlhDsaBridgeMachWots.lean:197/264/328`).

  `openCounts128s_sound` (`SlhDsaOpenCounts.lean:25`) ties the same numerals to the classical
  open programs of `security/`.

**My numerical evaluation** (Python, from the definitions above):

| (q, qs) | bound | dominant term |
|---|---|---|
| (2^40, 2^20) | **2^-22.91** (≤ 2^-22 ✓) | ITSR, almost entirely `(2q'√(qs/2^128))²` with `q' ≈ 3·2^40` |
| (1, 1) | 2^-78.2 | |
| (1, 2^10) | 2^-54.1 | |
| (2^40, 1) | 2^-39.6 | |
| (2^40, 2^10) | 2^-35.9 | |
| (2^50, 2^20) | 2^-6.0 | |
| (2^40, 2^30) | 2^5.9 | |
| (2^64, 1) | 2^8.4 | |

The bound exceeds 1:

- for `qs ≥ 2^28.04`, whatever `q` (this is the ITSR term);
- for `q ≥ 2^53.0` at `qs = 2^20`;
- for `q ≥ 2^59.8` at `qs = 0`.

At `q = 2^40` it exceeds `2^-22` once `qs ≥ 2^20.4`. `Num.composedBoundFinal_num`
(`SlhDsaComposedClosedNum.lean:138-140`) states exactly `composedBoundFinal (2^40) (2^20)
(openCounts128s (2^20)).noPrfMsg ≤ (2^22)⁻¹`. The `_num` headlines (`:187-209`) are the closed
headlines with `q = 2^40` and `qs = 2^20` substituted. They match the informal statement.

## Non-vacuity

The repo's `PQ/QROM/NonVacuity*.lean` files are about the Part-2 games (preimage, Deutsch,
Grover). They are **not** about this statement and do not mention `PortForger`.

I built an instance myself in `quantum/scratch/audit/NonVac.lean`. It compiles with axioms
`[propext, Classical.choice, Quot.sound]`.

- `c0 = ⟨35, 2⟩`.
- `F1 : PortForger (EncX c0) EncY Unit`. It makes one port call, then one signing query on
  `([], [])`, and outputs `(([], []), σ)`, where `σ` is the signature it received. Its `ρ₀` is a
  diagonal basis-state projector.
- `F1_hq`, `F1_hqs` (budget 1) and `F1_hcap` are proved.
- `F1_suf` and `F1_euf` apply both headlines.
- `F1_suf_num` applies the `2^40 / 2^20` corollary, using a proved monotonicity lemma for
  `CountBound`.

So the hypotheses are satisfiable by a forger that really uses both oracles. `F1` itself never
wins: it re-outputs a signature it received on a message it queried. What I did **not** do is
exhibit a forger whose advantage is provably positive. Non-triviality of the
left-hand side rests on the semantics (`qWeight`, `qUnforgeableAdvantage_eq`).

## Findings

### (A) False or materially overstated

None found.

### (B) Caveats the claim should carry

1. **The functions are constant outside the caps, not random.** See `SlhDsaRandomFinite.lean:100-104`.
   With `hcap` and `35 ≤ c.tl`, the experiment should never evaluate a hash outside the caps, so
   the world is indistinguishable from unbounded random oracles. But the repo itself says this
   side condition "is NOT formalised as a theorem" (`SlhDsaRandomFinite.lean:42-44`). The reading
   "SLH-DSA with random oracles on unbounded domains" is an informal step. Precisely: the theorem
   is about random functions on capped domains, extended by constants.
2. **Message lengths are bounded, and the forger's type depends on `c`.**
   - `hcap` requires every signing query and the forgery to satisfy `|M| + |ctx| + 2 ≤ c.ml`. The
     forger's port register `EncX c` depends on `c`, so it cannot query longer inputs (these are
     constants in the model anyway).
   - The bound does not depend on `c.ml`. So any forger whose messages are bounded can be covered
     by choosing `c.ml` large enough. A forger that is "the same" across caps is not one Lean
     object, though.
3. **The oracle uses `+` mod 256, not XOR.** `bytesGroup`, `SlhDsaBridgePrf.lean:56`. A standard
   XOR-oracle forger with `q` queries is simulated with `2q` port calls: compute into a zeroed
   register, XOR, negate, query again. So for XOR-model forgers the bound applies at `2q`.
4. **Strength of the bound.** It is weak, as the claim warns, and vacuous for `qs ≥ 2^28`. It is
   also vacuous for `q ≥ 2^53` at `qs = 2^20`, and for `q ≳ 2^59.8` even with no signatures. The
   cause is the linear-in-`q` ITSR reprogramming term together with the reduction's roughly
   `2^21` counted hash calls per signature. At the stated point the true value is `≈ 2^-22.9`.
5. **Scheme parameters are universally quantified, with one restriction.** `optRand₀` and
   `pkSeedDist₀` are arbitrary: nothing is assumed about them, which only strengthens the
   theorem. But `opt_rand` may depend only on `(PK.seed, PK.root)` and not on ω or `SK`
   (`SlhDsaComposed.lean:397-398`). This covers FIPS hedged signing (uniform) and deterministic
   signing (`opt_rand = PK.seed`). PK.seed's distribution is arbitrary; `SK.seed` and `SK.prf`
   are uniform.
6. **Independence of the four components is an idealization.** In real SHA2 SLH-DSA, `PRF` and
   `F` are the same SHA-256 call, separated only by the ADRS type. `H_msg` is MGF1 over a nested
   SHA-256, and `PRF_msg` is HMAC. Modelling them as four independent monolithic random functions
   is the stated model; it is not "SHA-256 is a random oracle".
7. **Where the hypotheses must hold.** `hq` / `hqs` / `hcap` must hold for every `pk : List Byte`
   (including non-keys) and on every syntactic path, for every answer value. This is harmless:
   any forger can be truncated.
8. **FIPS 205 conformance is not checked here.** The conformance of the generic `pureBytesAlg` /
   VCVio `GeneralScheme` code to FIPS 205 is inherited from `security/` and the Spec link, and I
   did not re-audit it. The QROM scheme is that same code.

### (C) Cosmetic or outdated documentation

- Several headers say the bridge terms or `hInd` are unproved. They are now superseded by the
  closed theorem:
  - `SlhDsaComposedFinal.lean:35-55` ("NO field … discharged");
  - `SlhDsaBridgePrf.lean:30-37` (`hInd` "NOT proved");
  - `SlhDsaComposed.lean:34-35` ("`c.tl ≥ 35` … NOT a hypothesis", which is about the older
    theorem);
  - `SlhDsaOpenCounts.lean:15-17` ("not yet used to bound the oracle calls of the quantum
    machines"; per-term `…_openCounts128s` lemmas now exist).
- The same holds for `HANDOFF.md:19,31` and `quantum/STATUS.md:33-59`.

### Axioms and placeholders

- `#print axioms` gives only the three standard axioms. `native_decide` and `bv_decide` would
  show up as `Lean.ofReduceBool`; they do not.
- Grep over `quantum/Integration`, `quantum/PQ` and `security` (excluding `.lake`), for `sorry`,
  `axiom`, `native_decide`, `bv_decide`, `unsafe`, `implemented_by`, `@[extern]`, `opaque`,
  `notation`, `macro`, `syntax`:
  - nothing in `quantum/Integration` or `quantum/PQ`;
  - in `security`, only `sorry` in `security/scratch/**` (not imported) and `local notation`
    abbreviations in `security/Ideal/Transport/Adv*.lean` (not in this cone, and abbreviations
    only).
- `#check` prints the statement with its real constants.
- `qm_kernel_rfl` (`SlhDsaBridgeMach.lean:201-207`) and `qtcr_kernel_rfl`
  (`SlhDsaBridgeTcr.lean:142-148`) only assign `Eq.refl a` to the goal (`Lean.Meta.mkEqRefl`).
  The definitional check is done by the kernel when the declaration is added. They introduce no
  axiom.

## Corrected plain-English statement

Let `c` be any caps with `c.tl ≥ 35`. Let the four hash components of SLH-DSA-SHA2-128s (`Thash`,
`H_msg`, `PRF` on 22-byte compressed addresses, `PRF_msg`) be independent uniformly random
functions on the capped domains (Thash lists of ≤ `c.tl` nodes, messages of ≤ `c.ml` bytes),
extended by fixed constants outside the caps. Consider the FIPS 205 external pure interface on
byte strings (Alg. 21/22/24, context strings, FIPS wire codec). Key generation uses uniform
`SK.seed` / `SK.prf` and an arbitrary fixed `PK.seed` distribution. Signing randomness is drawn
from an arbitrary fixed distribution that depends only on `(PK.seed, PK.root)`.

Take any quantum forger. It is a fixed program with an arbitrary finite workspace and an
arbitrary initial state. Its only access to the hash functions is a single quantum oracle on the
disjoint union of the four capped domains, `|x, y⟩ ↦ |x, y + H(x)⟩` with bytewise addition
mod 256. It also has a classical signing oracle and uniform randomness. On every path, it makes at
most `q` oracle calls and at most `qs` signing queries, and all signing queries and the forgery
satisfy `|M| + |ctx| + 2 ≤ c.ml`.

Then its SUF-CMA (resp. EUF-CMA) success probability, averaged over the random functions, is at
most `composedBoundFinal q qs (openCounts128s qs).noPrfMsg`. In that bound, the reduction's own
roughly `2.0·10^6` hash evaluations per signature are counted as quantum queries. The bound is
≈ `2^-22.9` (proved `≤ 2^-22`) at `q = 2^40` and `qs = 2^20`, and is vacuous for `qs ≥ 2^28`, or
for `q ≥ 2^53` at `qs = 2^20`. The equivalence of this capped model with unbounded random oracles
is informal and is not formalised.

## Not checked

- The proofs themselves; the kernel checks those.
- FIPS 205 conformance of `pureBytesAlg` and VCVio's `GeneralScheme`.
- The informal claim that the experiment never evaluates a hash outside the caps under `hcap` and
  `tl ≥ 35`.
- That some forger has positive advantage.
- The Part-2 game definitions (`PQ/QROM/Exact*`). These enter only through proofs, not through
  the statement.
- The provenance of the `security/` oleans beyond their timestamps.
