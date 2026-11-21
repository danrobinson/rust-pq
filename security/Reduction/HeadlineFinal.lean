import Reduction.LinearBytes

/-!
# The final headline theorems (phase 3 integration)

This file composes the three phase-3 improvements into one family of statements:

* the **byte-level schemes** `bytesAlg` / `pureBytesAlg` (`Reduction/Bytes.lean`): public keys,
  secret keys, messages and signatures are byte strings, and the deterministic cores are the
  functions the Rust code is proved to compute (`E2E/Bytes.lean`, `E2E/Headline.lean`);
* the **tight target caps** (`Reduction/TightCaps.lean`): every SM game is capped at the number
  of targets its adversary provably registers (`thashArityProblemT`, `wotsTcrProblemT`);
* the **memoising class adversaries** `bTcrArM n A` (`Reduction/TcrMemo.lean`), which do not
  recompute the key structure after the seed is revealed.

## Statements

Absolute-value form (twelve advantages, `boundFinalTight`, adversaries written out):

| scheme | SUF-CMA | EUF-CMA |
|---|---|---|
| typed, internal (`internalAlg`) | `slhdsa_suf_cma_final_memo` | `slhdsa_euf_cma_final_memo` |
| typed, external (`externalAlg`) | `slhdsa_pure_suf_cma_final_memo` | `slhdsa_pure_euf_cma_final_memo` |
| bytes, internal (`bytesAlg`) | `slhdsa_bytes_suf_cma_final` | `slhdsa_bytes_euf_cma_final` |
| bytes, external (`pureBytesAlg`) | `slhdsa_pure_bytes_suf_cma_final` | `slhdsa_pure_bytes_euf_cma_final` |

(the typed rows are in `Reduction/TcrMemoHeadline.lean`; the byte-level rows are here).  The
right-hand sides are `betaSufFinalMemo` / `betaEufFinalMemo` at the typed forger built from the
given one, unfolded one step.

Linear (signed-pair) form, same adversaries and games: `slhdsa_{suf,euf}_cma_final_linear`,
`slhdsa_pure_{suf,euf}_cma_final_linear` (`Reduction/Linear.lean`) and
`slhdsa_bytes_{suf,euf}_cma_linear`, `slhdsa_pure_bytes_{suf,euf}_cma_linear`
(`Reduction/LinearBytes.lean`); these are already at the final adversaries and tight caps
(`linRealSuf`, `linIdealSuf`, … are defined with `bTcrArM` and `rTcrT`), so nothing is restated
here.  `slhdsa_*_memo_of_linear` re-derive the absolute-value bounds from the linear ones; the
theorems of this file are derived directly from the typed absolute-value theorems through the
byte-level transfer lemmas of `Reduction/Bytes.lean`.

SHA2-128s instances without hypothesis: `slhdsa_sha2_128s_{bytes,pure_bytes}_{suf,euf}_cma_final`.

## Uniform seed, FIPS choices of `opt_rand`

All theorems above hold for an **arbitrary** distribution `pkSeedDist` of `PK.seed` and an
arbitrary source `optRand` of `opt_rand`.  The second half of the file instantiates them, so
that a reader does not have to: `pkSeedDist := $ᵗ prims.PkSeed` (uniform `PK.seed`) and

* *deterministic* (FIPS 205 Alg. 19/22 with `opt_rand = PK.seed`):
  `optRand := fun pk => pure (toY pk.pkSeed)` for a map `toY : PkSeed → Y` (the abstract
  interface keeps the two carriers independent; at SHA2-128s both are `Bytes 16` and `toY` is
  VCVio's `SLHDSA.Concrete.sha2RandomizerOfPkSeed`, the identity);
* *hedged* (fresh uniform `opt_rand` per signature): `optRand := fun _ => $ᵗ prims.Y`.

Names: `slhdsa_{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}` and
`slhdsa_sha2_128s_{,pure_}{,bytes_}{suf,euf}_cma_{deterministic,hedged}`.

**On the seed distribution.**  The general theorems are true for every `pkSeedDist`, including
degenerate ones (a constant seed).  For a degenerate seed distribution the same `pkSeedDist`
is the seed distribution of all twelve games on the right, so the statement is then about
games with a known seed: still a theorem, but the assumptions that those twelve advantages are
small are then implausible (an adversary may have the seed's collisions built in).  The
corollaries fix the uniform distribution, which is what FIPS 205 key generation prescribes.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

open TweakableHash

set_option linter.unusedSectionVars false

section Final

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

-- as in `Reduction/TightCaps.lean`: never evaluate the caps during unification
attribute [local irreducible] arityTargets tcrTargets

/-! ## Byte-level schemes, tight caps, final adversaries -/

/-- **Standard-model SUF-CMA security of SLH-DSA on byte strings (FIPS 205 Alg. 18–20) — final
form.**  For every strong forger `S` against the byte-level scheme
`bytesAlg vp prims codec optRand pkSeedDist` — `S` gets the public key as bytes, has a signing
oracle from message bytes to signature bytes, and wins if it outputs a message and a byte string
that `byteVerify` accepts and that the oracle never returned for that message — the advantage is
at most the twelve standard-model advantages of `boundFinalTight`: every SM game at its tight
target cap, the class adversaries `bTcrArM` (no structure recomputation after the seed reveal),
all at the typed forger `bytesToTypedS S` (one typed signing query per byte-level query).
Holds for arbitrary `optRand` and `pkSeedDist`. -/
theorem slhdsa_bytes_suf_cma_final (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary)
        (Lazy.bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary)
        (Lazy.bItsrL (bytesToTypedS S).toUnforgeableAdversary)
        (toDspr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
        (toTcr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
        (bTcrArM 1 (bytesToTypedS S).toUnforgeableAdversary) (bTcrArM 2 (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArM vp.params.len (bytesToTypedS S).toUnforgeableAdversary)
        (bTcrArM vp.params.k (bytesToTypedS S).toUnforgeableAdversary)
        (rUd pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
        (rPre pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
        (rTcrT pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary)) :=
  bytes_strong_bound_of_typed_bound (fun B => betaSufFinalMemo B.toUnforgeableAdversary)
    (slhdsa_suf_cma_final_memo' hS) S

/-- **Standard-model EUF-CMA security of SLH-DSA on byte strings — final form**: the twelve
advantages of `boundFinalTight` (tight caps, `bTcrArM`) at the typed forger `bytesToTyped A`. -/
theorem slhdsa_bytes_euf_cma_final (hS : Structural vp prims)
    (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC (bytesToTyped A))
        (Lazy.bPrfMsgL (bytesToTyped A))
        (Lazy.bItsrL (bytesToTyped A))
        (toDspr (Lazy.bOpenPreS (bytesToTyped A)))
        (toTcr (Lazy.bOpenPreS (bytesToTyped A)))
        (bTcrArM 1 (bytesToTyped A)) (bTcrArM 2 (bytesToTyped A))
        (bTcrArM vp.params.len (bytesToTyped A))
        (bTcrArM vp.params.k (bytesToTyped A))
        (rUd pkSeedDist (Lazy.bWotsS (bytesToTyped A)))
        (rPre pkSeedDist (Lazy.bWotsS (bytesToTyped A)))
        (rTcrT pkSeedDist (Lazy.bWotsS (bytesToTyped A))) :=
  bytes_bound_of_typed_bound betaEufFinalMemo (slhdsa_euf_cma_final_memo' hS) A

/-- **Standard-model SUF-CMA security of the external pure interface on byte strings (FIPS 205
Alg. 21/22/24) — final form.**  For every strong forger `S` against
`pureBytesAlg vp prims codec optRand pkSeedDist` — messages are `(message, context)` pairs of
byte strings; a forgery is `((message, context), some bytes)` accepted by `byteVerifyPure` and
never returned for that pair; `none` is never accepted — the advantage is at most the twelve
advantages of `boundFinalTight` (tight caps, `bTcrArM`) at the internal typed forger
`toInternal (pureBytesToTyped S.toUnforgeableAdversary)`. -/
theorem slhdsa_pure_bytes_suf_cma_final (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      boundFinalTight pkSeedDist (bPrfWC sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (Lazy.bPrfMsgWL sufCheck (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (Lazy.bItsrL (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (toDspr (Lazy.bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))
        (toTcr (Lazy.bOpenPreS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))
        (bTcrArM 1 (toInternal (pureBytesToTyped S.toUnforgeableAdversary))) (bTcrArM 2 (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (bTcrArM vp.params.len (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (bTcrArM vp.params.k (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))
        (rPre pkSeedDist (Lazy.bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary))))
        (rTcrT pkSeedDist (Lazy.bWotsS (toInternal (pureBytesToTyped S.toUnforgeableAdversary)))) :=
  pure_bytes_strong_bound_of_internal_bound (fun B => betaSufFinalMemo B.toUnforgeableAdversary)
    (slhdsa_suf_cma_final_memo' hS) S

/-- **Standard-model EUF-CMA security of the external pure interface on byte strings — final
form**: the twelve advantages at `toInternal (pureBytesToTyped A)`. -/
theorem slhdsa_pure_bytes_euf_cma_final (hS : Structural vp prims)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      boundFinalTight pkSeedDist (bPrfC (toInternal (pureBytesToTyped A)))
        (Lazy.bPrfMsgL (toInternal (pureBytesToTyped A)))
        (Lazy.bItsrL (toInternal (pureBytesToTyped A)))
        (toDspr (Lazy.bOpenPreS (toInternal (pureBytesToTyped A))))
        (toTcr (Lazy.bOpenPreS (toInternal (pureBytesToTyped A))))
        (bTcrArM 1 (toInternal (pureBytesToTyped A))) (bTcrArM 2 (toInternal (pureBytesToTyped A)))
        (bTcrArM vp.params.len (toInternal (pureBytesToTyped A)))
        (bTcrArM vp.params.k (toInternal (pureBytesToTyped A)))
        (rUd pkSeedDist (Lazy.bWotsS (toInternal (pureBytesToTyped A))))
        (rPre pkSeedDist (Lazy.bWotsS (toInternal (pureBytesToTyped A))))
        (rTcrT pkSeedDist (Lazy.bWotsS (toInternal (pureBytesToTyped A)))) :=
  pure_bytes_bound_of_internal_bound betaEufFinalMemo (slhdsa_euf_cma_final_memo' hS) A

/-- The right-hand side of `slhdsa_bytes_suf_cma_final` is `betaSufFinalMemo` (by definition);
likewise for the other three (`betaEufFinalMemo`). -/
theorem slhdsa_bytes_suf_cma_final_rhs (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    boundFinalTight pkSeedDist (bPrfWC sufCheck (bytesToTypedS S).toUnforgeableAdversary)
      (Lazy.bPrfMsgWL sufCheck (bytesToTypedS S).toUnforgeableAdversary)
      (Lazy.bItsrL (bytesToTypedS S).toUnforgeableAdversary)
      (toDspr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
      (toTcr (Lazy.bOpenPreS (bytesToTypedS S).toUnforgeableAdversary))
      (bTcrArM 1 (bytesToTypedS S).toUnforgeableAdversary) (bTcrArM 2 (bytesToTypedS S).toUnforgeableAdversary)
      (bTcrArM vp.params.len (bytesToTypedS S).toUnforgeableAdversary)
      (bTcrArM vp.params.k (bytesToTypedS S).toUnforgeableAdversary)
      (rUd pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
      (rPre pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary))
      (rTcrT pkSeedDist (Lazy.bWotsS (bytesToTypedS S).toUnforgeableAdversary)) =
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary := rfl

/-! ## Uniform `PK.seed`, deterministic and hedged `opt_rand`

Instances of the general theorems (which hold for arbitrary `pkSeedDist` and `optRand`; for a
degenerate seed distribution they are statements about games with a known seed — still true,
but the assumptions are then implausible; see the file header).  In every theorem below
`PK.seed` is uniform, in the scheme and in all twelve games.  The bound is written
`betaSufFinalMemo …` / `betaEufFinalMemo …` (`Reduction/TcrMemoHeadline.lean`): the twelve
advantages of `boundFinalTight` at the displayed typed forger. -/

variable [SampleableType prims.PkSeed]

/-- **SUF-CMA of SLH-DSA, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_suf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed))) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_memo' hS S

/-- **SUF-CMA of SLH-DSA, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_suf_cma_hedged (hS : Structural vp prims)
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed))) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo S.toUnforgeableAdversary :=
  slhdsa_suf_cma_final_memo' hS S

/-- **EUF-CMA of SLH-DSA, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_euf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (A : Forger vp prims (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo A :=
  slhdsa_euf_cma_final_memo' hS A

/-- **EUF-CMA of SLH-DSA, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_euf_cma_hedged (hS : Structural vp prims)
    (A : Forger vp prims (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo A :=
  slhdsa_euf_cma_final_memo' hS A

/-- **SUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures; uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_suf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (S : ExtStrongForger vp prims (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final_memo' hS S

/-- **SUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures; uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_suf_cma_hedged (hS : Structural vp prims)
    (S : ExtStrongForger vp prims (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_final_memo' hS S

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures; uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_euf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (A : ExtForger vp prims (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal A) :=
  slhdsa_pure_euf_cma_final_memo' hS A

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures; uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_euf_cma_hedged (hS : Structural vp prims)
    (A : ExtForger vp prims (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal A) :=
  slhdsa_pure_euf_cma_final_memo' hS A

/-- **SUF-CMA of SLH-DSA on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_bytes_suf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (S : BytesStrongForger vp prims codec (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_final hS S

/-- **SUF-CMA of SLH-DSA on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_bytes_suf_cma_hedged (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_final hS S

/-- **EUF-CMA of SLH-DSA on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_bytes_euf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (A : BytesForger vp prims codec (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_final hS A

/-- **EUF-CMA of SLH-DSA on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_bytes_euf_cma_hedged (hS : Structural vp prims)
    (A : BytesForger vp prims codec (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_final hS A

/-- **SUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24); uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_bytes_suf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (S : PureBytesStrongForger vp prims codec (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_final hS S

/-- **SUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24); uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_bytes_suf_cma_hedged (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_final hS S

/-- **EUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24); uniform `PK.seed`; deterministic signing, `opt_rand = toY PK.seed` (FIPS 205: `opt_rand = PK.seed`).**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_bytes_euf_cma_deterministic (hS : Structural vp prims) (toY : prims.PkSeed → prims.Y)
    (A : PureBytesForger vp prims codec (fun pk => (pure (toY pk.pkSeed) : ProbComp prims.Y)) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_final hS A

/-- **EUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24); uniform `PK.seed`; hedged signing, `opt_rand` uniform and fresh per signature.**
Instance of the general theorem, which holds for arbitrary `pkSeedDist` and `optRand`. -/
theorem slhdsa_pure_bytes_euf_cma_hedged (hS : Structural vp prims)
    (A : PureBytesForger vp prims codec (fun _ => $ᵗ prims.Y) ($ᵗ prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_final hS A

end Final

/-! ## SLH-DSA-SHA2-128s

`Link.prims.PkSeed` and `Link.prims.Y` are both `Bytes 16`; the deterministic variant uses
VCVio's `SLHDSA.Concrete.sha2RandomizerOfPkSeed` (the identity: `detRand_128s`), i.e.
`opt_rand = PK.seed` literally. -/

/-- At SHA2-128s the FIPS conversion `PK.seed ↦ opt_rand` is the identity on `Bytes 16`. -/
theorem detRand_128s (s : Link.prims.PkSeed) :
    SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params s = s := rfl

/-- **SUF-CMA of SLH-DSA-SHA2-128s on byte strings (internal algorithms), final form**
(arbitrary `optRand`, `pkSeedDist`). -/
theorem slhdsa_sha2_128s_bytes_suf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : BytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_final structural_128s S

/-- **EUF-CMA of SLH-DSA-SHA2-128s on byte strings (internal algorithms), final form.** -/
theorem slhdsa_sha2_128s_bytes_euf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : BytesForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_final structural_128s A

/-- **SUF-CMA of the external pure interface of SLH-DSA-SHA2-128s on byte strings, final
form.** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : PureBytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_final structural_128s S

/-- **EUF-CMA of the external pure interface of SLH-DSA-SHA2-128s on byte strings, final
form.** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_final
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : PureBytesForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_final structural_128s A

/-- **SUF-CMA of SLH-DSA-SHA2-128s, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_suf_cma_deterministic
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg Link.vp Link.prims (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed))) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo S.toUnforgeableAdversary :=
  slhdsa_suf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) S

/-- **SUF-CMA of SLH-DSA-SHA2-128s, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_suf_cma_hedged
    (S : SignatureAlg.StrongUnforgeableAdversary (internalAlg Link.vp Link.prims (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed))) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo S.toUnforgeableAdversary :=
  slhdsa_suf_cma_hedged structural_128s S

/-- **EUF-CMA of SLH-DSA-SHA2-128s, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_euf_cma_deterministic
    (A : Forger Link.vp Link.prims (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo A :=
  slhdsa_euf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) A

/-- **EUF-CMA of SLH-DSA-SHA2-128s, internal algorithms (FIPS 205 Alg. 18–20), typed keys and signatures; uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_euf_cma_hedged
    (A : Forger Link.vp Link.prims (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo A :=
  slhdsa_euf_cma_hedged structural_128s A

/-- **SUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures of SLH-DSA-SHA2-128s; uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_pure_suf_cma_deterministic
    (S : ExtStrongForger Link.vp Link.prims (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) S

/-- **SUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures of SLH-DSA-SHA2-128s; uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_pure_suf_cma_hedged
    (S : ExtStrongForger Link.vp Link.prims (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal S.toUnforgeableAdversary) :=
  slhdsa_pure_suf_cma_hedged structural_128s S

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures of SLH-DSA-SHA2-128s; uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_pure_euf_cma_deterministic
    (A : ExtForger Link.vp Link.prims (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal A) :=
  slhdsa_pure_euf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) A

/-- **EUF-CMA of the external pure interface (FIPS 205 Alg. 21/22/24), typed keys and signatures of SLH-DSA-SHA2-128s; uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_pure_euf_cma_hedged
    (A : ExtForger Link.vp Link.prims (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal A) :=
  slhdsa_pure_euf_cma_hedged structural_128s A

/-- **SUF-CMA of SLH-DSA-SHA2-128s on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_bytes_suf_cma_deterministic
    (S : BytesStrongForger Link.vp Link.prims codec128s (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) S

/-- **SUF-CMA of SLH-DSA-SHA2-128s on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_bytes_suf_cma_hedged
    (S : BytesStrongForger Link.vp Link.prims codec128s (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma_hedged structural_128s S

/-- **EUF-CMA of SLH-DSA-SHA2-128s on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_bytes_euf_cma_deterministic
    (A : BytesForger Link.vp Link.prims codec128s (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) A

/-- **EUF-CMA of SLH-DSA-SHA2-128s on byte strings, internal algorithms (FIPS 205 Alg. 18–20); uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_bytes_euf_cma_hedged
    (A : BytesForger Link.vp Link.prims codec128s (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (bytesToTyped A) :=
  slhdsa_bytes_euf_cma_hedged structural_128s A

/-- **SUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24) of SLH-DSA-SHA2-128s; uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_deterministic
    (S : PureBytesStrongForger Link.vp Link.prims codec128s (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) S

/-- **SUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24) of SLH-DSA-SHA2-128s; uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_pure_bytes_suf_cma_hedged
    (S : PureBytesStrongForger Link.vp Link.prims codec128s (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalMemo (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma_hedged structural_128s S

/-- **EUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24) of SLH-DSA-SHA2-128s; uniform `PK.seed`; deterministic signing (`opt_rand = PK.seed`).** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_deterministic
    (A : PureBytesForger Link.vp Link.prims codec128s (fun pk => (pure (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params pk.pkSeed) :
        ProbComp Link.prims.Y)) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_deterministic structural_128s (SLHDSA.Concrete.sha2RandomizerOfPkSeed Link.vp.params) A

/-- **EUF-CMA of the external pure interface on byte strings (FIPS 205 Alg. 21/22/24) of SLH-DSA-SHA2-128s; uniform `PK.seed`; hedged signing (`opt_rand` uniform, fresh per signature).** -/
theorem slhdsa_sha2_128s_pure_bytes_euf_cma_hedged
    (A : PureBytesForger Link.vp Link.prims codec128s (fun _ => $ᵗ Link.prims.Y) ($ᵗ Link.prims.PkSeed)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalMemo (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma_hedged structural_128s A

#print axioms slhdsa_bytes_suf_cma_final
#print axioms slhdsa_bytes_euf_cma_final
#print axioms slhdsa_pure_bytes_suf_cma_final
#print axioms slhdsa_pure_bytes_euf_cma_final
#print axioms slhdsa_sha2_128s_bytes_suf_cma_final
#print axioms slhdsa_sha2_128s_bytes_euf_cma_final
#print axioms slhdsa_sha2_128s_pure_bytes_suf_cma_final
#print axioms slhdsa_sha2_128s_pure_bytes_euf_cma_final
#print axioms slhdsa_suf_cma_deterministic
#print axioms slhdsa_suf_cma_hedged
#print axioms slhdsa_euf_cma_deterministic
#print axioms slhdsa_euf_cma_hedged
#print axioms slhdsa_pure_suf_cma_deterministic
#print axioms slhdsa_pure_suf_cma_hedged
#print axioms slhdsa_pure_euf_cma_deterministic
#print axioms slhdsa_pure_euf_cma_hedged
#print axioms slhdsa_bytes_suf_cma_deterministic
#print axioms slhdsa_bytes_suf_cma_hedged
#print axioms slhdsa_bytes_euf_cma_deterministic
#print axioms slhdsa_bytes_euf_cma_hedged
#print axioms slhdsa_pure_bytes_suf_cma_deterministic
#print axioms slhdsa_pure_bytes_suf_cma_hedged
#print axioms slhdsa_pure_bytes_euf_cma_deterministic
#print axioms slhdsa_pure_bytes_euf_cma_hedged
#print axioms slhdsa_sha2_128s_suf_cma_deterministic
#print axioms slhdsa_sha2_128s_suf_cma_hedged
#print axioms slhdsa_sha2_128s_euf_cma_deterministic
#print axioms slhdsa_sha2_128s_euf_cma_hedged
#print axioms slhdsa_sha2_128s_pure_suf_cma_deterministic
#print axioms slhdsa_sha2_128s_pure_suf_cma_hedged
#print axioms slhdsa_sha2_128s_pure_euf_cma_deterministic
#print axioms slhdsa_sha2_128s_pure_euf_cma_hedged
#print axioms slhdsa_sha2_128s_bytes_suf_cma_deterministic
#print axioms slhdsa_sha2_128s_bytes_suf_cma_hedged
#print axioms slhdsa_sha2_128s_bytes_euf_cma_deterministic
#print axioms slhdsa_sha2_128s_bytes_euf_cma_hedged
#print axioms slhdsa_sha2_128s_pure_bytes_suf_cma_deterministic
#print axioms slhdsa_sha2_128s_pure_bytes_suf_cma_hedged
#print axioms slhdsa_sha2_128s_pure_bytes_euf_cma_deterministic
#print axioms slhdsa_sha2_128s_pure_bytes_euf_cma_hedged

end Reduction
