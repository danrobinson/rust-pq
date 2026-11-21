import Reduction.External

/-!
# Strong unforgeability through a partial message encoding

`Reduction.External` transfers EUF-CMA from a scheme `alg` to `Guarded.scheme alg enc` (the same
scheme behind a partial injective message encoding, signatures of type `Except ε S`).  This file
does the same for SUF-CMA:

* `Guarded.reduceS` — the same wrapper as `Guarded.reduce`, as a strong-unforgeability adversary;
* `Guarded.strongUnforgeableAdvantage_le` — the SUF-CMA advantage against `scheme alg enc` is at
  most that of the wrapped adversary against `alg`;
* `toInternalS`, `external_strong_advantage_le`, `toInternalS_queryBound` — the instance at the
  external pure SLH-DSA scheme `externalAlg`.

A strong forgery against `scheme alg enc` is a pair `(e, s)` that verifies and was never returned
by the signing oracle.  An error value `s = .error x` is never accepted by `verify`
(`externalAlg_verify_error`), and neither is any signature on an `e` whose encoding fails, so
the error value the signing oracle returns for over-long contexts cannot be (part of) a forgery;
the log entries `(e, .error x)` are dropped by `decodeLog`.  If the forger outputs `(e, .ok σ)`
with `enc e = .ok m` and the pair `(m, σ)` were in the reduction's log, the log of the forger
would contain some `(e', .ok σ)` with `enc e' = .ok m`, and `e' = e` by injectivity.
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

namespace Guarded

variable {E M PK SK S ε : Type}

/-- **The reduction for strong unforgeability**: the program of `Guarded.reduce`. -/
def reduceS (alg : SignatureAlg ProbComp M PK SK S) (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.StrongUnforgeableAdversary alg where
  main pk := readForgery enc fallback <$> simulateQ (signingImpl enc) (adv.main pk)

/-- `reduceS` and `reduce` are the same program. -/
theorem reduceS_toUnforgeableAdversary (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    (reduceS alg enc fallback adv).toUnforgeableAdversary =
      reduce alg enc fallback adv.toUnforgeableAdversary := rfl

/-- Pair-freshness transfers: if `enc` is injective on its domain and the pair `(e, .ok σ)` was
never returned to the forger, then `(m, σ)` (with `enc e = .ok m`) was never returned to the
reduction. -/
theorem pairFresh_of_pairFresh (enc : E → Except ε M)
    (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (log : QueryLog (E →ₒ Except ε S)) (e : E) (m : M) (σ : S) (he : enc e = .ok m)
    (hfresh : (⟨e, Except.ok σ⟩ : (_ : E) × Except ε S) ∉ log) :
    (⟨m, σ⟩ : (_ : M) × S) ∉ decodeLog enc log := by
  intro hm
  obtain ⟨⟨e', s⟩, hw, hdec⟩ := List.mem_filterMap.mp hm
  apply hfresh
  cases he' : enc e' with
  | error x => simp [he'] at hdec
  | ok m'' =>
    cases s with
    | error x => simp [he'] at hdec
    | ok σ' =>
      simp only [he', Option.some.injEq, Sigma.mk.injEq] at hdec
      obtain ⟨rfl, hσ⟩ := hdec
      have hσ' : σ' = σ := eq_of_heq hσ
      have := hinj e e' _ he he'
      subst this
      subst hσ'
      exact hw

open scoped Classical in
/-- The strong-unforgeability experiment of the reduction, written over the run of the original
forger. -/
theorem strongUnforgeableExperiment_reduceS (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.strongUnforgeableExperiment (reduceS alg enc fallback adv) = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← (scheme alg enc).runWithSigningOracle pk sk (adv.main pk)
      let verified ← alg.verify pk (readForgery enc fallback out).1 (readForgery enc fallback out).2
      return !SignatureAlg.signingLogContains (decodeLog enc log)
        (readForgery enc fallback out).1 (readForgery enc fallback out).2 && verified := by
  simp only [SignatureAlg.strongUnforgeableExperiment, reduceS, runWithSigningOracle_map,
    bind_map_left]
  simp only [runWithSigningOracle_signingImpl alg enc, bind_map_left]
  rfl

set_option linter.style.longLine false in
open scoped Classical in
/-- **Advantage transfer for strong unforgeability (generic).**  If `enc` is injective on its
domain, the SUF-CMA advantage of any strong forger against `scheme alg enc` is at most that of
`reduceS alg enc fallback adv` against `alg`. -/
theorem strongUnforgeableAdvantage_le (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (fallback : M × S) (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (reduceS alg enc fallback adv) := by
  have key : Pr{let b ← SignatureAlg.strongUnforgeableExperiment adv}[b = true] ≤
      Pr{let b ← SignatureAlg.strongUnforgeableExperiment (reduceS alg enc fallback adv)}[b = true] := by
    rw [strongUnforgeableExperiment_reduceS]
    simp only [SignatureAlg.strongUnforgeableExperiment]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨pk, sk⟩
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨⟨e, s⟩, log⟩
    cases he : enc e with
    | error x => simp [scheme, he]
    | ok m =>
      cases s with
      | error x => simp [scheme, he]
      | ok σ =>
        simp only [scheme, readForgery, he]
        apply prEvent_bind_mono_of_forall_le
        intro verified
        by_cases hf : (⟨e, Except.ok σ⟩ : (_ : E) × Except ε S) ∈ log
        · simp [SignatureAlg.signingLogContains, hf]
        · have ht := pairFresh_of_pairFresh enc hinj log e m σ he hf
          simp [SignatureAlg.signingLogContains, ht, hf]
  simpa only [SignatureAlg.strongUnforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using key

/-- **Query budget of `reduceS`**: at most as many signing queries as the forger. -/
theorem reduceS_queryBound (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) (qs : ℕ) (pk : PK)
    (h : IsQueryBoundP (adv.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP ((reduceS alg enc fallback adv).main pk) (fun i => i.isRight = true) qs :=
  reduce_queryBound alg enc fallback adv.toUnforgeableAdversary qs pk h

end Guarded

/-! ## The external pure SLH-DSA scheme -/

section External

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

variable (vp prims optRand pkSeedDist) in
/-- A strong forger against the external pure scheme: it wins
(`SignatureAlg.strongUnforgeableExperiment`) if its output `((message, context), s)` is accepted
— so `s = .ok σ` and the context has at most 255 bytes — and that exact pair was never returned
by the signing oracle. -/
abbrev ExtStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary (externalAlg vp prims optRand pkSeedDist)

/-- **The reduction from the external to the internal strong-unforgeability game**: the program
of `toInternal`. -/
noncomputable def toInternalS [Inhabited prims.Y]
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist) :=
  Guarded.reduceS (internalAlg vp prims optRand pkSeedDist) pureEncode ([], constSig default) S

/-- `toInternalS S`, regarded as an EUF-CMA forger, is `toInternal` of `S` regarded as one. -/
theorem toInternalS_toUnforgeableAdversary [Inhabited prims.Y]
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    (toInternalS S).toUnforgeableAdversary = toInternal S.toUnforgeableAdversary := rfl

/-- **External SUF-CMA advantage ≤ internal SUF-CMA advantage.** -/
theorem external_strong_advantage_le [Inhabited prims.Y]
    (S : ExtStrongForger vp prims optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (toInternalS S) :=
  Guarded.strongUnforgeableAdvantage_le _ _ pureEncode_injective _ S

/-- **Resources of `toInternalS`**: at most as many signing queries as `S`. -/
theorem toInternalS_queryBound [Inhabited prims.Y]
    (S : ExtStrongForger vp prims optRand pkSeedDist)
    (qs : ℕ) (hS : ∀ pk, IsQueryBoundP (S.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((toInternalS S).main pk) (fun i => i.isRight = true) qs :=
  fun pk => Guarded.reduceS_queryBound _ _ _ S qs pk (hS pk)

end External

#print axioms Guarded.strongUnforgeableAdvantage_le
#print axioms external_strong_advantage_le
#print axioms toInternalS_queryBound

end Reduction
