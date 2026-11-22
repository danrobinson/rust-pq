import Reduction.ExternalSuf
import Link.Security

/-!
# A scheme behind a partial message encoding, over an arbitrary oracle interface

`Reduction.Guarded` (`Reduction/External.lean`, `Reduction/ExternalSuf.lean`) puts a signature
scheme over `ProbComp` behind a partial injective message encoding `enc : E → Except ε M` and
transfers EUF-CMA / SUF-CMA from the scheme to the wrapped one.  The random-oracle theorem of
SLH-DSA (`Link.security_128s`) is about a scheme over `OracleComp (unifSpec + hashSpec …)`, so
the same construction is needed over an arbitrary ambient interface `spec`:

* `GuardedRom.scheme alg enc` — the same definition as `Reduction.Guarded.scheme`, for
  `alg : SignatureAlg (OracleComp spec) …`; at `spec = unifSpec` it *is* `Guarded.scheme`
  (`scheme_eq_guarded`, `rfl`);
* `map_scheme` — interpreting the ambient oracles commutes with the wrapper;
* `GuardedRom.reduceS` — the wrapper adversary: it runs the forger once, forwards every ambient
  query (uniform sampling *and* hash queries) unchanged, answers a signing query `e` by the error
  value if `enc e` fails (no query) and otherwise by exactly one query `enc e` to its own signing
  oracle, and outputs the encoded forgery;
* `prEvent_strongUnforgeableExperiment_le` — under **every** stateful interpretation of the
  ambient oracles (in particular the lazy random oracle), the success probability of the
  forger against `scheme alg enc` is at most that of `reduceS` against `alg`;
* `strongUnforgeableAdvantage_le` — the same in the random-oracle runtime
  `ProbCompRuntime.rom hs`;
* `romQueryBound_reduceS` — `reduceS` makes at most as many hash queries and at most as many
  signing queries as the forger (`RomQueryBound qh qs` is preserved).
-/

open OracleComp OracleSpec ENNReal

namespace E2E

namespace GuardedRom

variable {ι : Type} {spec : OracleSpec ι} {E M PK SK S ε : Type}

/-- The scheme `alg` behind a partial message encoding `enc`: signing `e` returns the error if
`enc e` fails and `.ok σ` with `σ ← alg.sign pk sk m` if `enc e = .ok m`; verification accepts
only `.ok σ` on an `e` that encodes, and then runs `alg.verify` on the encoding. -/
def scheme (alg : SignatureAlg (OracleComp spec) M PK SK S) (enc : E → Except ε M) :
    SignatureAlg (OracleComp spec) E PK SK (Except ε S) where
  keygen := alg.keygen
  sign pk sk e := match enc e with
    | .error x => pure (.error x)
    | .ok m => Except.ok <$> alg.sign pk sk m
  verify pk e s := match enc e, s with
    | .ok m, .ok σ => alg.verify pk m σ
    | _, _ => pure false

/-- Over `ProbComp` the wrapper is `Reduction.Guarded.scheme`. -/
theorem scheme_eq_guarded (alg : SignatureAlg ProbComp M PK SK S) (enc : E → Except ε M) :
    scheme alg enc = Reduction.Guarded.scheme alg enc := rfl

/-- Interpreting the ambient oracles commutes with the wrapper. -/
theorem map_scheme {ι' : Type} {spec' : OracleSpec ι'}
    (alg : SignatureAlg (OracleComp spec) M PK SK S) (enc : E → Except ε M)
    (handler : QueryImpl spec (OracleComp spec')) :
    (scheme alg enc).map (simulateQ' handler) = scheme (alg.map (simulateQ' handler)) enc := by
  apply SignatureAlg.ext
  · rfl
  · funext pk sk e
    simp only [SignatureAlg.map_sign, scheme]
    cases enc e <;> simp
  · funext pk e s
    simp only [SignatureAlg.map_verify, scheme]
    cases enc e <;> cases s <;> simp

/-- How the wrapper answers the forger's queries: every ambient query is forwarded; a signing
query `e` is answered with the error if `enc e` fails, and otherwise by exactly one query
`enc e` to the wrapper's own signing oracle. -/
def signingImpl (enc : E → Except ε M) :
    QueryImpl (spec + (E →ₒ Except ε S)) (OracleComp (spec + (M →ₒ S)))
  | .inl t => (query (spec := spec + (M →ₒ S)) (.inl t) : OracleComp _ (spec.Range t))
  | .inr e => match enc e with
    | .error x => pure (.error x)
    | .ok m => Except.ok <$> (query (spec := spec + (M →ₒ S)) (.inr m) : OracleComp _ S)

/-- **The wrapper adversary** (strong unforgeability): run the forger once under `signingImpl`,
translate its output by `Reduction.Guarded.readForgery`. -/
def reduceS (alg : SignatureAlg (OracleComp spec) M PK SK S) (enc : E → Except ε M)
    (fallback : M × S) (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.StrongUnforgeableAdversary alg where
  main pk := Reduction.Guarded.readForgery enc fallback <$>
    simulateQ (signingImpl enc) (adv.main pk)

/-- Mapping an adversary's output leaves its signing log unchanged. -/
theorem runWithSigningOracle_map (alg : SignatureAlg (OracleComp spec) M PK SK S) (pk : PK)
    (sk : SK) {α β : Type} (f : α → β) (oa : OracleComp (spec + (M →ₒ S)) α) :
    alg.runWithSigningOracle pk sk (f <$> oa) =
      (Prod.map f id) <$> alg.runWithSigningOracle pk sk oa := by
  simp [SignatureAlg.runWithSigningOracle]
  rfl

/-- Running the wrapper's simulation against the signing oracle of `alg` is running the forger
against the signing oracle of `scheme alg enc`, with the log translated. -/
theorem runWithSigningOracle_signingImpl (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (enc : E → Except ε M) (pk : PK) (sk : SK) {α : Type}
    (oa : OracleComp (spec + (E →ₒ Except ε S)) α) :
    alg.runWithSigningOracle pk sk (simulateQ (signingImpl enc) oa) =
      (fun z => (z.1, Reduction.Guarded.decodeLog enc z.2)) <$>
        (scheme alg enc).runWithSigningOracle pk sk oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [SignatureAlg.runWithSigningOracle, Reduction.Guarded.decodeLog]
  | query_bind t k ih =>
    simp only [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
      QueryImpl.passthrough_add, Reduction.Guarded.decodeLog] at ih
    cases t with
    | inl t =>
      simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle,
        QueryImpl.passthrough_add, ih, Reduction.Guarded.decodeLog]
    | inr e =>
      cases he : enc e with
      | error x =>
        simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle, scheme,
          QueryImpl.passthrough_add, ih, Reduction.Guarded.decodeLog, he]
      | ok m =>
        simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle, scheme,
          QueryImpl.passthrough_add, ih, Reduction.Guarded.decodeLog, he]

open scoped Classical in
/-- The strong-unforgeability experiment of the wrapper, written over the run of the forger. -/
theorem strongUnforgeableExperiment_reduceS (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.strongUnforgeableExperiment (reduceS alg enc fallback adv) = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← (scheme alg enc).runWithSigningOracle pk sk (adv.main pk)
      let verified ← alg.verify pk (Reduction.Guarded.readForgery enc fallback out).1
        (Reduction.Guarded.readForgery enc fallback out).2
      return !SignatureAlg.signingLogContains (Reduction.Guarded.decodeLog enc log)
        (Reduction.Guarded.readForgery enc fallback out).1
        (Reduction.Guarded.readForgery enc fallback out).2 && verified := by
  simp only [SignatureAlg.strongUnforgeableExperiment, reduceS,
    runWithSigningOracle_map, bind_map_left]
  simp only [runWithSigningOracle_signingImpl alg enc, bind_map_left]
  rfl

open scoped Classical in
/-- **Advantage transfer under every stateful oracle interpretation.**  If `enc` is injective on
its domain, then for every interpretation `so` of the ambient oracles with state (for example the
lazy random oracle) and every initial state, the probability that the forger wins the SUF-CMA game
against `scheme alg enc` is at most the probability that `reduceS` wins it against `alg`. -/
theorem prEvent_strongUnforgeableExperiment_le (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (enc : E → Except ε M) (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (fallback : M × S) (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc))
    {σ : Type} (so : QueryImpl spec (StateT σ ProbComp)) (state : σ) :
    Pr{let z ← (simulateQ so (SignatureAlg.strongUnforgeableExperiment adv)).run state}[
        z.1 = true] ≤
      Pr{let z ← (simulateQ so (SignatureAlg.strongUnforgeableExperiment
        (reduceS alg enc fallback adv))).run state}[z.1 = true] := by
  classical
  rw [strongUnforgeableExperiment_reduceS]
  simp only [SignatureAlg.strongUnforgeableExperiment, simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨pk, sk⟩, st⟩
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨⟨e, s⟩, log⟩, st'⟩
  cases he : enc e with
  | error x => simp [scheme, he, StateT.run_pure]
  | ok m =>
    cases s with
    | error x => simp [scheme, he, StateT.run_pure]
    | ok σ' =>
      simp only [scheme, Reduction.Guarded.readForgery, he]
      apply prEvent_bind_mono_of_forall_le
      rintro ⟨verified, st''⟩
      simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
      by_cases hf : (⟨e, Except.ok σ'⟩ : (_ : E) × Except ε S) ∈ log
      · simp [SignatureAlg.signingLogContains, hf]
      · have ht := Reduction.Guarded.pairFresh_of_pairFresh enc hinj log e m σ' he hf
        simp [SignatureAlg.signingLogContains, ht, hf]

/-- **Advantage transfer in the random-oracle model.**  The SUF-CMA advantage of any forger
against `scheme alg enc` in the random-oracle runtime is at most that of `reduceS` against
`alg`. -/
theorem strongUnforgeableAdvantage_le {ιh : Type} {hs : OracleSpec ιh}
    [DecidableEq ιh] [∀ t, SampleableType (hs.Range t)]
    (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (enc : E → Except ε M) (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (fallback : M × S) (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.strongUnforgeableAdvantage (ProbCompRuntime.rom hs) adv ≤
      SignatureAlg.strongUnforgeableAdvantage (ProbCompRuntime.rom hs)
        (reduceS alg enc fallback adv) := by
  let : MeasurableSpace (Bool × hs.QueryCache) := ⊤
  have h := prEvent_strongUnforgeableExperiment_le alg enc hinj fallback adv
    (romImpl hs) (∅ : hs.QueryCache)
  rw [SignatureAlg.strongUnforgeableAdvantage, SignatureAlg.strongUnforgeableAdvantage,
    ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist]
  simp only [StateT.run'_eq, evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
  simpa only [prEvent_eq_evalDist_of_discrete, Set.preimage, Set.mem_singleton_iff] using h

/-- **Query budget of the wrapper in the random-oracle model**: at most `qh` hash queries and at
most `qs` signing queries if the forger makes at most that many (every hash query is forwarded
once; a signing query costs one signing query, or none if its encoding fails). -/
theorem romQueryBound_reduceS {ιh : Type} {hs : OracleSpec ιh}
    (alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary (scheme alg enc)) {qh qs : ℕ}
    (h : adv.RomQueryBound qh qs) : (reduceS alg enc fallback adv).RomQueryBound qh qs := by
  intro pk
  obtain ⟨hh, hs⟩ := h pk
  constructor
  · simp only [SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary, reduceS,
      isQueryBoundP_map_iff]
    apply hh.simulateQ_of_step
    · rintro ((_ | _) | e) ht
      · simp [SignatureAlg.IsHashQuery] at ht
      · simp [signingImpl, SignatureAlg.IsHashQuery]
      · simp [SignatureAlg.IsHashQuery] at ht
    · rintro ((_ | _) | e) ht
      · simp [signingImpl, SignatureAlg.IsHashQuery]
      · simp [SignatureAlg.IsHashQuery] at ht
      · simp only [signingImpl]
        cases enc e <;> simp [SignatureAlg.IsHashQuery]
  · simp only [SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary, reduceS,
      isQueryBoundP_map_iff]
    apply hs.simulateQ_of_step
    · rintro ((_ | _) | e) ht
      · simp [SignatureAlg.IsSignQuery] at ht
      · simp [SignatureAlg.IsSignQuery] at ht
      · simp only [signingImpl]
        cases enc e <;> simp [SignatureAlg.IsSignQuery]
    · rintro ((_ | _) | e) ht
      · simp [signingImpl, SignatureAlg.IsSignQuery]
      · simp [signingImpl, SignatureAlg.IsSignQuery]
      · simp [SignatureAlg.IsSignQuery] at ht

end GuardedRom

end E2E

#print axioms E2E.GuardedRom.map_scheme
#print axioms E2E.GuardedRom.prEvent_strongUnforgeableExperiment_le
#print axioms E2E.GuardedRom.strongUnforgeableAdvantage_le
#print axioms E2E.GuardedRom.romQueryBound_reduceS
