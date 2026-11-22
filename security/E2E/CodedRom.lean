import E2E.GuardedRom

/-!
# A scheme seen through encodings of keys and signatures, over an arbitrary oracle interface

`Reduction.Coded` (`Reduction/Bytes.lean`) transfers EUF-CMA / SUF-CMA from a typed scheme over
`ProbComp` to the same scheme seen through encodings of keys and signatures (the byte-level
scheme).  This is the same transfer for schemes over an arbitrary ambient interface `spec`, in
particular the random-oracle interface `unifSpec + hashSpec …`:

* `CodedRom.View alg balg` — the same fields as `Reduction.Coded.View`;
* `CodedRom.reduceS` — the typed forger built from a byte forger: it encodes the public key, runs
  the byte forger once, forwards every ambient query (sampling and hash queries), answers a
  signing query by one typed signing query whose answer it encodes, and parses the forgery;
* `prEvent_strongUnforgeableExperiment_le` (every stateful interpretation of the ambient
  oracles), `strongUnforgeableAdvantage_le` (random-oracle runtime);
* `romQueryBound_reduceS` — the hash-query and signing-query budgets are preserved.
-/

open OracleComp OracleSpec ENNReal

namespace E2E

namespace CodedRom

variable {ι : Type} {spec : OracleSpec ι} {M PK SK S PKb SKb Sb : Type}

/-- `balg` is `alg` seen through encodings of public keys, secret keys and signatures, with a
signature parser `decS` that accepts only canonical encodings (as `Reduction.Coded.View`). -/
structure View (alg : SignatureAlg (OracleComp spec) M PK SK S)
    (balg : SignatureAlg (OracleComp spec) M PKb SKb Sb) where
  /-- encoding of public keys -/
  encPk : PK → PKb
  /-- encoding of secret keys -/
  encSk : SK → SKb
  /-- encoding of signatures -/
  encS : S → Sb
  /-- parser of signatures -/
  decS : Sb → Option S
  /-- key generation of `balg`: generate a key pair of `alg`, encode both keys -/
  keygen_eq : balg.keygen = (fun ks => (encPk ks.1, encSk ks.2)) <$> alg.keygen
  /-- signing under encoded keys: sign in `alg`, encode the signature -/
  sign_eq : ∀ pk sk m, balg.sign (encPk pk) (encSk sk) m = encS <$> alg.sign pk sk m
  /-- verifying under an encoded public key: parse the signature; reject if that fails;
  otherwise verify in `alg` -/
  verify_eq : ∀ pk m sb, balg.verify (encPk pk) m sb =
    match decS sb with
    | some s => alg.verify pk m s
    | none => pure false
  /-- the parser accepts only canonical encodings -/
  canonical : ∀ sb s, decS sb = some s → encS s = sb

variable {alg : SignatureAlg (OracleComp spec) M PK SK S}
  {balg : SignatureAlg (OracleComp spec) M PKb SKb Sb}

/-- Ambient queries are forwarded; a signing query `m` becomes one typed signing query `m`, whose
answer is encoded. -/
def signingImpl (v : View alg balg) :
    QueryImpl (spec + (M →ₒ Sb)) (OracleComp (spec + (M →ₒ S)))
  | .inl t => (query (spec := spec + (M →ₒ S)) (.inl t) : OracleComp _ (spec.Range t))
  | .inr m => v.encS <$> (query (spec := spec + (M →ₒ S)) (.inr m) : OracleComp _ S)

/-- The message with the parsed signature, `fallback` if it does not parse. -/
def readForgery (v : View alg balg) (fallback : S) (out : M × Sb) : M × S :=
  (out.1, (v.decS out.2).getD fallback)

/-- **The typed forger built from a byte forger** (strong unforgeability). -/
def reduceS (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.StrongUnforgeableAdversary alg where
  main pk := readForgery v fallback <$> simulateQ (signingImpl v) (adv.main (v.encPk pk))

/-- The byte forger's signing log, computed from the typed forger's. -/
def encodeLog (v : View alg balg) (log : QueryLog (M →ₒ S)) : QueryLog (M →ₒ Sb) :=
  log.map fun entry => ⟨entry.1, v.encS entry.2⟩

theorem runWithSigningOracle_signingImpl (v : View alg balg) (pk : PK) (sk : SK) {α : Type}
    (oa : OracleComp (spec + (M →ₒ Sb)) α) :
    balg.runWithSigningOracle (v.encPk pk) (v.encSk sk) oa =
      (fun z => (z.1, encodeLog v z.2)) <$>
        alg.runWithSigningOracle pk sk (simulateQ (signingImpl v) oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [SignatureAlg.runWithSigningOracle, encodeLog]
  | query_bind t k ih =>
    simp only [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
      QueryImpl.passthrough_add, encodeLog] at ih
    cases t with
    | inl t =>
      simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle,
        QueryImpl.passthrough_add, ih, encodeLog]
    | inr m =>
      simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle,
        QueryImpl.passthrough_add, ih, encodeLog, v.sign_eq]

/-- Pair freshness transfers (canonicity of the parser). -/
theorem pairFresh_of_pairFresh (v : View alg balg) (log : QueryLog (M →ₒ S)) (m : M) (sb : Sb)
    (s : S) (hs : v.decS sb = some s)
    (hfresh : (⟨m, sb⟩ : (_ : M) × Sb) ∉ encodeLog v log) :
    (⟨m, s⟩ : (_ : M) × S) ∉ log := by
  intro hm
  apply hfresh
  have := v.canonical sb s hs
  subst this
  exact List.mem_map.mpr ⟨⟨m, s⟩, hm, rfl⟩

open scoped Classical in
theorem strongUnforgeableExperiment_bytes (v : View alg balg)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.strongUnforgeableExperiment adv = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← alg.runWithSigningOracle pk sk
        (simulateQ (signingImpl v) (adv.main (v.encPk pk)))
      let verified ← balg.verify (v.encPk pk) out.1 out.2
      return !SignatureAlg.signingLogContains (encodeLog v log) out.1 out.2 && verified := by
  simp only [SignatureAlg.strongUnforgeableExperiment, v.keygen_eq, bind_map_left,
    runWithSigningOracle_signingImpl v]

open scoped Classical in
theorem strongUnforgeableExperiment_reduceS (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.strongUnforgeableExperiment (reduceS v fallback adv) = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← alg.runWithSigningOracle pk sk
        (simulateQ (signingImpl v) (adv.main (v.encPk pk)))
      let verified ← alg.verify pk out.1 ((v.decS out.2).getD fallback)
      return !SignatureAlg.signingLogContains log out.1 ((v.decS out.2).getD fallback) &&
        verified := by
  simp only [SignatureAlg.strongUnforgeableExperiment, reduceS,
    GuardedRom.runWithSigningOracle_map, bind_map_left]
  rfl

open scoped Classical in
/-- **Advantage transfer under every stateful oracle interpretation.** -/
theorem prEvent_strongUnforgeableExperiment_le (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg)
    {σ : Type} (so : QueryImpl spec (StateT σ ProbComp)) (state : σ) :
    Pr{let z ← (simulateQ so (SignatureAlg.strongUnforgeableExperiment adv)).run state}[
        z.1 = true] ≤
      Pr{let z ← (simulateQ so (SignatureAlg.strongUnforgeableExperiment
        (reduceS v fallback adv))).run state}[z.1 = true] := by
  classical
  rw [strongUnforgeableExperiment_reduceS, strongUnforgeableExperiment_bytes v]
  simp only [simulateQ_bind, StateT.run_bind]
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨pk, sk⟩, st⟩
  apply prEvent_bind_mono_of_forall_le
  rintro ⟨⟨⟨m, sb⟩, log⟩, st'⟩
  simp only [v.verify_eq]
  cases hs : v.decS sb with
  | none => simp [StateT.run_pure]
  | some s =>
    simp only [Option.getD_some]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨verified, st''⟩
    simp only [simulateQ_pure, StateT.run_pure, prEvent_pure]
    by_cases hf : (⟨m, sb⟩ : (_ : M) × Sb) ∈ encodeLog v log
    · simp [SignatureAlg.signingLogContains, hf]
    · have ht := pairFresh_of_pairFresh v log m sb s hs hf
      simp [SignatureAlg.signingLogContains, ht, hf]

/-- **Advantage transfer in the random-oracle model.** -/
theorem strongUnforgeableAdvantage_le {ιh : Type} {hs : OracleSpec ιh}
    [DecidableEq ιh] [∀ t, SampleableType (hs.Range t)]
    {alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {balg : SignatureAlg (OracleComp (unifSpec + hs)) M PKb SKb Sb}
    (v : View alg balg) (fallback : S) (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.strongUnforgeableAdvantage (ProbCompRuntime.rom hs) adv ≤
      SignatureAlg.strongUnforgeableAdvantage (ProbCompRuntime.rom hs)
        (reduceS v fallback adv) := by
  let : MeasurableSpace (Bool × hs.QueryCache) := ⊤
  have h := prEvent_strongUnforgeableExperiment_le v fallback adv
    (romImpl hs) (∅ : hs.QueryCache)
  rw [SignatureAlg.strongUnforgeableAdvantage, SignatureAlg.strongUnforgeableAdvantage,
    ProbCompRuntime.rom_evalDist, ProbCompRuntime.rom_evalDist]
  simp only [StateT.run'_eq, evalDist_map_of_discrete,
    MeasureTheory.Measure.map_apply Measurable.of_discrete (measurableSet_singleton true)]
  simpa only [prEvent_eq_evalDist_of_discrete, Set.preimage, Set.mem_singleton_iff] using h

/-- **Query budget**: the same numbers of hash and signing queries as the byte forger. -/
theorem romQueryBound_reduceS {ιh : Type} {hs : OracleSpec ιh}
    {alg : SignatureAlg (OracleComp (unifSpec + hs)) M PK SK S}
    {balg : SignatureAlg (OracleComp (unifSpec + hs)) M PKb SKb Sb}
    (v : View alg balg) (fallback : S) (adv : SignatureAlg.StrongUnforgeableAdversary balg)
    {qh qs : ℕ} (h : adv.RomQueryBound qh qs) : (reduceS v fallback adv).RomQueryBound qh qs := by
  intro pk
  obtain ⟨hh, hs⟩ := h (v.encPk pk)
  constructor
  · simp only [SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary, reduceS,
      isQueryBoundP_map_iff]
    apply hh.simulateQ_of_step
    · rintro ((_ | _) | m) ht
      · simp [SignatureAlg.IsHashQuery] at ht
      · simp [signingImpl, SignatureAlg.IsHashQuery]
      · simp [SignatureAlg.IsHashQuery] at ht
    · rintro ((_ | _) | m) ht
      · simp [signingImpl, SignatureAlg.IsHashQuery]
      · simp [SignatureAlg.IsHashQuery] at ht
      · simp [signingImpl, SignatureAlg.IsHashQuery]
  · simp only [SignatureAlg.StrongUnforgeableAdversary.toUnforgeableAdversary, reduceS,
      isQueryBoundP_map_iff]
    apply hs.simulateQ_of_step
    · rintro ((_ | _) | m) ht
      · simp [SignatureAlg.IsSignQuery] at ht
      · simp [SignatureAlg.IsSignQuery] at ht
      · simp [signingImpl, SignatureAlg.IsSignQuery]
    · rintro ((_ | _) | m) ht
      · simp [signingImpl, SignatureAlg.IsSignQuery]
      · simp [signingImpl, SignatureAlg.IsSignQuery]
      · simp [SignatureAlg.IsSignQuery] at ht

end CodedRom

end E2E

#print axioms E2E.CodedRom.prEvent_strongUnforgeableExperiment_le
#print axioms E2E.CodedRom.strongUnforgeableAdvantage_le
#print axioms E2E.CodedRom.romQueryBound_reduceS
