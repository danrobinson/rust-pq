import Reduction.Final
import HashSig.SLHDSA.External

/-!
# The external (pure, with context string) interface of SLH-DSA

`Reduction.slhdsa_euf_cma` is about the FIPS 205 *internal* algorithms (Alg. 18–20), whose
messages are the internal `M'`.  The interface a user of the scheme calls is the external pure one
(FIPS 205 Alg. 22 `slh_sign`, Alg. 24 `slh_verify`): the caller gives a message `M` and a context
string `ctx`, and the internal algorithm is run on `M' = 0x00 ‖ toByte(|ctx|,1) ‖ ctx ‖ M`
(`SLHDSA.External.encodePureMessage`); a context longer than 255 bytes is an error on signing and
a rejection on verification.

This file

* defines the external pure scheme `externalAlg` as a `SignatureAlg` over messages
  `(message, context)` (both arbitrary byte lists), built from VCVio's
  `External.signPureWithRandomizer` / `External.verifyPure` (`externalAlg_sign`,
  `externalAlg_verify_ok`, `externalAlg_verify_error`);
* proves that the encoding `(ctx, M) ↦ M'` is injective where it is defined
  (`encodePureMessage_injective`);
* gives the explicit adversary transformation `toInternal` from forgers against `externalAlg` to
  forgers against `internalAlg`, with `Adv_ext(A) ≤ Adv_int(toInternal A)`
  (`external_advantage_le`) and the same signing-query budget (`toInternal_queryBound`);
* transfers any bound valid for all internal forgers (`external_bound_of_internal_bound`), and
  instantiates this at `slhdsa_euf_cma` (`slhdsa_pure_euf_cma`);
* shows that the external scheme is correct for contexts of at most 255 bytes
  (`externalAlg_correct`), so the statement is about a functioning scheme.

The first part (`Reduction.Guarded`) is generic: a signature scheme whose messages are passed
through a partial injective encoding.

Scope: pure mode only (not the pre-hash variants, Alg. 23/25); single key.  This file is EUF-CMA;
SUF-CMA of `externalAlg` is proved too: transfer in `Reduction/ExternalSuf.lean`, theorem
`slhdsa_pure_suf_cma_final_split` (`Reduction/HeadlineSplit.lean`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

/-! ## Generic part: a scheme behind a partial message encoding -/

namespace Guarded

variable {E M PK SK S ε : Type}

/-- The scheme `alg` behind a partial message encoding `enc : E → Except ε M`.

* signing `e`: if `enc e = .error x` the result is the error value `.error x` (no call to
  `alg.sign`); if `enc e = .ok m` it is `.ok σ` with `σ ← alg.sign pk sk m`;
* verifying `(e, s)`: `alg.verify pk m σ` if `enc e = .ok m` and `s = .ok σ`, and `false`
  otherwise.  (An error value is never an accepted signature.)

Signatures are `Except ε S` because the signing algorithm of the external interface is a total
function that can return an error; the signing oracle of the EUF-CMA game then returns that
error to the adversary, exactly as the real interface does. -/
def scheme (alg : SignatureAlg ProbComp M PK SK S) (enc : E → Except ε M) :
    SignatureAlg ProbComp E PK SK (Except ε S) where
  keygen := alg.keygen
  sign pk sk e := match enc e with
    | .error x => pure (.error x)
    | .ok m => Except.ok <$> alg.sign pk sk m
  verify pk e s := match enc e, s with
    | .ok m, .ok σ => alg.verify pk m σ
    | _, _ => pure false

/-- How the reduction answers the forger's queries: uniform-sampling queries are forwarded; a
signing query `e` is answered locally with the error if `enc e` is an error, and otherwise by
exactly one query `enc e` to the reduction's own signing oracle. -/
def signingImpl (enc : E → Except ε M) :
    QueryImpl (unifSpec + (E →ₒ Except ε S)) (OracleComp (unifSpec + (M →ₒ S)))
  | .inl t => (query (spec := unifSpec + (M →ₒ S)) (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr e => match enc e with
    | .error x => pure (.error x)
    | .ok m => Except.ok <$> (query (spec := unifSpec + (M →ₒ S)) (.inr m) : OracleComp _ S)

/-- Translate the forger's final output: the encoded message with the signature if both are
well-formed, and the fixed pair `fallback` otherwise (in which case the forger has lost its own
game: its output is rejected by `scheme alg enc`). -/
def readForgery (enc : E → Except ε M) (fallback : M × S) (out : E × Except ε S) : M × S :=
  match enc out.1, out.2 with
  | .ok m, .ok σ => (m, σ)
  | _, _ => fallback

/-- **The reduction.**  Runs the forger once, answering its queries by `signingImpl`, and
translates its output by `readForgery`.  No choice, no search, no sampling of its own. -/
def reduce (alg : SignatureAlg ProbComp M PK SK S) (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.UnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.UnforgeableAdversary alg where
  main pk := readForgery enc fallback <$> simulateQ (signingImpl enc) (adv.main pk)

/-- The signing log of the reduction, computed from the log of the forger: entries with an
error are dropped (they caused no query), the others are encoded. -/
def decodeLog (enc : E → Except ε M) (log : QueryLog (E →ₒ Except ε S)) : QueryLog (M →ₒ S) :=
  log.filterMap fun entry =>
    match enc entry.1, (entry.2 : Except ε S) with
    | .ok m, .ok σ => some ⟨m, σ⟩
    | _, _ => none

/-- Running the reduction's simulation against the real signing oracle of `alg` is running the
forger against the signing oracle of `scheme alg enc`, with the log translated. -/
theorem runWithSigningOracle_signingImpl (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (pk : PK) (sk : SK) {α : Type}
    (oa : OracleComp (unifSpec + (E →ₒ Except ε S)) α) :
    alg.runWithSigningOracle pk sk (simulateQ (signingImpl enc) oa) =
      (fun z => (z.1, decodeLog enc z.2)) <$>
        (scheme alg enc).runWithSigningOracle pk sk oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [SignatureAlg.runWithSigningOracle, decodeLog]
  | query_bind t k ih =>
    simp only [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
      QueryImpl.passthrough_add, decodeLog] at ih
    cases t with
    | inl t =>
      simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle,
        QueryImpl.passthrough_add, ih, decodeLog]
    | inr e =>
      cases he : enc e with
      | error x =>
        simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle, scheme,
          QueryImpl.passthrough_add, ih, decodeLog, he]
      | ok m =>
        simp [SignatureAlg.runWithSigningOracle, signingImpl, SignatureAlg.signingOracle, scheme,
          QueryImpl.passthrough_add, ih, decodeLog, he]

/-- Freshness transfers: if `enc` is injective on its domain and `e` (with `enc e = .ok m`) was
not submitted by the forger, then `m` was not submitted by the reduction. -/
theorem fresh_of_fresh [DecidableEq E] [DecidableEq M] (enc : E → Except ε M)
    (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (log : QueryLog (E →ₒ Except ε S)) (e : E) (m : M) (he : enc e = .ok m)
    (hfresh : log.wasQueried e = false) : (decodeLog enc log).wasQueried m = false := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst, decide_eq_false_iff_not] at hfresh ⊢
  intro hm
  obtain ⟨⟨m', σ⟩, hmem, rfl⟩ := List.mem_map.mp hm
  obtain ⟨⟨e', s⟩, hw, hdec⟩ := List.mem_filterMap.mp hmem
  apply hfresh
  cases he' : enc e' with
  | error x => simp [he'] at hdec
  | ok m'' =>
    cases s with
    | error x => simp [he'] at hdec
    | ok σ' =>
      simp only [he', Option.some.injEq, Sigma.mk.injEq] at hdec
      obtain ⟨rfl, -⟩ := hdec
      have := hinj e e' _ he he'
      subst this
      exact List.mem_map.mpr ⟨_, hw, rfl⟩

/-- Mapping an adversary's output leaves its signing log unchanged. -/
theorem runWithSigningOracle_map (alg : SignatureAlg ProbComp M PK SK S) (pk : PK) (sk : SK)
    {α β : Type} (f : α → β) (oa : OracleComp (unifSpec + (M →ₒ S)) α) :
    alg.runWithSigningOracle pk sk (f <$> oa) =
      (Prod.map f id) <$> alg.runWithSigningOracle pk sk oa := by
  simp [SignatureAlg.runWithSigningOracle]
  rfl

open scoped Classical in
/-- The experiment of the reduction, written over the run of the original forger. -/
theorem unforgeableExperiment_reduce (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.UnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.unforgeableExperiment (reduce alg enc fallback adv) = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← (scheme alg enc).runWithSigningOracle pk sk (adv.main pk)
      let verified ← alg.verify pk (readForgery enc fallback out).1 (readForgery enc fallback out).2
      return !(decodeLog enc log).wasQueried (readForgery enc fallback out).1 && verified := by
  simp only [SignatureAlg.unforgeableExperiment, reduce, runWithSigningOracle_map,
    bind_map_left]
  simp only [runWithSigningOracle_signingImpl alg enc, bind_map_left]
  rfl

open scoped Classical in
/-- **Advantage transfer (generic).**  If `enc` is injective on its domain, the EUF-CMA advantage
of any forger against `scheme alg enc` is at most that of `reduce alg enc fallback adv` against
`alg`. -/
theorem unforgeableAdvantage_le (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (fallback : M × S) (adv : SignatureAlg.UnforgeableAdversary (scheme alg enc)) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduce alg enc fallback adv) := by
  have key : Pr{let b ← SignatureAlg.unforgeableExperiment adv}[b = true] ≤
      Pr{let b ← SignatureAlg.unforgeableExperiment (reduce alg enc fallback adv)}[b = true] := by
    rw [unforgeableExperiment_reduce]
    simp only [SignatureAlg.unforgeableExperiment]
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
        by_cases hf : log.wasQueried e = true
        · simp [hf]
        · have hf' : log.wasQueried e = false := by simpa using hf
          have ht := fresh_of_fresh enc hinj log e m he hf'
          simp [ht, hf']
  simpa only [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using key

/-- **Query budget of the reduction**: at most as many signing queries as the forger (a signing
query with a failing encoding costs none). -/
theorem reduce_queryBound (alg : SignatureAlg ProbComp M PK SK S)
    (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.UnforgeableAdversary (scheme alg enc)) (qs : ℕ) (pk : PK)
    (h : IsQueryBoundP (adv.main pk) (fun i => i.isRight = true) qs) :
    IsQueryBoundP ((reduce alg enc fallback adv).main pk) (fun i => i.isRight = true) qs := by
  simp only [reduce, isQueryBoundP_map_iff]
  apply h.simulateQ_of_step
  · rintro (t | e) ht
    · simp at ht
    · simp only [signingImpl]
      cases enc e <;> simp
  · rintro (t | e) ht
    · simp [signingImpl]
    · simp at ht

end Guarded

/-! ## The pure-mode message encoding -/

/-- The partial encoding of the external pure interface on `(message, context)` pairs:
`M' = 0x00 ‖ toByte(|ctx|,1) ‖ ctx ‖ M`, an error if the context is longer than 255 bytes. -/
def pureEncode (mc : List Byte × List Byte) : Except External.Error (List Byte) :=
  External.encodePureMessage mc.2 mc.1

/-- `encodePureMessage` succeeds only on contexts of at most 255 bytes, with the FIPS value. -/
theorem encodePureMessage_ok_iff (context message enc : List Byte) :
    External.encodePureMessage context message = .ok enc ↔
      context.length ≤ 255 ∧ enc = [0, UInt8.ofNat context.length] ++ context ++ message := by
  by_cases h : context.length ≤ 255
  · rw [External.encodePureMessage_eq_ok context message h]
    simp [h, eq_comm]
  · unfold External.encodePureMessage External.encodeMessage
    rw [External.requireContext_eq_error context (by omega)]
    simp only [h, false_and, iff_false]
    intro hc
    cases hc

/-- **Injectivity of the pure-mode encoding** `(ctx, M) ↦ 0x00 ‖ toByte(|ctx|,1) ‖ ctx ‖ M` on
contexts of at most 255 bytes: two (message, context) pairs with the same successful encoding
are equal.  (The length byte determines `|ctx|` because `|ctx| < 256`.) -/
theorem encodePureMessage_injective (context context' message message' enc : List Byte)
    (h : External.encodePureMessage context message = .ok enc)
    (h' : External.encodePureMessage context' message' = .ok enc) :
    context = context' ∧ message = message' := by
  obtain ⟨hl, rfl⟩ := (encodePureMessage_ok_iff _ _ _).1 h
  obtain ⟨hl', he⟩ := (encodePureMessage_ok_iff _ _ _).1 h'
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at he
  obtain ⟨hlen, happ⟩ := he
  have hlen' : context.length = context'.length := by
    have := congrArg UInt8.toNat hlen
    simp only [UInt8.toNat_ofNat'] at this
    omega
  exact List.append_inj happ hlen'

/-- Injectivity in the form used by the generic reduction. -/
theorem pureEncode_injective (e e' : List Byte × List Byte) (m : List Byte)
    (h : pureEncode e = .ok m) (h' : pureEncode e' = .ok m) : e = e' := by
  obtain ⟨h1, h2⟩ := encodePureMessage_injective _ _ _ _ _ h h'
  exact Prod.ext h2 h1

/-! ## The external pure scheme -/

section External

variable (vp : ValidatedParams) (prims : Primitives vp.params)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- **The external pure SLH-DSA scheme** (FIPS 205 Alg. 21, 22, 24) as a signature scheme whose
messages are pairs `(message, context)` of arbitrary byte lists.

* key generation is that of `internalAlg` (`PK.seed ← pkSeedDist`, `SK.seed`, `SK.prf` uniform);
* signing `(M, ctx)` draws `opt_rand ← optRand pk` and returns
  `External.signPureWithRandomizer vp prims M ctx sk opt_rand` (`externalAlg_sign`): the error
  `contextTooLong` if `|ctx| > 255` (then nothing is sampled), and otherwise `.ok` of the
  internal signature of `M' = 0 ‖ |ctx| ‖ ctx ‖ M`;
* verifying `(M, ctx)` against `.ok σ` returns `External.verifyPure vp prims M σ ctx pk`
  (`externalAlg_verify_ok`; `false` if `|ctx| > 255`), and against an error value returns `false`
  (`externalAlg_verify_error`).

The signature type is `Except External.Error (SignatureCore …)`, the return type of VCVio's
`signPureWithRandomizer`: the scheme's `sign` is then *literally* the external signing function
(no behaviour is invented for over-long contexts), the signing oracle of the EUF-CMA game hands
the error to the adversary just as the API does, and an error value is never accepted by
`verify`, so it cannot be a forgery.  (`Option` would lose nothing security-relevant but would
not be the type of the function the Rust link is stated against.)

Defined as `Guarded.scheme (internalAlg …) pureEncode`. -/
noncomputable def externalAlg :
    SignatureAlg ProbComp (List Byte × List Byte) (PublicKeyCore prims.core)
      (SecretKeyCore prims.core)
      (Except External.Error (GeneralScheme.SignatureCore vp prims.core)) :=
  Guarded.scheme (internalAlg vp prims optRand pkSeedDist) pureEncode

/-- Key generation of the external scheme is that of the internal one. -/
theorem externalAlg_keygen :
    (externalAlg vp prims optRand pkSeedDist).keygen =
      (internalAlg vp prims optRand pkSeedDist).keygen := rfl

/-- Signing in the external scheme is `External.signPureWithRandomizer` at
`opt_rand ← optRand pk` when the context has at most 255 bytes. -/
theorem externalAlg_sign (pk : PublicKeyCore prims.core) (sk : SecretKeyCore prims.core)
    (message context : List Byte) (h : context.length ≤ 255) :
    (externalAlg vp prims optRand pkSeedDist).sign pk sk (message, context) =
      (do let addrnd ← optRand pk
          pure (External.signPureWithRandomizer vp prims message context sk addrnd)) := by
  simp only [externalAlg, Guarded.scheme, pureEncode, External.signPureWithRandomizer,
    External.encodePureMessage_eq_ok context message h, internalAlg]
  simp

/-- Signing with an over-long context returns the error, which is also what
`External.signPureWithRandomizer` returns for every `opt_rand`. -/
theorem externalAlg_sign_tooLong (pk : PublicKeyCore prims.core) (sk : SecretKeyCore prims.core)
    (message context : List Byte) (h : 255 < context.length) :
    (externalAlg vp prims optRand pkSeedDist).sign pk sk (message, context) =
        pure (.error (.contextTooLong context.length)) ∧
      ∀ addrnd, External.signPureWithRandomizer vp prims message context sk addrnd =
        .error (.contextTooLong context.length) := by
  have he : External.encodePureMessage context message =
      .error (.contextTooLong context.length) := by
    unfold External.encodePureMessage External.encodeMessage
    rw [External.requireContext_eq_error context h]; rfl
  constructor
  · simp only [externalAlg, Guarded.scheme, pureEncode, he]
  · intro addrnd
    simp only [External.signPureWithRandomizer, he]
    rfl

/-- Verification of a signature value in the external scheme is `External.verifyPure`. -/
theorem externalAlg_verify_ok (pk : PublicKeyCore prims.core) (message context : List Byte)
    (σ : GeneralScheme.SignatureCore vp prims.core) :
    (externalAlg vp prims optRand pkSeedDist).verify pk (message, context) (.ok σ) =
      pure (External.verifyPure vp prims message σ context pk) := by
  simp only [externalAlg, Guarded.scheme, pureEncode, External.verifyPure]
  cases External.encodePureMessage context message <;> rfl

/-- An error value is never accepted. -/
theorem externalAlg_verify_error (pk : PublicKeyCore prims.core) (mc : List Byte × List Byte)
    (x : External.Error) :
    (externalAlg vp prims optRand pkSeedDist).verify pk mc (.error x) = pure false := by
  simp only [externalAlg, Guarded.scheme]
  cases pureEncode mc <;> rfl

/-- **Non-vacuity: the external scheme is correct.**  For every context of at most 255 bytes,
every message, every key pair produced by key generation from any seeds and every `opt_rand`,
signing succeeds (returns `.ok σ`) and `σ` is accepted for the same message and context.  This
is `External.verifyPure_signPureWithRandomizer` restated for `externalAlg`. -/
theorem externalAlg_correct (message context : List Byte) (hc : context.length ≤ 255)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y) :
    ∃ σ, External.signPureWithRandomizer vp prims message context
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd = .ok σ ∧
      (externalAlg vp prims optRand pkSeedDist).verify
        (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1 (message, context) (.ok σ) =
          pure true := by
  have h := External.verifyPure_signPureWithRandomizer vp prims message context skSeed skPrf
    pkSeed addrnd hc
  simp only [External.keygenWithSeeds] at h
  cases hs : External.signPureWithRandomizer vp prims message context
      (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd with
  | error x => rw [hs] at h; cases h
  | ok σ =>
    rw [hs] at h
    refine ⟨σ, rfl, ?_⟩
    rw [externalAlg_verify_ok]
    exact congrArg pure (Except.ok.inj h)

/-- A chosen-message forger against the external pure scheme: given the public key and a signing
oracle taking `(message, context)` pairs, it outputs a pair `(message, context)` and a candidate
signature.  It wins (`SignatureAlg.unforgeableExperiment`) if that exact pair
`(message, context)` was never submitted to the signing oracle and the signature is accepted
(so in particular the context has at most 255 bytes and the signature is not an error value). -/
abbrev ExtForger : Type :=
  SignatureAlg.UnforgeableAdversary (externalAlg vp prims optRand pkSeedDist)

variable {vp prims optRand pkSeedDist}

/-- A fixed, syntactically well-formed signature (every node equal to `y`), used only as the
output of `toInternal` when the external forger's own output is malformed. -/
def constSig (y : prims.Y) : GeneralScheme.SignatureCore vp prims.core :=
  ⟨y, Vector.replicate _ ⟨y, Vector.replicate _ y⟩,
    Vector.replicate _ ⟨Vector.replicate _ y, Vector.replicate _ y⟩⟩

/-- **The reduction from the external to the internal game.**  `toInternal A`, on input `pk`:
runs `A pk` once; forwards its sampling queries; answers a signing query `(M, ctx)` with the
error `contextTooLong` if `|ctx| > 255` (no oracle call) and otherwise with `.ok σ` where `σ` is
the answer of its own signing oracle on `M' = 0 ‖ |ctx| ‖ ctx ‖ M` (one call); when `A` outputs
`((M, ctx), .ok σ)` with `|ctx| ≤ 255` it outputs `(M', σ)`, and otherwise (where `A` has lost)
the fixed pair `([], constSig default)`. -/
noncomputable def toInternal [Inhabited prims.Y] (A : ExtForger vp prims optRand pkSeedDist) :
    Forger vp prims optRand pkSeedDist :=
  Guarded.reduce (internalAlg vp prims optRand pkSeedDist) pureEncode ([], constSig default) A

/-- **External advantage ≤ internal advantage.** -/
theorem external_advantage_le [Inhabited prims.Y] (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (toInternal A) :=
  Guarded.unforgeableAdvantage_le _ _ pureEncode_injective _ A

/-- **Resources of `toInternal`**: at most as many signing queries as `A`. -/
theorem toInternal_queryBound [Inhabited prims.Y] (A : ExtForger vp prims optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((toInternal A).main pk) (fun i => i.isRight = true) qs :=
  fun pk => Guarded.reduce_queryBound _ _ _ A qs pk (hA pk)

/-- **Transfer lemma.**  Any bound `β` on the EUF-CMA advantage of *all* forgers against the
internal scheme (as a function of the forger) bounds the advantage of every forger `A` against
the external pure scheme by `β (toInternal A)`.  Re-instantiate with any internal theorem. -/
theorem external_bound_of_internal_bound [Inhabited prims.Y]
    (β : Forger vp prims optRand pkSeedDist → ℝ≥0∞)
    (hβ : ∀ B : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ β (toInternal A) :=
  (external_advantage_le A).trans (hβ _)

end External

/-! ## Composition with the standard-model theorem -/

section Headline

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **Standard-model EUF-CMA security of the external pure interface of SLH-DSA** (FIPS 205
Alg. 21/22/24, messages with context strings).  (Phase-1 bound; superseded by
`Reduction.slhdsa_pure_euf_cma_final_split` and `slhdsa_pure_suf_cma_final_split`,
`Reduction/HeadlineSplit.lean`.)

For every chosen-message forger `A` against `externalAlg vp prims optRand pkSeedDist` — a forgery
is a `(message, context)` pair never submitted to the signing oracle, with a signature that
`External.verifyPure` accepts — the advantage of `A` is at most the eight-term bound of
`slhdsa_euf_cma` at the internal forger `toInternal A` (which runs `A` once and makes at most as
many signing queries, `toInternal_queryBound`).

Scope: pure mode only (not pre-hash); this theorem is EUF-CMA (external SUF-CMA is proved as
`slhdsa_pure_suf_cma_final_split`); single key; the eight advantages of this phase-1 bound are
not bounded here (see `slhdsa_euf_cma` for all caveats, which carry over). -/
theorem slhdsa_pure_euf_cma (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      bound pkSeedDist (bPrf (toInternal A)) (bPrfMsg (toInternal A)) (bItsr (toInternal A))
        (bOpenPre (toInternal A)) (bTcr (toInternal A))
        (rUd pkSeedDist (bWots (toInternal A))) (rPre pkSeedDist (bWots (toInternal A)))
        (rTcr pkSeedDist (bWots (toInternal A))) :=
  external_bound_of_internal_bound _ (fun B => slhdsa_euf_cma hS B) A

/-- The bound together with the `qs`-dependent resources of the composed reductions: if `A`
makes at most `qs` signing queries, so does `toInternal A`, and the query bounds of
`slhdsa_euf_cma_resources` hold for the adversaries built from it. -/
theorem slhdsa_pure_euf_cma_resources (hS : Structural vp prims)
    (A : ExtForger vp prims optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
        bound pkSeedDist (bPrf (toInternal A)) (bPrfMsg (toInternal A)) (bItsr (toInternal A))
          (bOpenPre (toInternal A)) (bTcr (toInternal A))
          (rUd pkSeedDist (bWots (toInternal A))) (rPre pkSeedDist (bWots (toInternal A)))
          (rTcr pkSeedDist (bWots (toInternal A))) ∧
      IsQueryBoundP (bPrf (toInternal A)) (fun i => i.isRight = true)
        (2 ^ vp.params.hp * vp.params.len + qs * signReads vp) ∧
      IsQueryBoundP (bPrfMsg (toInternal A)) (fun i => i.isRight = true) qs ∧
      IsQueryBoundP (bItsr (toInternal A)).main (fun i => i.isRight = true) qs :=
  ⟨slhdsa_pure_euf_cma hS A,
    (slhdsa_euf_cma_resources hS (toInternal A) qs (toInternal_queryBound A qs hA)).2⟩

end Headline

#print axioms Guarded.unforgeableAdvantage_le
#print axioms Guarded.reduce_queryBound
#print axioms encodePureMessage_injective
#print axioms externalAlg_sign
#print axioms externalAlg_sign_tooLong
#print axioms externalAlg_verify_ok
#print axioms externalAlg_correct
#print axioms external_advantage_le
#print axioms toInternal_queryBound
#print axioms external_bound_of_internal_bound
#print axioms slhdsa_pure_euf_cma
#print axioms slhdsa_pure_euf_cma_resources

end Reduction
