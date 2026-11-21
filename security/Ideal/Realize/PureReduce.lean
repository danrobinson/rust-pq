import Reduction.Bytes

/-!
# From the byte-level external pure scheme to the byte-level internal scheme

`Reduction.pureBytesAlg` is the external pure interface of SLH-DSA (FIPS 205 Alg. 21/22/24) on
byte strings: messages are `(message, context)` pairs, a signature is `Option (List Byte)`.
`Reduction.bytesAlg` is the internal interface (Alg. 18–20) on byte strings.  This file gives
the explicit reduction from forgers against the first to forgers against the second, directly
on byte strings (no detour through typed values):

* `OptGuard` (generic): a scheme `alg'` on messages `E` with `Option` signatures that, under the
  key pairs it generates, signs `e` by signing `enc e` in `alg` (and returns `none` when the
  partial encoding `enc` fails), and verifies `(e, some σ)` by verifying `(enc e, σ)` in `alg`.
  `OptGuard.reduceS` / `OptGuard.reduce` run the forger once, answer a signing query `e` with
  `none` (no query) if `enc e` fails and otherwise with `some` of one signing query `enc e`, and
  translate the output.  `strongUnforgeableAdvantage_le`, `unforgeableAdvantage_le`: if `enc` is
  injective on its domain, the advantage against `alg'` is at most that of the reduction against
  `alg`.
* `pureAgree`: the hypotheses hold for `pureBytesAlg` / `bytesAlg` with `enc = pureEncode`
  (`M' = 0x00 ‖ toByte(|ctx|,1) ‖ ctx ‖ M`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Ideal.Pure

set_option linter.unusedSectionVars false

namespace OptGuard

variable {E M PK SK S ε PK0 SK0 : Type}

/-- How the reduction answers the forger's queries: sampling forwarded; a signing query `e` is
answered by `none` if `enc e` fails (no query), otherwise by `some` of the answer to one signing
query `enc e`. -/
def signImpl (enc : E → Except ε M) :
    QueryImpl (unifSpec + (E →ₒ Option S)) (OracleComp (unifSpec + (M →ₒ S)))
  | .inl t => (query (spec := unifSpec + (M →ₒ S)) (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr e => match enc e with
    | .error _ => pure none
    | .ok m => some <$> (query (spec := unifSpec + (M →ₒ S)) (.inr m) : OracleComp _ S)

/-- Translate the forger's output: `(enc e, σ)` for `(e, some σ)` with `enc e` defined, the fixed
pair `fallback` otherwise. -/
def readOut (enc : E → Except ε M) (fallback : M × S) (out : E × Option S) : M × S :=
  match enc out.1, out.2 with
  | .ok m, some σ => (m, σ)
  | _, _ => fallback

/-- The reduction's signing log computed from the forger's. -/
def decodeLog (enc : E → Except ε M) (log : QueryLog (E →ₒ Option S)) : QueryLog (M →ₒ S) :=
  log.filterMap fun entry =>
    match enc entry.1, (entry.2 : Option S) with
    | .ok m, some σ => some ⟨m, σ⟩
    | _, _ => none

/-- Signing agreement under the key pair `(pk, sk)`. -/
def SignAgree (alg : SignatureAlg ProbComp M PK SK S) (alg' : SignatureAlg ProbComp E PK SK (Option S))
    (enc : E → Except ε M) (pk : PK) (sk : SK) : Prop :=
  ∀ e, alg'.sign pk sk e = match enc e with
    | .error _ => pure none
    | .ok m => some <$> alg.sign pk sk m

/-- The hypotheses of the transfer. -/
structure Agree (alg : SignatureAlg ProbComp M PK SK S)
    (alg' : SignatureAlg ProbComp E PK SK (Option S)) (enc : E → Except ε M) where
  K : ProbComp (PK0 × SK0)
  encPk : PK0 → PK
  encSk : SK0 → SK
  keygen : alg.keygen = (fun ks => (encPk ks.1, encSk ks.2)) <$> K
  keygen' : alg'.keygen = (fun ks => (encPk ks.1, encSk ks.2)) <$> K
  sign : ∀ pk sk, SignAgree alg alg' enc (encPk pk) (encSk sk)
  verify_none : ∀ pk e, alg'.verify pk e none = pure false
  verify_error : ∀ pk e x s, enc e = .error x → alg'.verify pk e (some s) = pure false
  verify_ok : ∀ pk e m s, enc e = .ok m → alg'.verify pk e (some s) = alg.verify pk m s
  inj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e'

variable {alg : SignatureAlg ProbComp M PK SK S} {alg' : SignatureAlg ProbComp E PK SK (Option S)}
  {enc : E → Except ε M}

/-- **The reduction (SUF).** -/
def reduceS (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.StrongUnforgeableAdversary alg') :
    SignatureAlg.StrongUnforgeableAdversary alg where
  main pk := readOut enc fallback <$> simulateQ (signImpl enc) (adv.main pk)

/-- **The reduction (EUF).** -/
def reduce (enc : E → Except ε M) (fallback : M × S)
    (adv : SignatureAlg.UnforgeableAdversary alg') :
    SignatureAlg.UnforgeableAdversary alg where
  main pk := readOut enc fallback <$> simulateQ (signImpl enc) (adv.main pk)

theorem run_signImpl {pk : PK} {sk : SK} (h : SignAgree alg alg' enc pk sk) {α : Type}
    (oa : OracleComp (unifSpec + (E →ₒ Option S)) α) :
    alg.runWithSigningOracle pk sk (simulateQ (signImpl enc) oa) =
      (fun z => (z.1, decodeLog enc z.2)) <$> alg'.runWithSigningOracle pk sk oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp [SignatureAlg.runWithSigningOracle, decodeLog]
  | query_bind t k ih =>
    simp only [SignatureAlg.runWithSigningOracle, SignatureAlg.signingOracle,
      QueryImpl.passthrough_add, decodeLog] at ih
    cases t with
    | inl t =>
      simp [SignatureAlg.runWithSigningOracle, signImpl, SignatureAlg.signingOracle,
        QueryImpl.passthrough_add, ih, decodeLog]
    | inr e =>
      cases he : enc e with
      | error x =>
        simp [SignatureAlg.runWithSigningOracle, signImpl, SignatureAlg.signingOracle,
          QueryImpl.passthrough_add, ih, decodeLog, he, h e]
      | ok m =>
        simp [SignatureAlg.runWithSigningOracle, signImpl, SignatureAlg.signingOracle,
          QueryImpl.passthrough_add, ih, decodeLog, he, h e]

open scoped Classical in
theorem fresh_of_fresh
    (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (log : QueryLog (E →ₒ Option S)) (e : E) (m : M) (he : enc e = .ok m)
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
    | none => simp [he'] at hdec
    | some σ' =>
      simp only [he', Option.some.injEq, Sigma.mk.injEq] at hdec
      obtain ⟨rfl, -⟩ := hdec
      have := hinj e e' _ he he'
      subst this
      exact List.mem_map.mpr ⟨_, hw, rfl⟩

theorem pairFresh_of_pairFresh
    (hinj : ∀ e e' m, enc e = .ok m → enc e' = .ok m → e = e')
    (log : QueryLog (E →ₒ Option S)) (e : E) (m : M) (σ : S) (he : enc e = .ok m)
    (hfresh : (⟨e, some σ⟩ : (_ : E) × Option S) ∉ log) :
    (⟨m, σ⟩ : (_ : M) × S) ∉ decodeLog enc log := by
  intro hm
  obtain ⟨⟨e', s⟩, hw, hdec⟩ := List.mem_filterMap.mp hm
  apply hfresh
  cases he' : enc e' with
  | error x => simp [he'] at hdec
  | ok m'' =>
    cases s with
    | none => simp [he'] at hdec
    | some σ' =>
      simp only [he', Option.some.injEq, Sigma.mk.injEq] at hdec
      obtain ⟨rfl, hσ⟩ := hdec
      have hσ' : σ' = σ := eq_of_heq hσ
      have := hinj e e' _ he he'
      subst this
      subst hσ'
      exact hw

open scoped Classical in
/-- **Advantage transfer, SUF-CMA.** -/
theorem strongUnforgeableAdvantage_le (A : Agree (PK0 := PK0) (SK0 := SK0) alg alg' enc)
    (fallback : M × S) (adv : SignatureAlg.StrongUnforgeableAdversary alg') :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (reduceS (alg := alg) enc fallback adv) := by
  have key : Pr{let b ← SignatureAlg.strongUnforgeableExperiment adv}[b = true] ≤
      Pr{let b ← SignatureAlg.strongUnforgeableExperiment (reduceS (alg := alg) enc fallback adv)}[b = true] := by
    simp only [SignatureAlg.strongUnforgeableExperiment, A.keygen, A.keygen', bind_map_left]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨pk, sk⟩
    simp only [reduceS, Reduction.Guarded.runWithSigningOracle_map, run_signImpl (A.sign pk sk),
      bind_map_left]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨⟨e, s⟩, log⟩
    cases s with
    | none => simp [A.verify_none]
    | some σ =>
      cases he : enc e with
      | error x => simp [A.verify_error _ _ _ _ he]
      | ok m =>
        simp only [A.verify_ok _ _ _ _ he, Prod.map_apply, id_eq, readOut, he]
        apply prEvent_bind_mono_of_forall_le
        intro verified
        by_cases hf : (⟨e, some σ⟩ : (_ : E) × Option S) ∈ log
        · simp [SignatureAlg.signingLogContains, hf]
        · have ht := pairFresh_of_pairFresh A.inj log e m σ he hf
          simp [SignatureAlg.signingLogContains, ht, hf]
  simpa only [SignatureAlg.strongUnforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using key

open scoped Classical in
/-- **Advantage transfer, EUF-CMA.** -/
theorem unforgeableAdvantage_le
    (A : Agree (PK0 := PK0) (SK0 := SK0) alg alg' enc)
    (fallback : M × S) (adv : SignatureAlg.UnforgeableAdversary alg') :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (reduce (alg := alg) enc fallback adv) := by
  have key : Pr{let b ← SignatureAlg.unforgeableExperiment adv}[b = true] ≤
      Pr{let b ← SignatureAlg.unforgeableExperiment (reduce (alg := alg) enc fallback adv)}[b = true] := by
    simp only [SignatureAlg.unforgeableExperiment, A.keygen, A.keygen', bind_map_left]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨pk, sk⟩
    simp only [reduce, Reduction.Guarded.runWithSigningOracle_map, run_signImpl (A.sign pk sk),
      bind_map_left]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨⟨e, s⟩, log⟩
    cases s with
    | none => simp [A.verify_none]
    | some σ =>
      cases he : enc e with
      | error x => simp [A.verify_error _ _ _ _ he]
      | ok m =>
        simp only [A.verify_ok _ _ _ _ he, Prod.map_apply, id_eq, readOut, he]
        apply prEvent_bind_mono_of_forall_le
        intro verified
        by_cases hf : log.wasQueried e = true
        · simp [hf]
        · have hf' : log.wasQueried e = false := by simpa using hf
          have ht := fresh_of_fresh A.inj log e m he hf'
          simp [ht, hf']
  simpa only [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using key

end OptGuard

/-! ## The instance: `pureBytesAlg` over `bytesAlg` -/

section Inst

open Reduction

variable {vp : ValidatedParams} {prims : Primitives vp.params} [DecidableEq prims.Y]
  {codec : CoreWireCodec vp.params prims.core}
  [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
  {optRand : PublicKeyCore prims.core → ProbComp prims.Y} {pkSeedDist : ProbComp prims.PkSeed}

theorem byteSignPure_encode_ok (M ctx : List Byte) (m : List Byte)
    (h : pureEncode (M, ctx) = .ok m) (k : SecretKeyCore prims.core) (a : prims.Y) :
    byteSignPure vp prims codec M ctx (encodeSecretKey codec k) a =
      some (byteSign vp prims codec m (encodeSecretKey codec k) a) := by
  rw [byteSignPure_encode, byteSign_encode]
  simp only [pureEncode] at h
  simp [External.signPureWithRandomizer, h, Except.toOption]

/-- **The hypotheses of the transfer hold for the byte-level schemes.** -/
noncomputable def pureAgree :
    OptGuard.Agree (PK0 := PublicKeyCore prims.core) (SK0 := SecretKeyCore prims.core)
      (bytesAlg vp prims codec optRand pkSeedDist)
      (pureBytesAlg vp prims codec optRand pkSeedDist) pureEncode where
  K := (internalAlg vp prims optRand pkSeedDist).keygen
  encPk := encodePublicKey codec
  encSk := encodeSecretKey codec
  keygen := (bytesView vp prims codec optRand pkSeedDist).keygen_eq
  keygen' := (pureBytesView vp prims codec optRand pkSeedDist).keygen_eq
  sign pk sk := by
    rintro ⟨M, ctx⟩
    cases he : pureEncode (M, ctx) with
    | error x =>
      have hc : ¬ ctx.length ≤ 255 := by
        intro hc
        simp [pureEncode, External.encodePureMessage_eq_ok ctx M hc] at he
      simp [pureBytesAlg, hc]
    | ok m =>
      have hc : ctx.length ≤ 255 := by
        by_contra hc
        have := (encodePureMessage_ok_iff ctx M m).1 he
        exact hc this.1
      simp only [pureBytesAlg, hc, ite_true, decodePublicKey_encode, bytesAlg]
      simp only [byteSignPure_encode_ok M ctx m he, map_bind, map_pure]
  verify_none _ _ := rfl
  verify_error pk e x s he := by
    obtain ⟨M, ctx⟩ := e
    simp only [pureBytesAlg, byteVerifyPure]
    have he' : External.encodePureMessage ctx M = .error x := he
    cases decodeSignature vp codec s <;> cases decodePublicKey codec pk <;>
      simp [External.verifyPure, he']
  verify_ok pk e m s he := by
    obtain ⟨M, ctx⟩ := e
    have he' : External.encodePureMessage ctx M = .ok m := he
    simp only [pureBytesAlg, bytesAlg, byteVerifyPure, byteVerify]
    cases decodeSignature vp codec s <;> cases decodePublicKey codec pk <;>
      simp [External.verifyPure, he']
  inj e e' m h h' := pureEncode_injective e e' m h h'

/-- The fixed output of the reduction when the external forger's output is malformed. -/
def fallbackB : List Byte × List Byte := ([], [])

/-- **External byte-level SUF-CMA advantage ≤ internal byte-level SUF-CMA advantage.** -/
theorem pure_bytes_strong_le_bytes (adv : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (OptGuard.reduceS (alg := bytesAlg vp prims codec optRand pkSeedDist) pureEncode
          fallbackB adv) :=
  OptGuard.strongUnforgeableAdvantage_le pureAgree fallbackB adv

/-- **External byte-level EUF-CMA advantage ≤ internal byte-level EUF-CMA advantage.** -/
theorem pure_bytes_le_bytes (adv : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp
        (OptGuard.reduce (alg := bytesAlg vp prims codec optRand pkSeedDist) pureEncode
          fallbackB adv) :=
  OptGuard.unforgeableAdvantage_le pureAgree fallbackB adv

end Inst

end Ideal.Pure

#print axioms Ideal.Pure.OptGuard.strongUnforgeableAdvantage_le
#print axioms Ideal.Pure.OptGuard.unforgeableAdvantage_le
#print axioms Ideal.Pure.pureAgree
