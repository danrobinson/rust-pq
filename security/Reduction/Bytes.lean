import Reduction.HeadlineSplit
import Reduction.ExternalSuf
import HashSig.SLHDSA.Codec
import Link.Verify

/-!
# Byte-level security: the games on byte strings

The headline theorems (`Reduction/HeadlineSplit.lean`) are about games on *typed* values: the
forger receives a `PublicKeyCore`, and a forgery is a typed `SignatureCore` (external interface:
`Except External.Error SignatureCore`).  An implementation, and an attacker against it, handles
*byte strings*: the public key is `PK.seed ‖ PK.root`, a signature is `R ‖ SIG_FORS ‖ SIG_HT`, and
the verifier first parses what it is given and rejects what does not parse.

This file

* (`Reduction.Coded`) gives a generic transfer.  `Coded.View alg balg` says that the scheme `balg`
  is the scheme `alg` seen through encodings of keys and signatures: key generation of `balg` is
  key generation of `alg` followed by encoding; signing under encoded keys is signing followed by
  encoding; verifying under an encoded public key is "parse the signature, reject if that fails,
  else verify"; and the parser accepts only canonical encodings
  (`decS sb = some s → encS s = sb`).  Then every EUF-CMA / SUF-CMA forger `A` against `balg`
  yields the explicit forger `Coded.reduce v fb A` / `Coded.reduceS v fb A` against `alg` with
  `Adv_balg(A) ≤ Adv_alg(reduce A)` (`Coded.unforgeableAdvantage_le`,
  `Coded.strongUnforgeableAdvantage_le`), making exactly one signing query per signing query of
  `A` (`Coded.reduce_queryBound`), no sampling of its own, no choice;
* defines, for every parameter set `vp`, primitive bundle `prims` and atomic wire codec
  `codec : CoreWireCodec vp.params prims.core` (VCVio's FIPS 205 Figure 15–17 codecs), the
  deterministic byte-level cores `byteKeygen`, `byteSign`, `byteVerify` (FIPS 205 Alg. 18–20) and
  `byteSignPure`, `byteVerifyPure` (Alg. 22, 24), and the byte-level schemes `bytesAlg`
  (internal) and `pureBytesAlg` (external pure, with context strings) built from them: public
  keys, secret keys, messages, contexts and signatures are all `List Byte`;
* proves `bytesView`, `pureBytesView` (they are views of `internalAlg` and `externalAlg`), hence
  the transfers `bytes_bound_of_typed_bound` etc. ("any bound `∀ B, Adv B ≤ β B` on typed forgers
  gives `∀ A, Adv A ≤ β (toTyped A)` on byte forgers"), and the byte-level headline theorems
  `slhdsa_bytes_suf_cma`, `slhdsa_bytes_euf_cma`, `slhdsa_pure_bytes_suf_cma`,
  `slhdsa_pure_bytes_euf_cma` (and `…_128s` at SLH-DSA-SHA2-128s with VCVio's approved codec);
* proves that the byte-level schemes are correct (`byteVerify_byteSign`,
  `byteVerifyPure_byteSignPure`, `bytesAlg_perfectlyComplete`).

**Why the transfer holds.**  A strong forgery against the byte-level scheme is a pair
(message, signature bytes) that verifies and whose exact byte string was never returned for that
message.  Since it verifies, the bytes parse to a typed signature `s` that the typed verifier
accepts; since the parser accepts only canonical encodings, the bytes are `encS s`; so if `s` had
been returned by the typed signing oracle for that message, the byte string `encS s` would have
been returned to the byte forger.  (Injectivity of the encoding is not needed for this direction;
it is `encodeSignature_injective` and holds.)  The public key given to the byte forger is the
encoding of the typed key the typed forger receives.

**Malformed inputs** (the scheme is total on byte strings; none of these cases occurs in the
games, where keys come from key generation, and none is reachable from the Rust functions, whose
key arguments are fixed-length arrays):

* `verify`: a public key that is not exactly `2n` bytes, or a signature that is not exactly
  `signatureBytes` bytes, is rejected (the strict decoders fail exactly on a wrong length);
* `sign`: a secret key that is not exactly `4n` bytes yields the empty byte string `[]` (internal)
  resp. `none` (external) — values that no verifier accepts; a public key that does not parse
  yields the same without sampling `opt_rand` (the public key is used by `sign` only as the
  argument of `optRand`).
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security ENNReal

namespace Reduction

set_option linter.unusedSectionVars false

/-! ## Generic part: a scheme seen through encodings of keys and signatures -/

namespace Coded

variable {M PK SK S PKb SKb Sb : Type}

/-- `balg` is `alg` seen through encodings of public keys, secret keys and signatures, with a
signature parser `decS` that accepts only canonical encodings. -/
structure View (alg : SignatureAlg ProbComp M PK SK S)
    (balg : SignatureAlg ProbComp M PKb SKb Sb) where
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

variable {alg : SignatureAlg ProbComp M PK SK S} {balg : SignatureAlg ProbComp M PKb SKb Sb}

/-- How the typed forger answers the byte forger's queries: uniform-sampling queries are
forwarded; a signing query `m` is answered by exactly one query `m` to the typed signing oracle,
whose answer is encoded. -/
def signingImpl (v : View alg balg) :
    QueryImpl (unifSpec + (M →ₒ Sb)) (OracleComp (unifSpec + (M →ₒ S)))
  | .inl t => (query (spec := unifSpec + (M →ₒ S)) (.inl t) : OracleComp _ (unifSpec.Range t))
  | .inr m => v.encS <$> (query (spec := unifSpec + (M →ₒ S)) (.inr m) : OracleComp _ S)

/-- Translate the byte forger's output: the message with the parsed signature; if the signature
bytes do not parse (the byte forger has then lost: its output is rejected), the fixed signature
`fallback`. -/
def readForgery (v : View alg balg) (fallback : S) (out : M × Sb) : M × S :=
  (out.1, (v.decS out.2).getD fallback)

/-- **The typed forger built from a byte forger.**  On input the typed public key `pk`: encode
it, run the byte forger once on the encoding, answer its queries by `signingImpl`, translate its
output by `readForgery`.  No choice, no search, no sampling of its own. -/
def reduce (v : View alg balg) (fallback : S) (adv : SignatureAlg.UnforgeableAdversary balg) :
    SignatureAlg.UnforgeableAdversary alg where
  main pk := readForgery v fallback <$> simulateQ (signingImpl v) (adv.main (v.encPk pk))

/-- The same program as a strong-unforgeability adversary. -/
def reduceS (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.StrongUnforgeableAdversary alg where
  main pk := readForgery v fallback <$> simulateQ (signingImpl v) (adv.main (v.encPk pk))

/-- `reduceS` and `reduce` are the same program. -/
theorem reduceS_toUnforgeableAdversary (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    (reduceS v fallback adv).toUnforgeableAdversary =
      reduce v fallback adv.toUnforgeableAdversary := rfl

/-- The byte forger's signing log, computed from the typed forger's: every entry encoded. -/
def encodeLog (v : View alg balg) (log : QueryLog (M →ₒ S)) : QueryLog (M →ₒ Sb) :=
  log.map fun entry => ⟨entry.1, v.encS entry.2⟩

/-- Running the byte forger against the signing oracle of `balg` under encoded keys is running
the simulation against the signing oracle of `alg`, with the log encoded. -/
theorem runWithSigningOracle_signingImpl (v : View alg balg) (pk : PK) (sk : SK) {α : Type}
    (oa : OracleComp (unifSpec + (M →ₒ Sb)) α) :
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

/-- Message freshness is the same in both logs. -/
theorem wasQueried_encodeLog [DecidableEq M] (v : View alg balg) (log : QueryLog (M →ₒ S))
    (m : M) : (encodeLog v log).wasQueried m = log.wasQueried m := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst, QueryLog.wasQueried_eq_decide_mem_map_fst]
  congr 1
  simp [encodeLog, List.map_map, Function.comp_def]

/-- Pair freshness transfers: if the byte string `sb` parses to `s` and the pair `(m, sb)` was
never returned to the byte forger, then `(m, s)` was never returned to the typed forger. -/
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
/-- The EUF-CMA experiment of the byte forger, written over the run of the typed forger. -/
theorem unforgeableExperiment_bytes (v : View alg balg)
    (adv : SignatureAlg.UnforgeableAdversary balg) :
    SignatureAlg.unforgeableExperiment adv = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← alg.runWithSigningOracle pk sk
        (simulateQ (signingImpl v) (adv.main (v.encPk pk)))
      let verified ← balg.verify (v.encPk pk) out.1 out.2
      return !(encodeLog v log).wasQueried out.1 && verified := by
  simp only [SignatureAlg.unforgeableExperiment, v.keygen_eq, bind_map_left,
    runWithSigningOracle_signingImpl v]

open scoped Classical in
/-- The EUF-CMA experiment of the typed forger `reduce v fallback adv`. -/
theorem unforgeableExperiment_reduce (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.UnforgeableAdversary balg) :
    SignatureAlg.unforgeableExperiment (reduce v fallback adv) = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← alg.runWithSigningOracle pk sk
        (simulateQ (signingImpl v) (adv.main (v.encPk pk)))
      let verified ← alg.verify pk out.1 ((v.decS out.2).getD fallback)
      return !log.wasQueried out.1 && verified := by
  simp only [SignatureAlg.unforgeableExperiment, reduce, Guarded.runWithSigningOracle_map,
    bind_map_left]
  rfl

open scoped Classical in
/-- **Advantage transfer, EUF-CMA (generic).**  The advantage of any forger against `balg` is at
most that of the typed forger `reduce v fallback adv` against `alg`. -/
theorem unforgeableAdvantage_le (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.UnforgeableAdversary balg) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (reduce v fallback adv) := by
  have key : Pr{let b ← SignatureAlg.unforgeableExperiment adv}[b = true] ≤
      Pr{let b ← SignatureAlg.unforgeableExperiment (reduce v fallback adv)}[b = true] := by
    rw [unforgeableExperiment_reduce, unforgeableExperiment_bytes v]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨pk, sk⟩
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨⟨m, sb⟩, log⟩
    simp only [v.verify_eq, wasQueried_encodeLog]
    cases hs : v.decS sb with
    | none => simp
    | some s => simp
  simpa only [SignatureAlg.unforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using key

open scoped Classical in
/-- The SUF-CMA experiment of the byte forger, written over the run of the typed forger. -/
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
/-- The SUF-CMA experiment of the typed forger `reduceS v fallback adv`. -/
theorem strongUnforgeableExperiment_reduceS (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.strongUnforgeableExperiment (reduceS v fallback adv) = do
      let (pk, sk) ← alg.keygen
      let (out, log) ← alg.runWithSigningOracle pk sk
        (simulateQ (signingImpl v) (adv.main (v.encPk pk)))
      let verified ← alg.verify pk out.1 ((v.decS out.2).getD fallback)
      return !SignatureAlg.signingLogContains log out.1 ((v.decS out.2).getD fallback) &&
        verified := by
  simp only [SignatureAlg.strongUnforgeableExperiment, reduceS, Guarded.runWithSigningOracle_map,
    bind_map_left]
  rfl

open scoped Classical in
/-- **Advantage transfer, SUF-CMA (generic).**  The strong-unforgeability advantage of any forger
against `balg` is at most that of the typed forger `reduceS v fallback adv` against `alg`. -/
theorem strongUnforgeableAdvantage_le (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp adv ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp
        (reduceS v fallback adv) := by
  have key : Pr{let b ← SignatureAlg.strongUnforgeableExperiment adv}[b = true] ≤
      Pr{let b ← SignatureAlg.strongUnforgeableExperiment (reduceS v fallback adv)}[b = true] := by
    rw [strongUnforgeableExperiment_reduceS, strongUnforgeableExperiment_bytes v]
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨pk, sk⟩
    apply prEvent_bind_mono_of_forall_le
    rintro ⟨⟨m, sb⟩, log⟩
    simp only [v.verify_eq]
    cases hs : v.decS sb with
    | none => simp
    | some s =>
      simp only [Option.getD_some]
      apply prEvent_bind_mono_of_forall_le
      intro verified
      by_cases hf : (⟨m, sb⟩ : (_ : M) × Sb) ∈ encodeLog v log
      · simp [SignatureAlg.signingLogContains, hf]
      · have ht := pairFresh_of_pairFresh v log m sb s hs hf
        simp [SignatureAlg.signingLogContains, ht, hf]
  simpa only [SignatureAlg.strongUnforgeableAdvantage, ProbCompRuntime.probComp_evalDist,
    prEvent_eq_evalDist_of_discrete, Set.ofPred_eq_eq_singleton] using key

/-- **Query budget of the typed forger**: as many signing queries as the byte forger (one per
signing query). -/
theorem reduce_queryBound (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.UnforgeableAdversary balg) (qs : ℕ) (pk : PK)
    (h : IsQueryBoundP (adv.main (v.encPk pk)) (fun i => i.isRight = true) qs) :
    IsQueryBoundP ((reduce v fallback adv).main pk) (fun i => i.isRight = true) qs := by
  simp only [reduce, isQueryBoundP_map_iff]
  apply h.simulateQ_of_step
  · rintro (t | e) ht
    · simp at ht
    · simp [signingImpl]
  · rintro (t | e) ht
    · simp [signingImpl]
    · simp at ht

/-- The same for `reduceS`. -/
theorem reduceS_queryBound (v : View alg balg) (fallback : S)
    (adv : SignatureAlg.StrongUnforgeableAdversary balg) (qs : ℕ) (pk : PK)
    (h : IsQueryBoundP (adv.main (v.encPk pk)) (fun i => i.isRight = true) qs) :
    IsQueryBoundP ((reduceS v fallback adv).main pk) (fun i => i.isRight = true) qs :=
  reduce_queryBound v fallback adv.toUnforgeableAdversary qs pk h

end Coded

/-! ## The byte-level cores and schemes -/

section Scheme

variable (vp : ValidatedParams) (prims : Primitives vp.params) [DecidableEq prims.Y]
variable (codec : CoreWireCodec vp.params prims.core)

/-- **Byte-level key generation core** (FIPS 205 Alg. 18): the encodings
`(PK.seed ‖ PK.root, SK.seed ‖ SK.prf ‖ PK.seed ‖ PK.root)` of the key pair computed from the
three seeds.  (Public key first, as in `SignatureAlg.keygen`.) -/
def byteKeygen (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) :
    List Byte × List Byte :=
  (encodePublicKey codec (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1,
    encodeSecretKey codec (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2)

/-- **Byte-level signing core** (FIPS 205 Alg. 19 with `opt_rand = addrnd`): parse the secret
key (exactly `4n` bytes), sign, return the encoding `R ‖ SIG_FORS ‖ SIG_HT`.  A secret key of
the wrong length yields `[]` (which no verifier accepts). -/
def byteSign (m sk : List Byte) (addrnd : prims.Y) : List Byte :=
  match decodeSecretKey codec sk with
  | .ok k => encodeSignature vp codec (GeneralScheme.signInternal vp prims m k addrnd)
  | .error _ => []

/-- **Byte-level verification core** (FIPS 205 Alg. 20): parse the signature and the public key
with the strict decoders; reject if either fails (wrong length); otherwise verify. -/
def byteVerify (m sig pk : List Byte) : Bool :=
  match decodeSignature vp codec sig, decodePublicKey codec pk with
  | .ok s, .ok k => GeneralScheme.verifyInternal vp prims m s k
  | _, _ => false

/-- **Byte-level pure signing core** (FIPS 205 Alg. 22 with caller-supplied `addrnd`): `none` if
the context is longer than 255 bytes (or the secret key has the wrong length), otherwise `some`
of the encoded signature of `0x00 ‖ |ctx| ‖ ctx ‖ M`. -/
def byteSignPure (m ctx sk : List Byte) (addrnd : prims.Y) : Option (List Byte) :=
  match decodeSecretKey codec sk with
  | .ok k =>
    (External.signPureWithRandomizer vp prims m ctx k addrnd).toOption.map
      (encodeSignature vp codec)
  | .error _ => none

/-- **Byte-level pure verification core** (FIPS 205 Alg. 24): parse signature and public key,
reject if either fails; otherwise `External.verifyPure` (which rejects an over-long context). -/
def byteVerifyPure (m sig ctx pk : List Byte) : Bool :=
  match decodeSignature vp codec sig, decodePublicKey codec pk with
  | .ok s, .ok k => External.verifyPure vp prims m s ctx k
  | _, _ => false

variable {vp prims codec}

theorem byteSign_encode (m : List Byte) (k : SecretKeyCore prims.core) (addrnd : prims.Y) :
    byteSign vp prims codec m (encodeSecretKey codec k) addrnd =
      encodeSignature vp codec (GeneralScheme.signInternal vp prims m k addrnd) := by
  simp [byteSign]

theorem byteVerify_encode (m sig : List Byte) (k : PublicKeyCore prims.core) :
    byteVerify vp prims codec m sig (encodePublicKey codec k) =
      match decodeSignature vp codec sig with
      | .ok s => GeneralScheme.verifyInternal vp prims m s k
      | .error _ => false := by
  simp only [byteVerify, decodePublicKey_encode]
  cases decodeSignature vp codec sig <;> rfl

theorem byteSignPure_encode (m ctx : List Byte) (k : SecretKeyCore prims.core)
    (addrnd : prims.Y) :
    byteSignPure vp prims codec m ctx (encodeSecretKey codec k) addrnd =
      (External.signPureWithRandomizer vp prims m ctx k addrnd).toOption.map
        (encodeSignature vp codec) := by
  simp [byteSignPure]

theorem byteVerifyPure_encode (m sig ctx : List Byte) (k : PublicKeyCore prims.core) :
    byteVerifyPure vp prims codec m sig ctx (encodePublicKey codec k) =
      match decodeSignature vp codec sig with
      | .ok s => External.verifyPure vp prims m s ctx k
      | .error _ => false := by
  simp only [byteVerifyPure, decodePublicKey_encode]
  cases decodeSignature vp codec sig <;> rfl

/-- The pure signing core returns `none` on every over-long context. -/
theorem byteSignPure_tooLong (m ctx sk : List Byte) (addrnd : prims.Y)
    (h : 255 < ctx.length) : byteSignPure vp prims codec m ctx sk addrnd = none := by
  unfold byteSignPure
  cases decodeSecretKey codec sk with
  | error e => rfl
  | ok k =>
    have he : External.encodePureMessage ctx m = .error (.contextTooLong ctx.length) := by
      unfold External.encodePureMessage External.encodeMessage
      rw [External.requireContext_eq_error ctx h]; rfl
    simp only [External.signPureWithRandomizer, he]
    rfl

/-- A public key of the wrong length is rejected. -/
theorem byteVerify_of_pk_length_ne (m sig pk : List Byte)
    (h : pk.length ≠ vp.params.publicKeyBytes) : byteVerify vp prims codec m sig pk = false := by
  unfold byteVerify
  have : decodePublicKey codec pk = .error (.invalidLength vp.params.publicKeyBytes pk.length) :=
    WireCodec.decode_eq_error_of_length_ne _ _ h
  rw [this]
  cases decodeSignature vp codec sig <;> rfl

/-- A signature of the wrong length is rejected. -/
theorem byteVerify_of_sig_length_ne (m sig pk : List Byte)
    (h : sig.length ≠ vp.params.signatureBytes) : byteVerify vp prims codec m sig pk = false := by
  unfold byteVerify
  have : decodeSignature vp codec sig =
      .error (.invalidLength vp.params.signatureBytes sig.length) :=
    WireCodec.decode_eq_error_of_length_ne _ _ h
  rw [this]

/-- A secret key of the wrong length makes the signing core return `[]`. -/
theorem byteSign_of_sk_length_ne (m sk : List Byte) (addrnd : prims.Y)
    (h : sk.length ≠ vp.params.secretKeyBytes) : byteSign vp prims codec m sk addrnd = [] := by
  unfold byteSign
  have : decodeSecretKey codec sk = .error (.invalidLength vp.params.secretKeyBytes sk.length) :=
    WireCodec.decode_eq_error_of_length_ne _ _ h
  rw [this]

/-- The value `[]` returned for a malformed secret key is never accepted (signatures are not
empty). -/
theorem byteVerify_nil (m pk : List Byte) (h : vp.params.signatureBytes ≠ 0) :
    byteVerify vp prims codec m [] pk = false :=
  byteVerify_of_sig_length_ne m [] pk (fun h' => h h'.symm)

variable (vp prims codec)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- **The byte-level SLH-DSA scheme, internal interface** (FIPS 205 Alg. 18–20): public keys,
secret keys, messages and signatures are byte strings.

* key generation draws `PK.seed ← pkSeedDist`, `SK.seed`, `SK.prf` uniformly and returns
  `byteKeygen` of them (the encoded key pair);
* signing parses the public key (only to evaluate `optRand` on it), draws `opt_rand ← optRand pk`
  and returns `byteSign m sk opt_rand`; if the public key does not parse it returns `[]`;
* verification is `byteVerify m sig pk`. -/
noncomputable def bytesAlg :
    SignatureAlg ProbComp (List Byte) (List Byte) (List Byte) (List Byte) where
  keygen := do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (byteKeygen vp prims codec skSeed skPrf pkSeed)
  sign pk sk m :=
    match decodePublicKey codec pk with
    | .ok k => do
      let addrnd ← optRand k
      pure (byteSign vp prims codec m sk addrnd)
    | .error _ => pure []
  verify pk m sig := pure (byteVerify vp prims codec m sig pk)

/-- **The byte-level SLH-DSA scheme, external pure interface** (FIPS 205 Alg. 21/22/24):
messages are pairs `(message, context)` of byte strings, keys are byte strings, and a signature
is `Option (List Byte)` — the return type of the Rust `slh_sign`, which returns `None` for a
context longer than 255 bytes.

* key generation as in `bytesAlg`;
* signing `(M, ctx)`: if `|ctx| > 255` return `none` (nothing is sampled; FIPS 205 Alg. 22
  line 1); otherwise parse the public key, draw `opt_rand ← optRand pk`, return
  `byteSignPure M ctx sk opt_rand` (which is also `none` for `|ctx| > 255`,
  `byteSignPure_tooLong`); `none` if the public key does not parse;
* verifying `(M, ctx)` against `some sig` is `byteVerifyPure M sig ctx pk`; `none` is rejected. -/
noncomputable def pureBytesAlg :
    SignatureAlg ProbComp (List Byte × List Byte) (List Byte) (List Byte)
      (Option (List Byte)) where
  keygen := do
    let pkSeed ← pkSeedDist
    let skSeed ← $ᵗ prims.SkSeed
    let skPrf ← $ᵗ prims.SkPrf
    pure (byteKeygen vp prims codec skSeed skPrf pkSeed)
  sign pk sk mc :=
    if mc.2.length ≤ 255 then
      match decodePublicKey codec pk with
      | .ok k => do
        let addrnd ← optRand k
        pure (byteSignPure vp prims codec mc.1 mc.2 sk addrnd)
      | .error _ => pure none
    else pure none
  verify pk mc sig := pure (match sig with
    | some raw => byteVerifyPure vp prims codec mc.1 raw mc.2 pk
    | none => false)

/-- **`bytesAlg` is `internalAlg` seen through the FIPS wire encodings.** -/
noncomputable def bytesView :
    Coded.View (internalAlg vp prims optRand pkSeedDist)
      (bytesAlg vp prims codec optRand pkSeedDist) where
  encPk := encodePublicKey codec
  encSk := encodeSecretKey codec
  encS := encodeSignature vp codec
  decS raw := (decodeSignature vp codec raw).toOption
  keygen_eq := by
    simp [bytesAlg, internalAlg, byteKeygen]
  sign_eq pk sk m := by
    simp only [bytesAlg, internalAlg, decodePublicKey_encode]
    simp only [bind_pure_comp, Functor.map_map]
    exact congrArg (· <$> optRand pk) (funext fun a => byteSign_encode m sk a)
  verify_eq pk m sb := by
    simp only [bytesAlg, internalAlg, byteVerify_encode]
    cases decodeSignature vp codec sb <;> rfl
  canonical sb s h := by
    cases hd : decodeSignature vp codec sb with
    | error e => rw [hd] at h; cases h
    | ok s' =>
      rw [hd] at h
      have hs : s' = s := by simpa [Except.toOption] using h
      subst hs
      exact ((decodeSignature_eq_ok_iff vp codec sb s').1 hd).symm

/-- Encoding of a typed external signature value: `none` for an error, else the wire bytes. -/
def encodePureSig (s : Except External.Error (GeneralScheme.SignatureCore vp prims.core)) :
    Option (List Byte) :=
  s.toOption.map (encodeSignature vp codec)

/-- Parser of a byte-level external signature value: `none` and unparsable bytes are rejected. -/
def decodePureSig : Option (List Byte) →
    Option (Except External.Error (GeneralScheme.SignatureCore vp prims.core))
  | none => none
  | some raw => (decodeSignature vp codec raw).toOption.map Except.ok

/-- **`pureBytesAlg` is `externalAlg` seen through the FIPS wire encodings.** -/
noncomputable def pureBytesView :
    Coded.View (externalAlg vp prims optRand pkSeedDist)
      (pureBytesAlg vp prims codec optRand pkSeedDist) where
  encPk := encodePublicKey codec
  encSk := encodeSecretKey codec
  encS := encodePureSig vp prims codec
  decS := decodePureSig vp prims codec
  keygen_eq := by
    simp [pureBytesAlg, externalAlg, Guarded.scheme, internalAlg, byteKeygen]
  sign_eq pk sk mc := by
    obtain ⟨m, ctx⟩ := mc
    by_cases h : ctx.length ≤ 255
    · rw [externalAlg_sign vp prims optRand pkSeedDist pk sk m ctx h]
      simp only [pureBytesAlg, h, ite_true, decodePublicKey_encode]
      simp only [bind_pure_comp, Functor.map_map]
      exact congrArg (· <$> optRand pk) (funext fun a => byteSignPure_encode m ctx sk a)
    · rw [(externalAlg_sign_tooLong vp prims optRand pkSeedDist pk sk m ctx (by omega)).1]
      simp [pureBytesAlg, h, encodePureSig, Except.toOption]
  verify_eq pk mc sb := by
    obtain ⟨m, ctx⟩ := mc
    cases sb with
    | none => rfl
    | some raw =>
      simp only [pureBytesAlg, byteVerifyPure_encode, decodePureSig]
      cases hd : decodeSignature vp codec raw with
      | error e => rfl
      | ok s =>
        exact (externalAlg_verify_ok vp prims optRand pkSeedDist pk m ctx s).symm
  canonical sb s h := by
    cases sb with
    | none => cases h
    | some raw =>
      simp only [decodePureSig] at h
      cases hd : decodeSignature vp codec raw with
      | error e => rw [hd] at h; cases h
      | ok s' =>
        rw [hd] at h
        have hs : Except.ok s' = s := by simpa [Except.toOption] using h
        subst hs
        simp only [encodePureSig, Except.toOption, Option.map_some]
        exact congrArg some ((decodeSignature_eq_ok_iff vp codec raw s').1 hd).symm

end Scheme

/-! ## Forgers against the byte-level schemes and their typed counterparts -/

section Transfer

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [DecidableEq prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

variable (vp prims codec optRand pkSeedDist) in
/-- A chosen-message forger against the byte-level internal scheme: it receives the public key
as bytes `PK.seed ‖ PK.root`, has a signing oracle from message bytes to signature bytes, and
outputs a message and a byte string. -/
abbrev BytesForger : Type :=
  SignatureAlg.UnforgeableAdversary (bytesAlg vp prims codec optRand pkSeedDist)

variable (vp prims codec optRand pkSeedDist) in
/-- A strong forger against the byte-level internal scheme: it wins if its output
(message, byte string) is accepted by `byteVerify` and that exact pair was never returned by the
signing oracle. -/
abbrev BytesStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary (bytesAlg vp prims codec optRand pkSeedDist)

variable (vp prims codec optRand pkSeedDist) in
/-- A chosen-message forger against the byte-level external pure scheme. -/
abbrev PureBytesForger : Type :=
  SignatureAlg.UnforgeableAdversary (pureBytesAlg vp prims codec optRand pkSeedDist)

variable (vp prims codec optRand pkSeedDist) in
/-- A strong forger against the byte-level external pure scheme: it wins if its output
`((message, context), some bytes)` is accepted by `byteVerifyPure` and that exact pair was never
returned by the signing oracle. -/
abbrev PureBytesStrongForger : Type :=
  SignatureAlg.StrongUnforgeableAdversary (pureBytesAlg vp prims codec optRand pkSeedDist)

variable [Inhabited prims.Y]

/-- **The typed forger built from a byte-level forger (internal interface).**  On input the typed
public key `pk`, `bytesToTyped A` runs `A` once on `encodePublicKey codec pk`; forwards its
sampling queries; answers a signing query `M` by one query `M` to its own (typed) signing oracle
and returns the encoding of the answer; when `A` outputs `(M, raw)` it outputs `(M, s)` if `raw`
decodes to `s`, and `(M, constSig default)` otherwise (where `A` has lost). -/
noncomputable def bytesToTyped (A : BytesForger vp prims codec optRand pkSeedDist) :
    Forger vp prims optRand pkSeedDist :=
  Coded.reduce (bytesView vp prims codec optRand pkSeedDist) (constSig default) A

/-- The same program as a strong forger. -/
noncomputable def bytesToTypedS (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist) :=
  Coded.reduceS (bytesView vp prims codec optRand pkSeedDist) (constSig default) S

theorem bytesToTypedS_toUnforgeableAdversary
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    (bytesToTypedS S).toUnforgeableAdversary = bytesToTyped S.toUnforgeableAdversary := rfl

/-- **The typed external forger built from a byte-level forger (external pure interface).**  As
`bytesToTyped`; a signing answer `.error _` of the typed oracle (over-long context) is passed on
as `none`; an output `((M, ctx), some raw)` becomes `((M, ctx), .ok s)` if `raw` decodes to `s`,
and otherwise (also for `none`) `((M, ctx), .error _)`, which is never accepted. -/
noncomputable def pureBytesToTyped (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    ExtForger vp prims optRand pkSeedDist :=
  Coded.reduce (pureBytesView vp prims codec optRand pkSeedDist)
    (.error (.contextTooLong 0)) A

/-- The same program as a strong forger. -/
noncomputable def pureBytesToTypedS
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    ExtStrongForger vp prims optRand pkSeedDist :=
  Coded.reduceS (pureBytesView vp prims codec optRand pkSeedDist)
    (.error (.contextTooLong 0)) S

theorem pureBytesToTypedS_toUnforgeableAdversary
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    (pureBytesToTypedS S).toUnforgeableAdversary = pureBytesToTyped S.toUnforgeableAdversary :=
  rfl

/-- **Byte-level EUF-CMA advantage ≤ typed EUF-CMA advantage (internal).** -/
theorem bytes_advantage_le (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (bytesToTyped A) :=
  Coded.unforgeableAdvantage_le _ _ A

/-- **Byte-level SUF-CMA advantage ≤ typed SUF-CMA advantage (internal).** -/
theorem bytes_strong_advantage_le (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (bytesToTypedS S) :=
  Coded.strongUnforgeableAdvantage_le _ _ S

/-- **Byte-level EUF-CMA advantage ≤ typed EUF-CMA advantage (external pure).** -/
theorem pure_bytes_advantage_le (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp (pureBytesToTyped A) :=
  Coded.unforgeableAdvantage_le _ _ A

/-- **Byte-level SUF-CMA advantage ≤ typed SUF-CMA advantage (external pure).** -/
theorem pure_bytes_strong_advantage_le
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp (pureBytesToTypedS S) :=
  Coded.strongUnforgeableAdvantage_le _ _ S

/-- **Resources of `bytesToTyped`**: if `A` makes at most `qs` signing queries on every public
key, so does `bytesToTyped A` (one typed signing query per signing query of `A`; no sampling). -/
theorem bytesToTyped_queryBound (A : BytesForger vp prims codec optRand pkSeedDist) (qs : ℕ)
    (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((bytesToTyped A).main pk) (fun i => i.isRight = true) qs :=
  fun pk => Coded.reduce_queryBound _ _ A qs pk (hA _)

theorem bytesToTypedS_queryBound (S : BytesStrongForger vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hS : ∀ pk, IsQueryBoundP (S.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((bytesToTypedS S).main pk) (fun i => i.isRight = true) qs :=
  fun pk => Coded.reduceS_queryBound _ _ S qs pk (hS _)

/-- **Resources of `pureBytesToTyped`**: at most as many signing queries as `A`. -/
theorem pureBytesToTyped_queryBound (A : PureBytesForger vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((pureBytesToTyped A).main pk) (fun i => i.isRight = true) qs :=
  fun pk => Coded.reduce_queryBound _ _ A qs pk (hA _)

theorem pureBytesToTypedS_queryBound
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hS : ∀ pk, IsQueryBoundP (S.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((pureBytesToTypedS S).main pk) (fun i => i.isRight = true) qs :=
  fun pk => Coded.reduceS_queryBound _ _ S qs pk (hS _)

/-- Resources of the composite `toInternal (pureBytesToTyped A)`: at most as many signing
queries as `A`. -/
theorem toInternal_pureBytesToTyped_queryBound
    (A : PureBytesForger vp prims codec optRand pkSeedDist)
    (qs : ℕ) (hA : ∀ pk, IsQueryBoundP (A.main pk) (fun i => i.isRight = true) qs) :
    ∀ pk, IsQueryBoundP ((toInternal (pureBytesToTyped A)).main pk)
      (fun i => i.isRight = true) qs :=
  toInternal_queryBound _ qs (pureBytesToTyped_queryBound A qs hA)

/-! ### Modular transfer lemmas -/

/-- **Transfer, EUF-CMA, internal.**  Any bound `β` on the EUF-CMA advantage of all forgers
against the typed internal scheme bounds every byte-level forger `A` by `β (bytesToTyped A)`. -/
theorem bytes_bound_of_typed_bound (β : Forger vp prims optRand pkSeedDist → ℝ≥0∞)
    (hβ : ∀ B : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ β (bytesToTyped A) :=
  (bytes_advantage_le A).trans (hβ _)

/-- **Transfer, SUF-CMA, internal.**  Any bound `β` on the SUF-CMA advantage of all strong
forgers against the typed internal scheme bounds every byte-level strong forger `S` by
`β (bytesToTypedS S)`. -/
theorem bytes_strong_bound_of_typed_bound
    (β : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist) → ℝ≥0∞)
    (hβ : ∀ B : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤ β (bytesToTypedS S) :=
  (bytes_strong_advantage_le S).trans (hβ _)

/-- **Transfer, EUF-CMA, external pure, from a bound on the typed external scheme.** -/
theorem pure_bytes_bound_of_typed_bound (β : ExtForger vp prims optRand pkSeedDist → ℝ≥0∞)
    (hβ : ∀ B : ExtForger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤ β (pureBytesToTyped A) :=
  (pure_bytes_advantage_le A).trans (hβ _)

/-- **Transfer, SUF-CMA, external pure, from a bound on the typed external scheme.** -/
theorem pure_bytes_strong_bound_of_typed_bound
    (β : ExtStrongForger vp prims optRand pkSeedDist → ℝ≥0∞)
    (hβ : ∀ B : ExtStrongForger vp prims optRand pkSeedDist,
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      β (pureBytesToTypedS S) :=
  (pure_bytes_strong_advantage_le S).trans (hβ _)

/-- **Transfer, EUF-CMA, external pure, from a bound on the typed *internal* scheme**: every
byte-level forger `A` against the external pure scheme is bounded by
`β (toInternal (pureBytesToTyped A))`. -/
theorem pure_bytes_bound_of_internal_bound (β : Forger vp prims optRand pkSeedDist → ℝ≥0∞)
    (hβ : ∀ B : Forger vp prims optRand pkSeedDist,
      SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      β (toInternal (pureBytesToTyped A)) :=
  (pure_bytes_advantage_le A).trans (external_bound_of_internal_bound β hβ _)

/-- **Transfer, SUF-CMA, external pure, from a bound on the typed *internal* scheme**: every
byte-level strong forger `S` is bounded by `β (toInternalS (pureBytesToTypedS S))`. -/
theorem pure_bytes_strong_bound_of_internal_bound
    (β : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist) → ℝ≥0∞)
    (hβ : ∀ B : SignatureAlg.StrongUnforgeableAdversary (internalAlg vp prims optRand pkSeedDist),
      SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp B ≤ β B)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      β (toInternalS (pureBytesToTypedS S)) :=
  ((pure_bytes_strong_advantage_le S).trans (external_strong_advantage_le _)).trans (hβ _)

end Transfer

/-! ## Non-vacuity: the byte-level schemes are correct -/

section Correct

variable {vp : ValidatedParams} {prims : Primitives vp.params} [DecidableEq prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}

/-- **Correctness of the byte-level cores (internal).**  For all seeds, every message and every
`opt_rand`: the byte string produced by `byteSign` under the secret-key bytes of `byteKeygen` is
accepted by `byteVerify` under its public-key bytes. -/
theorem byteVerify_byteSign (m : List Byte) (skSeed : prims.SkSeed) (skPrf : prims.SkPrf)
    (pkSeed : prims.PkSeed) (addrnd : prims.Y) :
    byteVerify vp prims codec m
        (byteSign vp prims codec m (byteKeygen vp prims codec skSeed skPrf pkSeed).2 addrnd)
        (byteKeygen vp prims codec skSeed skPrf pkSeed).1 = true := by
  simp only [byteKeygen, byteSign_encode, byteVerify_encode, decodeSignature_encode]
  exact GeneralScheme.verifyInternal_signInternal vp prims m skSeed skPrf pkSeed addrnd

/-- **Correctness of the byte-level cores (external pure).**  For a context of at most 255 bytes,
`byteSignPure` under honestly generated key bytes returns `some sig`, and `byteVerifyPure`
accepts `sig` for the same message and context. -/
theorem byteVerifyPure_byteSignPure (m ctx : List Byte) (hc : ctx.length ≤ 255)
    (skSeed : prims.SkSeed) (skPrf : prims.SkPrf) (pkSeed : prims.PkSeed) (addrnd : prims.Y) :
    ∃ sig, byteSignPure vp prims codec m ctx
        (byteKeygen vp prims codec skSeed skPrf pkSeed).2 addrnd = some sig ∧
      byteVerifyPure vp prims codec m sig ctx
        (byteKeygen vp prims codec skSeed skPrf pkSeed).1 = true := by
  have h := External.verifyPure_signPureWithRandomizer vp prims m ctx skSeed skPrf pkSeed addrnd hc
  simp only [External.keygenWithSeeds] at h
  simp only [byteKeygen, byteSignPure_encode, byteVerifyPure_encode]
  cases hs : External.signPureWithRandomizer vp prims m ctx
      (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).2 addrnd with
  | error x => rw [hs] at h; cases h
  | ok σ =>
    rw [hs] at h
    refine ⟨encodeSignature vp codec σ, rfl, ?_⟩
    rw [decodeSignature_encode]
    exact Except.ok.inj h

variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
variable (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (pkSeedDist : ProbComp prims.PkSeed)

/-- **The byte-level internal scheme is perfectly complete**: for every message the
keygen–sign–verify run accepts with probability 1. -/
theorem bytesAlg_perfectlyComplete :
    (bytesAlg vp prims codec optRand pkSeedDist).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  have hbody : (do
      let (pk, sk) ← (bytesAlg vp prims codec optRand pkSeedDist).keygen
      let sig ← (bytesAlg vp prims codec optRand pkSeedDist).sign pk sk msg
      (bytesAlg vp prims codec optRand pkSeedDist).verify pk msg sig) = (do
      let pkSeed ← pkSeedDist
      let skSeed ← $ᵗ prims.SkSeed
      let skPrf ← $ᵗ prims.SkPrf
      let _addrnd ← optRand (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1
      pure true) := by
    simp only [bytesAlg, bind_assoc, pure_bind]
    refine bind_congr fun pkSeed => bind_congr fun skSeed => bind_congr fun skPrf => ?_
    simp only [byteKeygen, decodePublicKey_encode, bind_assoc, pure_bind]
    refine bind_congr fun addrnd => ?_
    exact congrArg pure (byteVerify_byteSign msg skSeed skPrf pkSeed addrnd)
  rw [hbody, ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_singleton]
  refine prEvent_eq_one_of_forall_mem_support _ _ fun b hb => ?_
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hb
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hb
  rfl

/-- **The byte-level external pure scheme is complete on contexts of at most 255 bytes**: the
keygen–sign–verify run on `(message, context)` accepts with probability 1. -/
theorem pureBytesAlg_complete (m ctx : List Byte) (hc : ctx.length ≤ 255) :
    ProbCompRuntime.probComp.evalDist (do
      let (pk, sk) ← (pureBytesAlg vp prims codec optRand pkSeedDist).keygen
      let sig ← (pureBytesAlg vp prims codec optRand pkSeedDist).sign pk sk (m, ctx)
      (pureBytesAlg vp prims codec optRand pkSeedDist).verify pk (m, ctx) sig) {true} = 1 := by
  have hbody : (do
      let (pk, sk) ← (pureBytesAlg vp prims codec optRand pkSeedDist).keygen
      let sig ← (pureBytesAlg vp prims codec optRand pkSeedDist).sign pk sk (m, ctx)
      (pureBytesAlg vp prims codec optRand pkSeedDist).verify pk (m, ctx) sig) = (do
      let pkSeed ← pkSeedDist
      let skSeed ← $ᵗ prims.SkSeed
      let skPrf ← $ᵗ prims.SkPrf
      let _addrnd ← optRand (GeneralScheme.keygenInternal vp prims skSeed skPrf pkSeed).1
      pure true) := by
    simp only [pureBytesAlg, bind_assoc, pure_bind, hc, ite_true]
    refine bind_congr fun pkSeed => bind_congr fun skSeed => bind_congr fun skPrf => ?_
    simp only [byteKeygen, decodePublicKey_encode, bind_assoc, pure_bind]
    refine bind_congr fun addrnd => ?_
    obtain ⟨sig, h1, h2⟩ := byteVerifyPure_byteSignPure (codec := codec) m ctx hc skSeed skPrf
      pkSeed addrnd
    simp only [byteKeygen] at h1 h2
    rw [h1]
    exact congrArg pure h2
  rw [hbody, ProbCompRuntime.probComp_evalDist, ← prEvent_eq_evalDist_singleton]
  refine prEvent_eq_one_of_forall_mem_support _ _ fun b hb => ?_
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hb
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := hb
  rfl

end Correct

/-! ## Byte-level headline theorems -/

section Headline

variable {vp : ValidatedParams} {prims : Primitives vp.params}
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]
  [Fintype prims.Y]
variable {codec : CoreWireCodec vp.params prims.core}
variable {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
  {pkSeedDist : ProbComp prims.PkSeed}

/-- **Standard-model SUF-CMA security of SLH-DSA on byte strings (FIPS 205 Alg. 18–20).**
For every strong forger `S` against the byte-level scheme `bytesAlg vp prims codec optRand
pkSeedDist` — it gets the public key as bytes, a signing oracle returning signature bytes, and
wins if it outputs a message and a byte string that `byteVerify` accepts and that was never
returned for that message — the advantage is at most the twelve-term bound
`betaSufFinalSplit` of `slhdsa_suf_cma_final_split`, at the typed forger `bytesToTypedS S`. -/
theorem slhdsa_bytes_suf_cma (hS : Structural vp prims)
    (S : BytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalSplit (bytesToTypedS S).toUnforgeableAdversary :=
  bytes_strong_bound_of_typed_bound _ (slhdsa_suf_cma_final_split' hS) S

/-- **Standard-model EUF-CMA security of SLH-DSA on byte strings (FIPS 205 Alg. 18–20)**: the
bound `betaEufFinalSplit` of `slhdsa_euf_cma_final_split` at `bytesToTyped A`. -/
theorem slhdsa_bytes_euf_cma (hS : Structural vp prims)
    (A : BytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalSplit (bytesToTyped A) :=
  bytes_bound_of_typed_bound _ (slhdsa_euf_cma_final_split' hS) A

/-- **Standard-model SUF-CMA security of the external pure interface on byte strings (FIPS 205
Alg. 21/22/24).**  For every strong forger `S` against `pureBytesAlg …` — a forgery is
`((message, context), some bytes)` accepted by `byteVerifyPure` and never returned for that
(message, context) — the advantage is at most `betaSufFinalSplit` at the internal typed forger
`toInternal (pureBytesToTyped S)`. -/
theorem slhdsa_pure_bytes_suf_cma (hS : Structural vp prims)
    (S : PureBytesStrongForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalSplit (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  pure_bytes_strong_bound_of_internal_bound (fun B => betaSufFinalSplit B.toUnforgeableAdversary)
    (slhdsa_suf_cma_final_split' hS) S

/-- **Standard-model EUF-CMA security of the external pure interface on byte strings**: the
bound `betaEufFinalSplit` at `toInternal (pureBytesToTyped A)`. -/
theorem slhdsa_pure_bytes_euf_cma (hS : Structural vp prims)
    (A : PureBytesForger vp prims codec optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalSplit (toInternal (pureBytesToTyped A)) :=
  pure_bytes_bound_of_internal_bound _ (slhdsa_euf_cma_final_split' hS) A

end Headline

/-! ## SLH-DSA-SHA2-128s -/

/-- The atomic wire codec of SLH-DSA-SHA2-128s (VCVio's approved codec: every carrier is 16
bytes, encoded as itself).  `decodeSignature Link.vp codec128s = Link.decodeSig` and
`decodePublicKey codec128s = Link.decodePk` by `rfl`. -/
abbrev codec128s : CoreWireCodec Link.vp.params Link.prims.core :=
  SLHDSA.Concrete.approvedWireCodec Link.S128

example (raw : List Byte) : decodeSignature Link.vp codec128s raw = Link.decodeSig raw := rfl
example (raw : List Byte) : decodePublicKey codec128s raw = Link.decodePk raw := rfl

/-- **SUF-CMA security of SLH-DSA-SHA2-128s on byte strings (internal algorithms).** -/
theorem slhdsa_bytes_suf_cma_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : BytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalSplit (bytesToTypedS S).toUnforgeableAdversary :=
  slhdsa_bytes_suf_cma structural_128s S

/-- **EUF-CMA security of SLH-DSA-SHA2-128s on byte strings (internal algorithms).** -/
theorem slhdsa_bytes_euf_cma_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : BytesForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalSplit (bytesToTyped A) :=
  slhdsa_bytes_euf_cma structural_128s A

/-- **SUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s on byte strings.** -/
theorem slhdsa_pure_bytes_suf_cma_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (S : PureBytesStrongForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.strongUnforgeableAdvantage ProbCompRuntime.probComp S ≤
      betaSufFinalSplit (toInternal (pureBytesToTyped S.toUnforgeableAdversary)) :=
  slhdsa_pure_bytes_suf_cma structural_128s S

/-- **EUF-CMA security of the external pure interface of SLH-DSA-SHA2-128s on byte strings.** -/
theorem slhdsa_pure_bytes_euf_cma_128s
    (optRand : PublicKeyCore Link.prims.core → ProbComp Link.prims.Y)
    (pkSeedDist : ProbComp Link.prims.PkSeed)
    (A : PureBytesForger Link.vp Link.prims codec128s optRand pkSeedDist) :
    SignatureAlg.unforgeableAdvantage ProbCompRuntime.probComp A ≤
      betaEufFinalSplit (toInternal (pureBytesToTyped A)) :=
  slhdsa_pure_bytes_euf_cma structural_128s A

#print axioms Coded.unforgeableAdvantage_le
#print axioms Coded.strongUnforgeableAdvantage_le
#print axioms Coded.reduce_queryBound
#print axioms bytesView
#print axioms pureBytesView
#print axioms bytes_advantage_le
#print axioms bytes_strong_advantage_le
#print axioms pure_bytes_advantage_le
#print axioms pure_bytes_strong_advantage_le
#print axioms bytesToTyped_queryBound
#print axioms pureBytesToTyped_queryBound
#print axioms toInternal_pureBytesToTyped_queryBound
#print axioms bytes_bound_of_typed_bound
#print axioms bytes_strong_bound_of_typed_bound
#print axioms pure_bytes_bound_of_internal_bound
#print axioms pure_bytes_strong_bound_of_internal_bound
#print axioms byteVerify_byteSign
#print axioms byteVerifyPure_byteSignPure
#print axioms bytesAlg_perfectlyComplete
#print axioms pureBytesAlg_complete
#print axioms slhdsa_bytes_suf_cma
#print axioms slhdsa_bytes_euf_cma
#print axioms slhdsa_pure_bytes_suf_cma
#print axioms slhdsa_pure_bytes_euf_cma
#print axioms slhdsa_bytes_suf_cma_128s
#print axioms slhdsa_bytes_euf_cma_128s
#print axioms slhdsa_pure_bytes_suf_cma_128s
#print axioms slhdsa_pure_bytes_euf_cma_128s

end Reduction
