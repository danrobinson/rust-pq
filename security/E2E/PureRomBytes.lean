import E2E.PureRom
import E2E.CodedRom

/-!
# Random-oracle model for the external pure interface, on byte strings

`E2E/PureRom.lean` states the random-oracle theorem for the external pure interface on *typed*
keys and signatures (`pureRomScheme`, instantiating to `Reduction.externalAlg`), as the internal
random-oracle theorem `E2E.end_to_end` does.  The standard-model headlines `rust_pure_security`
and `api_pure_security` are stated on the byte-level scheme `Reduction.pureBytesAlg`, whose
deterministic cores the Rust functions are pointwise equal to.  This file gives the
random-oracle theorem in that form:

* `pureBytesRomScheme` — `pureBytesAlg` with the tweakable hash, `H_msg` and `PRF_msg` as the three
  oracles: public keys, secret keys, messages, contexts are byte strings, a signature is
  `Option (List Byte)`;
* `pureBytesRomScheme_instantiation` — answered by SHA-2 it **is** `Reduction.pureBytesAlg vp prims
  codec128s optRand pkSeedDist`;
* `pureBytesRomView` — it is `pureRomScheme` seen through the FIPS wire encodings (the encodings
  of `Reduction.pureBytesView`);
* `bytesToRom` and the bounds `pure_bytes_security_128s`, `pure_bytes_security_128s_euf`: the
  same bound `securityBound vp.params (256 ^ 16) 2 1 qh qs` at the same `qh`, `qs`;
* headlines `rust_pure_rom_security_bytes` (`slh_keygen_internal`, `slh_sign`, `slh_verify`) and
  `api_pure_rom_security_bytes` (`api.keygen`, `api.sign`, `api.sign_deterministic`,
  `api.verify`, through `ApiPureBytesEndToEnd`).
-/

namespace E2E

open Aeneas Aeneas.Std Result
open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open slhdsa (bytes Room)
open Link (vp prims cv sp sigBytes pkBytes skBytes)
open Reduction (externalAlg pureEncode constSig byteKeygen byteSignPure byteVerifyPure codec128s
  pureBytesAlg encodePureSig decodePureSig)

/-! ### Signing at a given `opt_rand` -/

/-- The random-oracle signing of `romScheme` after `opt_rand` has been drawn: query `PRF_msg`
for the randomizer `R`, then sign with every secret value drawn from the oracle. -/
noncomputable def romSignAt (sk : SecretKeyCore prims.core) (addrnd : prims.Y)
    (msg : List SLHDSA.Byte) :
    OracleComp (unifSpec + hashSpec prims.core) (GeneralScheme.SignatureCore vp prims.core) := do
  let R ← (query (spec := prfMsgSpec prims.core) ⟨sk.skPrf, addrnd, msg⟩ :
    OracleComp (unifSpec + hashSpec prims.core) prims.Y)
  GeneralScheme.signInternalWithSecretRandomizerM prims.core
    (oracleSecret prims.core (Equiv.refl _) sk.pkSeed sk.skSeed) msg sk.pkSeed sk.pkRoot R

theorem romScheme_sign_eq_romSignAt (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk : PublicKeyCore prims.core)
    (sk : SecretKeyCore prims.core) (msg : List SLHDSA.Byte) :
    (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).sign pk sk msg = (do
      let addrnd ← (optRand pk : ProbComp prims.Y)
      romSignAt sk addrnd msg) := rfl

theorem simulateQ_sha_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims))
      (liftM oa : OracleComp (unifSpec + hashSpec prims.core) α) = oa := by
  rw [unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.liftTarget_self, simulateQ_id']

/-- With its oracles answered by SHA-2, `romSignAt` is `GeneralScheme.signInternal`. -/
theorem simulateQ_sha_romSignAt (sk : SecretKeyCore prims.core) (addrnd : prims.Y)
    (msg : List SLHDSA.Byte) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims)) (romSignAt sk addrnd msg) =
      (pure (GeneralScheme.signInternal vp prims msg sk addrnd) : ProbComp _) := by
  have h := congrArg (fun A => A.sign ⟨sk.pkSeed, sk.pkRoot⟩ sk msg)
    (Link.romScheme_map_romAnswer_128s (fun _ => (pure addrnd : ProbComp prims.Y))
      ($ᵗ prims.PkSeed))
  simp only [SignatureAlg.map_sign, romScheme_sign_eq_romSignAt, internalAlg] at h
  change simulateQ (unifFwdAnswerImpl (romAnswer prims)) (liftM (pure addrnd) >>= _) = _ at h
  rw [simulateQ_bind, simulateQ_sha_liftM, pure_bind, pure_bind] at h
  exact h

/-! ### The byte-level scheme in the random-oracle model -/

/-- Byte-level pure signing at a given `opt_rand`, with oracles: parse the secret key; `none` if
it does not parse or the context is longer than 255 bytes; otherwise `some` of the encoding of
`romSignAt sk addrnd (0x00 ‖ |ctx| ‖ ctx ‖ M)`. -/
noncomputable def romSignPureBytes (m ctx skb : List SLHDSA.Byte) (addrnd : prims.Y) :
    OracleComp (unifSpec + hashSpec prims.core) (Option (List SLHDSA.Byte)) :=
  match decodeSecretKey codec128s skb with
  | .ok sk =>
    match pureEncode (m, ctx) with
    | .ok m' => (fun σ => some (encodeSignature vp codec128s σ)) <$> romSignAt sk addrnd m'
    | .error _ => pure none
  | .error _ => pure none

/-- **`pureBytesAlg` in the random-oracle model** (FIPS 205 Alg. 21/22/24 on byte strings, the
tweakable hash, `H_msg` and `PRF_msg` as three oracles).

* key generation: `romScheme`'s, followed by the FIPS encodings of both keys;
* signing `(M, ctx)`: `none` if `|ctx| > 255`; otherwise parse the public key (`none` if it does
  not parse), draw `opt_rand ← optRand pk`, and return `romSignPureBytes M ctx sk opt_rand`;
* verifying `(M, ctx)` against `some raw`: parse `raw` and the public key, reject if either fails,
  otherwise `pureRomScheme`'s verification; `none` is rejected. -/
noncomputable def pureBytesRomScheme (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec prims.core))
      (List SLHDSA.Byte × List SLHDSA.Byte) (List SLHDSA.Byte) (List SLHDSA.Byte)
      (Option (List SLHDSA.Byte)) where
  keygen := (fun ks => (encodePublicKey codec128s ks.1, encodeSecretKey codec128s ks.2)) <$>
    (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).keygen
  sign pk sk mc :=
    if mc.2.length ≤ 255 then
      match decodePublicKey codec128s pk with
      | .ok k => do
        let addrnd ← (optRand k : ProbComp prims.Y)
        romSignPureBytes mc.1 mc.2 sk addrnd
      | .error _ => pure none
    else pure none
  verify pk mc sig := match sig with
    | some raw =>
      match decodeSignature vp codec128s raw, decodePublicKey codec128s pk with
      | .ok s, .ok k => (pureRomScheme optRand pkSeedDist).verify k mc (.ok s)
      | _, _ => pure false
    | none => pure false

/-- With SHA-2, byte-level pure signing at `opt_rand` is `pure (byteSignPure …)`. -/
theorem simulateQ_sha_romSignPureBytes (m ctx skb : List SLHDSA.Byte) (addrnd : prims.Y) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims)) (romSignPureBytes m ctx skb addrnd) =
      (pure (byteSignPure vp prims codec128s m ctx skb addrnd) : ProbComp _) := by
  unfold romSignPureBytes byteSignPure
  cases decodeSecretKey codec128s skb with
  | error e => simp
  | ok sk =>
    simp only
    unfold External.signPureWithRandomizer
    cases he : pureEncode (m, ctx) with
    | error e =>
      simp only [pureEncode] at he
      simp [he, Except.toOption]
    | ok m' =>
      simp only [pureEncode] at he
      simp only [he]
      rw [simulateQ_map, simulateQ_sha_romSignAt]
      simp [Except.toOption]

/-- Verification of `pureBytesRomScheme`, answered by SHA-2, is that of `pureBytesAlg`. -/
theorem simulateQ_sha_pureBytesRom_verify (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk : List SLHDSA.Byte)
    (mc : List SLHDSA.Byte × List SLHDSA.Byte) (sig : Option (List SLHDSA.Byte)) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims))
        ((pureBytesRomScheme optRand pkSeedDist).verify pk mc sig) =
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).verify pk mc sig := by
  obtain ⟨m, ctx⟩ := mc
  cases sig with
  | none => exact simulateQ_pure _ _
  | some raw =>
    change simulateQ _ (match decodeSignature vp codec128s raw, decodePublicKey codec128s pk with
      | .ok s, .ok k => (pureRomScheme optRand pkSeedDist).verify k (m, ctx) (.ok s)
      | _, _ => pure false) =
      pure (byteVerifyPure vp prims codec128s m raw ctx pk)
    unfold byteVerifyPure
    cases decodeSignature vp codec128s raw with
    | error e => exact simulateQ_pure _ _
    | ok s =>
      cases decodePublicKey codec128s pk with
      | error e => exact simulateQ_pure _ _
      | ok k =>
        have hv := congrArg (fun A => A.verify k (m, ctx) (.ok s))
          (pureRomScheme_instantiation optRand pkSeedDist)
        simp only [SignatureAlg.map_verify] at hv
        exact hv.trans (Reduction.externalAlg_verify_ok vp prims optRand pkSeedDist k m ctx s)

/-- Key generation of `pureBytesRomScheme`, answered by SHA-2, is that of `pureBytesAlg`. -/
theorem simulateQ_sha_pureBytesRom_keygen (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims)) (pureBytesRomScheme optRand pkSeedDist).keygen =
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).keygen := by
  have hk := congrArg SignatureAlg.keygen (Link.romScheme_map_romAnswer_128s optRand pkSeedDist)
  simp only [SignatureAlg.map_keygen] at hk
  have hd : (pureBytesRomScheme optRand pkSeedDist).keygen =
      (fun ks => (encodePublicKey codec128s ks.1, encodeSecretKey codec128s ks.2)) <$>
        (romScheme (vp := vp) prims.core (Equiv.refl _) optRand pkSeedDist).keygen := rfl
  rw [hd, simulateQ_map, hk]
  simp only [internalAlg, pureBytesAlg, map_bind, map_pure]
  rfl

/-- Signing of `pureBytesRomScheme`, answered by SHA-2, is that of `pureBytesAlg`. -/
theorem simulateQ_sha_pureBytesRom_sign (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) (pk sk : List SLHDSA.Byte)
    (mc : List SLHDSA.Byte × List SLHDSA.Byte) :
    simulateQ (unifFwdAnswerImpl (romAnswer prims))
        ((pureBytesRomScheme optRand pkSeedDist).sign pk sk mc) =
      (pureBytesAlg vp prims codec128s optRand pkSeedDist).sign pk sk mc := by
  obtain ⟨m, ctx⟩ := mc
  simp only [pureBytesRomScheme, pureBytesAlg]
  split_ifs with hc
  · cases decodePublicKey codec128s pk with
    | error e => exact simulateQ_pure _ _
    | ok k =>
      change simulateQ (unifFwdAnswerImpl (romAnswer prims)) (liftM (optRand k) >>= _) = _
      rw [simulateQ_bind, simulateQ_sha_liftM]
      exact bind_congr fun a => simulateQ_sha_romSignPureBytes m ctx sk a
  · exact simulateQ_pure _ _

/-- **Instantiation.**  Answering the three oracles of `pureBytesRomScheme` by the SHA-2
functions (`romAnswer prims`) gives exactly the byte-level scheme `Reduction.pureBytesAlg vp prims
codec128s optRand pkSeedDist` of `rust_pure_security` / `api_pure_security`, whose cores the
Rust functions compute. -/
theorem pureBytesRomScheme_instantiation (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    (pureBytesRomScheme optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      pureBytesAlg vp prims codec128s optRand pkSeedDist :=
  SignatureAlg.ext (simulateQ_sha_pureBytesRom_keygen optRand pkSeedDist)
    (funext fun pk => funext fun sk => funext fun mc =>
      simulateQ_sha_pureBytesRom_sign optRand pkSeedDist pk sk mc)
    (funext fun pk => funext fun mc => funext fun sig =>
      simulateQ_sha_pureBytesRom_verify optRand pkSeedDist pk mc sig)

/-- **`pureBytesRomScheme` is `pureRomScheme` seen through the FIPS wire encodings** (the
encodings and parser of `Reduction.pureBytesView`). -/
noncomputable def pureBytesRomView (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    CodedRom.View (pureRomScheme optRand pkSeedDist) (pureBytesRomScheme optRand pkSeedDist) where
  encPk := encodePublicKey codec128s
  encSk := encodeSecretKey codec128s
  encS := encodePureSig vp prims codec128s
  decS := decodePureSig vp prims codec128s
  keygen_eq := rfl
  sign_eq pk sk mc := by
    obtain ⟨m, ctx⟩ := mc
    by_cases h : ctx.length ≤ 255
    · rw [pureRomScheme_sign optRand pkSeedDist pk sk m ctx h, romScheme_sign_eq_romSignAt]
      simp only [pureBytesRomScheme, h, ite_true, decodePublicKey_encode, romSignPureBytes,
        decodeSecretKey_encode, pureEncode, External.encodePureMessage_eq_ok ctx m h]
      simp only [map_bind, Functor.map_map]
      rfl
    · rw [pureRomScheme_sign_tooLong optRand pkSeedDist pk sk m ctx (by omega)]
      simp [pureBytesRomScheme, h, encodePureSig, Except.toOption]
  verify_eq pk mc sb := by
    cases sb with
    | none => rfl
    | some raw =>
      simp only [pureBytesRomScheme, decodePublicKey_encode, decodePureSig]
      cases decodeSignature vp codec128s raw <;> rfl
  canonical := (Reduction.pureBytesView vp prims codec128s optRand pkSeedDist).canonical

/-- **The typed random-oracle forger built from a byte forger**: encode the public key, run the
byte forger once, forward every sampling and hash query, answer a signing query by one typed
signing query and encode the answer (`none` for the error value), parse the forgery (an
unparsable one becomes the error value, which is never accepted). -/
noncomputable def bytesToRom {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
    {pkSeedDist : ProbComp prims.PkSeed}
    (S : StrongUnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) :
    StrongUnforgeableAdversary (pureRomScheme optRand pkSeedDist) :=
  CodedRom.reduceS (pureBytesRomView optRand pkSeedDist) (.error (.contextTooLong 0)) S

/-- **The reduction chain for a byte forger**: its SUF-CMA advantage is at most that of the
internal random-oracle forger `toInternalRom (bytesToRom S)`, which makes at most as many hash
and signing queries. -/
theorem pure_bytes_rom_advantage_le {optRand : PublicKeyCore prims.core → ProbComp prims.Y}
    {pkSeedDist : ProbComp prims.PkSeed}
    (S : StrongUnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
        strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core))
          (toInternalRom (bytesToRom S)) ∧
      ∀ qh qs : ℕ, S.RomQueryBound qh qs → (toInternalRom (bytesToRom S)).RomQueryBound qh qs :=
  ⟨(CodedRom.strongUnforgeableAdvantage_le _ _ S).trans (pure_rom_advantage_le _),
    fun _ _ hS => toInternalRom_romQueryBound _ (CodedRom.romQueryBound_reduceS _ _ S hS)⟩

/-- **SUF-CMA of the byte-level external pure scheme in the three-oracle model**: every strong
forger against `pureBytesRomScheme` with at most `qh` hash and `qs` signing queries has advantage
at most `securityBound vp.params (256 ^ 16) 2 1 qh qs`, through the typed forger
`toInternalRom (bytesToRom S)` against the internal `romScheme`, which makes at most `qh` hash
and `qs` signing queries. -/
theorem pure_bytes_security_128s (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (S : StrongUnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) {qh qs : ℕ}
    (hS : S.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  (CodedRom.strongUnforgeableAdvantage_le _ _ S).trans
    (pure_security_128s optRand pkSeedDist (bytesToRom S)
      (CodedRom.romQueryBound_reduceS _ _ S hS))

/-- **EUF-CMA of the byte-level external pure scheme in the three-oracle model.** -/
theorem pure_bytes_security_128s_euf (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed)
    (A : UnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) {qh qs : ℕ}
    (hA : A.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) A ≤
      securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ A).trans
    (pure_bytes_security_128s optRand pkSeedDist ⟨A.main⟩ hA)

/-! ### Headlines on byte strings -/

/-- **The Rust external pure interface and its random-oracle security, on byte strings.**

(a) As in `rust_pure_security`: the Rust `slh_keygen_internal`, `slh_sign`, `slh_verify` never
    panic and are pointwise equal to `byteKeygen`, `byteSignPure`, `byteVerifyPure` (under
    `Room m.length 409`), the deterministic cores of `X = Reduction.pureBytesAlg vp prims
    codec128s optRand pkSeedDist`.
(b) `X` is `pureBytesRomScheme optRand pkSeedDist` with its three oracles answered by SHA-2.
(c) SUF-CMA: every strong forger against `pureBytesRomScheme` — public key bytes in, a signing
    oracle on `(message, context)` pairs returning `Option` bytes, three random oracles; it wins
    with `((M, ctx), some raw)` accepted and never returned — making at most `qh` hash and `qs`
    signing queries has advantage at most `securityBound vp.params (256 ^ 16) 2 1 qh qs`.
(d) EUF-CMA: the same bound.

The bound is the internal random-oracle bound (`EndToEnd.security`) at the same `qh`, `qs`.
Not established: that the bound survives replacing the random oracles by SHA-256 (the
random-oracle methodology); sampling of the seeds and `addrnd` (the caller's); pre-hash mode;
side channels, the compiler, the Aeneas extraction. -/
theorem rust_pure_rom_security_bytes (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ((∀ sk_seed sk_prf pk_seed : Array U8 16#usize,
        ∃ sk pk, slhdsa.slh.slh_keygen_internal sk_seed sk_prf pk_seed = ok (sk, pk) ∧
          (wire pk.val, wire sk.val) =
            byteKeygen vp prims codec128s (node sk_seed) (node sk_prf) (node pk_seed)) ∧
      (∀ (m ctx : Slice U8) (sk : Array U8 64#usize) (addrnd : Array U8 16#usize),
        Room m.length 409 →
        ∃ r, slhdsa.slh.slh_sign m ctx sk addrnd = ok r ∧
          r.map (fun v => wire v.val) =
            byteSignPure vp prims codec128s (wire m.val) (wire ctx.val) (wire sk.val)
              (node addrnd)) ∧
      (∀ (m sig ctx : Slice U8) (pk : Array U8 32#usize), Room m.length 409 →
        slhdsa.slh.slh_verify m sig ctx pk =
          ok (byteVerifyPure vp prims codec128s (wire m.val) (wire sig.val) (wire ctx.val)
            (wire pk.val)))) ∧
    (pureBytesRomScheme optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      pureBytesAlg vp prims codec128s optRand pkSeedDist ∧
    (∀ (S : StrongUnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      S.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs) ∧
    ∀ (A : UnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      A.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) A ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  ⟨⟨rust_keygen_bytes, rust_sign_bytes, rust_verify_bytes⟩,
    pureBytesRomScheme_instantiation optRand pkSeedDist,
    fun S _ _ hS => pure_bytes_security_128s optRand pkSeedDist S hS,
    fun A _ _ hA => pure_bytes_security_128s_euf optRand pkSeedDist A hA⟩

/-- **The Rust interface `api` and its random-oracle security, on byte strings.**
`rust_pure_rom_security_bytes` with part (a) replaced by `ApiPureBytesEndToEnd`: `api.keygen`
(on the three 16-byte blocks of its 48-byte argument), `api.sign`, `api.sign_deterministic`
(`addrnd` := the `PK.seed` block of the key, i.e. the scheme at `optRand pk = pure pk.pkSeed`) and
`api.verify` never panic and are pointwise equal to the cores of `X = pureBytesAlg …`, together
with the descriptions of `X.keygen`, `X.sign`, `X.verify` and completeness.  Parts (b)–(d)
unchanged. -/
theorem api_pure_rom_security_bytes (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
    (pkSeedDist : ProbComp prims.PkSeed) :
    ApiPureBytesEndToEnd optRand pkSeedDist ∧
    (pureBytesRomScheme optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer prims))) =
      pureBytesAlg vp prims codec128s optRand pkSeedDist ∧
    (∀ (S : StrongUnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      S.RomQueryBound qh qs →
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) S ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs) ∧
    ∀ (A : UnforgeableAdversary (pureBytesRomScheme optRand pkSeedDist)) (qh qs : ℕ),
      A.RomQueryBound qh qs →
      unforgeableAdvantage (ProbCompRuntime.rom (hashSpec prims.core)) A ≤
        securityBound vp.params (256 ^ 16) 2 1 qh qs :=
  ⟨api_pure_bytes_end_to_end optRand pkSeedDist, (rust_pure_rom_security_bytes optRand pkSeedDist).2⟩

end E2E

#print axioms E2E.simulateQ_sha_romSignAt
#print axioms E2E.pureBytesRomScheme_instantiation
#print axioms E2E.simulateQ_sha_pureBytesRom_keygen
#print axioms E2E.simulateQ_sha_pureBytesRom_sign
#print axioms E2E.simulateQ_sha_pureBytesRom_verify
#print axioms E2E.pure_bytes_rom_advantage_le
#print axioms E2E.pure_bytes_security_128s
#print axioms E2E.pure_bytes_security_128s_euf
#print axioms E2E.rust_pure_rom_security_bytes
#print axioms E2E.api_pure_rom_security_bytes
