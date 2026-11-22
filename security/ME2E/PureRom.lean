import ME2E.Basic
import MLink.Security
import E2E.GuardedRom
import E2E.CodedRom

/-!
# Random-oracle model for the external pure interface (context strings), all six SHA-2 sets

Port of the single-set `E2E/PureRom.lean` and of the set-independent part of its
`E2E/PureRomBytes.lean` (git `26aa3d8`), generic in `S : MLink.Sha2Set` (one proof for the six sets).
`E2E/GuardedRom.lean` and `CodedRom.lean` mention no parameter set and are kept unmodified
(library `E2E`).

What in the single-set files is specific to SHA2-128s, and what replaces it here:

* `Link.vp`, `Link.prims`, `Reduction.codec128s` → `S.vp`, `S.prims`, `MReduction.codec S`;
* `Link.security_128s` (VCVio's `strongUnforgeableAdvantage_sha2_le` at the 128s
  `ApprovedAddressBounds`) → `MLink.security_sha2 S`, the same VCVio theorem at
  `fipsApprovedAddressBounds S.fips`, which VCVio proves for every `FipsParameterSet`: the
  random-oracle bound is available for **all six** SHA-2 sets;
* `Link.romScheme_map_romAnswer_128s` → `MLink.romScheme_map_romAnswer_sha2 S`;
* the bound `securityBound vp.params (256 ^ 16) 2 1 qh qs` → `securityBound S.vp.params
  (256 ^ S.vp.params.n) 2 1 qh qs` (`n = 16, 24, 32`).

Everything else — the wrapper `GuardedRom.scheme` behind `Reduction.pureEncode`, the wrapper
forger `GuardedRom.reduceS`, the byte-level view `CodedRom.View` — is generic in VCVio's
`ValidatedParams` / `Primitives` and is used as it is.

Contents (names as in the single-set tree, with `128s` replaced by `sha2`):

* `pureRomScheme S optRand pkSeedDist` — the external pure scheme with the tweakable hash, `H_msg`
  and `PRF_msg` as three random oracles; `pureRomScheme_instantiation` (answered by SHA-2 it *is*
  `Reduction.externalAlg S.vp S.prims optRand pkSeedDist`); `toInternalRom`,
  `pure_rom_advantage_le`, `toInternalRom_romQueryBound`; bounds `pure_security_sha2`,
  `pure_security_sha2_euf`: the internal bound at the same `qh`, `qs`.
* `pureBytesRomScheme S optRand pkSeedDist` — `Reduction.pureBytesAlg` in the random-oracle
  model; `pureBytesRomScheme_instantiation` (answered by SHA-2 it *is* `Reduction.pureBytesAlg
  S.vp S.prims (codec S) optRand pkSeedDist`); `pureBytesRomView`, `bytesToRom`,
  `pure_bytes_rom_advantage_le`; bounds `pure_bytes_security_sha2`, `pure_bytes_security_sha2_euf`.

The per-set headlines (`ME2E.sha2_<set>.pure_rom_security`, `api_pure_rom_security`,
`rust_pure_rom_security_bytes`, `api_pure_rom_security_bytes`) are in `ME2E/Rom/Sha2_<set>.lean`.
-/

namespace ME2E

open SLHDSA SLHDSA.Concrete SLHDSA.Security OracleComp OracleSpec SignatureAlg ENNReal
open MLink (Sha2Set)
open MReduction (codec)
open Reduction (externalAlg pureEncode constSig byteSignPure byteVerifyPure pureBytesAlg
  encodePureSig decodePureSig)

variable (S : Sha2Set)

/-! ### The typed scheme -/

/-- **The external pure SLH-DSA scheme in the random-oracle model** at the set `S` (FIPS 205
Alg. 21/22/24 on top of the three-oracle `romScheme` of `MLink.security_sha2`).  Messages are
`(message, context)` pairs of byte lists; signatures are `Except External.Error (SignatureCore …)`.
Signing `(M, ctx)` returns the error `contextTooLong` if `|ctx| > 255` (no sample, no query) and
otherwise `.ok σ` with `σ ← romScheme.sign pk sk (0x00 ‖ |ctx| ‖ ctx ‖ M)`; verification accepts
only `.ok σ` with `|ctx| ≤ 255`, and then verifies `σ` on that internal message. -/
noncomputable def pureRomScheme (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec S.prims.core))
      (List SLHDSA.Byte × List SLHDSA.Byte)
      (PublicKeyCore S.prims.core) (SecretKeyCore S.prims.core)
      (Except External.Error (GeneralScheme.SignatureCore S.vp S.prims.core)) :=
  E2E.GuardedRom.scheme (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist)
    pureEncode

theorem pureRomScheme_sign (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk : PublicKeyCore S.prims.core)
    (sk : SecretKeyCore S.prims.core) (message context : List SLHDSA.Byte)
    (h : context.length ≤ 255) :
    (pureRomScheme S optRand pkSeedDist).sign pk sk (message, context) =
      Except.ok <$> (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist).sign
        pk sk ([0, UInt8.ofNat context.length] ++ context ++ message) := by
  simp only [pureRomScheme, E2E.GuardedRom.scheme, pureEncode,
    External.encodePureMessage_eq_ok context message h]

theorem pureRomScheme_sign_tooLong (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk : PublicKeyCore S.prims.core)
    (sk : SecretKeyCore S.prims.core) (message context : List SLHDSA.Byte)
    (h : 255 < context.length) :
    (pureRomScheme S optRand pkSeedDist).sign pk sk (message, context) =
      pure (.error (.contextTooLong context.length)) := by
  have he : External.encodePureMessage context message =
      .error (.contextTooLong context.length) := by
    unfold External.encodePureMessage External.encodeMessage
    rw [External.requireContext_eq_error context h]; rfl
  simp only [pureRomScheme, E2E.GuardedRom.scheme, pureEncode, he]

theorem pureRomScheme_verify_ok (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk : PublicKeyCore S.prims.core)
    (message context : List SLHDSA.Byte) (σ : GeneralScheme.SignatureCore S.vp S.prims.core)
    (h : context.length ≤ 255) :
    (pureRomScheme S optRand pkSeedDist).verify pk (message, context) (.ok σ) =
      (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist).verify pk
        ([0, UInt8.ofNat context.length] ++ context ++ message) σ := by
  simp only [pureRomScheme, E2E.GuardedRom.scheme, pureEncode,
    External.encodePureMessage_eq_ok context message h]

/-- **Instantiation.**  Answering the three oracles of `pureRomScheme S` by the SHA-2 functions of
FIPS 205 §11.2 at the set (`romAnswer S.prims`), uniform sampling untouched, gives exactly
`Reduction.externalAlg S.vp S.prims optRand pkSeedDist`.  An identity of programs; it does not
transfer the bound. -/
theorem pureRomScheme_instantiation (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) :
    (pureRomScheme S optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer S.prims))) =
      externalAlg S.vp S.prims optRand pkSeedDist := by
  rw [pureRomScheme, E2E.GuardedRom.map_scheme, MLink.romScheme_map_romAnswer_sha2]
  rfl

/-! ### The reduction and the bound -/

/-- **The wrapper forger** (as `E2E.toInternalRom`): runs the pure forger once, forwards every
sampling and hash query, answers a signing query `(M, ctx)` with the error if `|ctx| > 255` (no
query) and otherwise by one internal signing query on `0x00 ‖ |ctx| ‖ ctx ‖ M`. -/
noncomputable def toInternalRom {S : Sha2Set}
    {optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y}
    {pkSeedDist : ProbComp S.prims.PkSeed}
    (F : StrongUnforgeableAdversary (pureRomScheme S optRand pkSeedDist)) :
    StrongUnforgeableAdversary
      (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist) :=
  E2E.GuardedRom.reduceS _ pureEncode ([], constSig default) F

theorem pure_rom_advantage_le {S : Sha2Set}
    {optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y}
    {pkSeedDist : ProbComp S.prims.PkSeed}
    (F : StrongUnforgeableAdversary (pureRomScheme S optRand pkSeedDist)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) F ≤
      strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) (toInternalRom F) :=
  E2E.GuardedRom.strongUnforgeableAdvantage_le _ pureEncode Reduction.pureEncode_injective _ F

theorem toInternalRom_romQueryBound {S : Sha2Set}
    {optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y}
    {pkSeedDist : ProbComp S.prims.PkSeed}
    (F : StrongUnforgeableAdversary (pureRomScheme S optRand pkSeedDist)) {qh qs : ℕ}
    (hF : F.RomQueryBound qh qs) : (toInternalRom F).RomQueryBound qh qs :=
  E2E.GuardedRom.romQueryBound_reduceS _ pureEncode _ F hF

/-- **SUF-CMA of the external pure interface of SLH-DSA-SHA2 (set `S`) in the three-oracle
model**: at most `securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs`, the internal bound of
`MLink.security_sha2` at the same `qh`, `qs`. -/
theorem pure_security_sha2 (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (F : StrongUnforgeableAdversary (pureRomScheme S optRand pkSeedDist)) {qh qs : ℕ}
    (hF : F.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) F ≤
      securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs :=
  (pure_rom_advantage_le F).trans
    (MLink.security_sha2 S (Equiv.refl _) optRand pkSeedDist (toInternalRom F)
      (toInternalRom_romQueryBound F hF))

/-- **EUF-CMA of the external pure interface in the three-oracle model**: the same bound. -/
theorem pure_security_sha2_euf (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (A : UnforgeableAdversary (pureRomScheme S optRand pkSeedDist)) {qh qs : ℕ}
    (hA : A.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) A ≤
      securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ A).trans
    (pure_security_sha2 S optRand pkSeedDist ⟨A.main⟩ hA)

/-! ### Signing at a given `opt_rand` -/

/-- The random-oracle signing of `romScheme` after `opt_rand` has been drawn. -/
noncomputable def romSignAt (sk : SecretKeyCore S.prims.core) (addrnd : S.prims.Y)
    (msg : List SLHDSA.Byte) :
    OracleComp (unifSpec + hashSpec S.prims.core)
      (GeneralScheme.SignatureCore S.vp S.prims.core) := do
  let R ← (query (spec := prfMsgSpec S.prims.core) ⟨sk.skPrf, addrnd, msg⟩ :
    OracleComp (unifSpec + hashSpec S.prims.core) S.prims.Y)
  GeneralScheme.signInternalWithSecretRandomizerM S.prims.core
    (oracleSecret S.prims.core (Equiv.refl _) sk.pkSeed sk.skSeed) msg sk.pkSeed sk.pkRoot R

theorem romScheme_sign_eq_romSignAt (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk : PublicKeyCore S.prims.core)
    (sk : SecretKeyCore S.prims.core) (msg : List SLHDSA.Byte) :
    (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist).sign pk sk msg = (do
      let addrnd ← (optRand pk : ProbComp S.prims.Y)
      romSignAt S sk addrnd msg) := rfl

theorem simulateQ_sha_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdAnswerImpl (romAnswer S.prims))
      (liftM oa : OracleComp (unifSpec + hashSpec S.prims.core) α) = oa := by
  rw [unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.liftTarget_self, simulateQ_id']

/-- With its oracles answered by SHA-2, `romSignAt` is `GeneralScheme.signInternal`. -/
theorem simulateQ_sha_romSignAt (sk : SecretKeyCore S.prims.core) (addrnd : S.prims.Y)
    (msg : List SLHDSA.Byte) :
    simulateQ (unifFwdAnswerImpl (romAnswer S.prims)) (romSignAt S sk addrnd msg) =
      (pure (GeneralScheme.signInternal S.vp S.prims msg sk addrnd) : ProbComp _) := by
  have h := congrArg (fun A => A.sign ⟨sk.pkSeed, sk.pkRoot⟩ sk msg)
    (MLink.romScheme_map_romAnswer_sha2 S (fun _ => (pure addrnd : ProbComp S.prims.Y))
      ($ᵗ S.prims.PkSeed))
  simp only [SignatureAlg.map_sign, romScheme_sign_eq_romSignAt, internalAlg] at h
  change simulateQ (unifFwdAnswerImpl (romAnswer S.prims)) (liftM (pure addrnd) >>= _) = _ at h
  rw [simulateQ_bind, simulateQ_sha_liftM, pure_bind, pure_bind] at h
  exact h

/-! ### The byte-level scheme in the random-oracle model -/

/-- Byte-level pure signing at a given `opt_rand`, with oracles. -/
noncomputable def romSignPureBytes (m ctx skb : List SLHDSA.Byte) (addrnd : S.prims.Y) :
    OracleComp (unifSpec + hashSpec S.prims.core) (Option (List SLHDSA.Byte)) :=
  match decodeSecretKey (codec S) skb with
  | .ok sk =>
    match pureEncode (m, ctx) with
    | .ok m' => (fun σ => some (encodeSignature S.vp (codec S) σ)) <$> romSignAt S sk addrnd m'
    | .error _ => pure none
  | .error _ => pure none

/-- **`pureBytesAlg` in the random-oracle model** at the set `S` (FIPS 205 Alg. 21/22/24 on byte
strings; the tweakable hash, `H_msg` and `PRF_msg` as three oracles). -/
noncomputable def pureBytesRomScheme (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec S.prims.core))
      (List SLHDSA.Byte × List SLHDSA.Byte) (List SLHDSA.Byte) (List SLHDSA.Byte)
      (Option (List SLHDSA.Byte)) where
  keygen := (fun ks => (encodePublicKey (codec S) ks.1, encodeSecretKey (codec S) ks.2)) <$>
    (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist).keygen
  sign pk sk mc :=
    if mc.2.length ≤ 255 then
      match decodePublicKey (codec S) pk with
      | .ok k => do
        let addrnd ← (optRand k : ProbComp S.prims.Y)
        romSignPureBytes S mc.1 mc.2 sk addrnd
      | .error _ => pure none
    else pure none
  verify pk mc sig := match sig with
    | some raw =>
      match decodeSignature S.vp (codec S) raw, decodePublicKey (codec S) pk with
      | .ok s, .ok k => (pureRomScheme S optRand pkSeedDist).verify k mc (.ok s)
      | _, _ => pure false
    | none => pure false

theorem simulateQ_sha_romSignPureBytes (m ctx skb : List SLHDSA.Byte) (addrnd : S.prims.Y) :
    simulateQ (unifFwdAnswerImpl (romAnswer S.prims)) (romSignPureBytes S m ctx skb addrnd) =
      (pure (byteSignPure S.vp S.prims (codec S) m ctx skb addrnd) : ProbComp _) := by
  unfold romSignPureBytes byteSignPure
  cases decodeSecretKey (codec S) skb with
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

theorem simulateQ_sha_pureBytesRom_verify
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk : List SLHDSA.Byte)
    (mc : List SLHDSA.Byte × List SLHDSA.Byte) (sig : Option (List SLHDSA.Byte)) :
    simulateQ (unifFwdAnswerImpl (romAnswer S.prims))
        ((pureBytesRomScheme S optRand pkSeedDist).verify pk mc sig) =
      (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).verify pk mc sig := by
  obtain ⟨m, ctx⟩ := mc
  cases sig with
  | none => exact simulateQ_pure _ _
  | some raw =>
    change simulateQ _ (match decodeSignature S.vp (codec S) raw, decodePublicKey (codec S) pk with
      | .ok s, .ok k => (pureRomScheme S optRand pkSeedDist).verify k (m, ctx) (.ok s)
      | _, _ => pure false) =
      pure (byteVerifyPure S.vp S.prims (codec S) m raw ctx pk)
    unfold byteVerifyPure
    cases decodeSignature S.vp (codec S) raw with
    | error e => exact simulateQ_pure _ _
    | ok s =>
      cases decodePublicKey (codec S) pk with
      | error e => exact simulateQ_pure _ _
      | ok k =>
        have hv := congrArg (fun A => A.verify k (m, ctx) (.ok s))
          (pureRomScheme_instantiation S optRand pkSeedDist)
        simp only [SignatureAlg.map_verify] at hv
        exact hv.trans (Reduction.externalAlg_verify_ok S.vp S.prims optRand pkSeedDist k m ctx s)

theorem simulateQ_sha_pureBytesRom_keygen
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) :
    simulateQ (unifFwdAnswerImpl (romAnswer S.prims))
        (pureBytesRomScheme S optRand pkSeedDist).keygen =
      (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).keygen := by
  have hk := congrArg SignatureAlg.keygen (MLink.romScheme_map_romAnswer_sha2 S optRand pkSeedDist)
  simp only [SignatureAlg.map_keygen] at hk
  have hd : (pureBytesRomScheme S optRand pkSeedDist).keygen =
      (fun ks => (encodePublicKey (codec S) ks.1, encodeSecretKey (codec S) ks.2)) <$>
        (romScheme (vp := S.vp) S.prims.core (Equiv.refl _) optRand pkSeedDist).keygen := rfl
  rw [hd, simulateQ_map, hk]
  simp only [internalAlg, pureBytesAlg, map_bind, map_pure]
  rfl

theorem simulateQ_sha_pureBytesRom_sign
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) (pk sk : List SLHDSA.Byte)
    (mc : List SLHDSA.Byte × List SLHDSA.Byte) :
    simulateQ (unifFwdAnswerImpl (romAnswer S.prims))
        ((pureBytesRomScheme S optRand pkSeedDist).sign pk sk mc) =
      (pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist).sign pk sk mc := by
  obtain ⟨m, ctx⟩ := mc
  simp only [pureBytesRomScheme, pureBytesAlg]
  split_ifs with hc
  · cases decodePublicKey (codec S) pk with
    | error e => exact simulateQ_pure _ _
    | ok k =>
      change simulateQ (unifFwdAnswerImpl (romAnswer S.prims)) (liftM (optRand k) >>= _) = _
      rw [simulateQ_bind, simulateQ_sha_liftM]
      exact bind_congr fun a => simulateQ_sha_romSignPureBytes S m ctx sk a
  · exact simulateQ_pure _ _

/-- **Instantiation, byte level.**  Answering the three oracles of `pureBytesRomScheme S` by the
SHA-2 functions gives exactly `Reduction.pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist`,
the byte-level scheme whose cores the Rust functions compute. -/
theorem pureBytesRomScheme_instantiation
    (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) :
    (pureBytesRomScheme S optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer S.prims))) =
      pureBytesAlg S.vp S.prims (codec S) optRand pkSeedDist :=
  SignatureAlg.ext (simulateQ_sha_pureBytesRom_keygen S optRand pkSeedDist)
    (funext fun pk => funext fun sk => funext fun mc =>
      simulateQ_sha_pureBytesRom_sign S optRand pkSeedDist pk sk mc)
    (funext fun pk => funext fun mc => funext fun sig =>
      simulateQ_sha_pureBytesRom_verify S optRand pkSeedDist pk mc sig)

/-- `pureBytesRomScheme S` is `pureRomScheme S` seen through the FIPS wire encodings. -/
noncomputable def pureBytesRomView (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed) :
    E2E.CodedRom.View (pureRomScheme S optRand pkSeedDist)
      (pureBytesRomScheme S optRand pkSeedDist) where
  encPk := encodePublicKey (codec S)
  encSk := encodeSecretKey (codec S)
  encS := encodePureSig S.vp S.prims (codec S)
  decS := decodePureSig S.vp S.prims (codec S)
  keygen_eq := rfl
  sign_eq pk sk mc := by
    obtain ⟨m, ctx⟩ := mc
    by_cases h : ctx.length ≤ 255
    · rw [pureRomScheme_sign S optRand pkSeedDist pk sk m ctx h, romScheme_sign_eq_romSignAt]
      simp only [pureBytesRomScheme, h, ite_true, decodePublicKey_encode, romSignPureBytes,
        decodeSecretKey_encode, pureEncode, External.encodePureMessage_eq_ok ctx m h]
      simp only [map_bind, Functor.map_map]
      rfl
    · rw [pureRomScheme_sign_tooLong S optRand pkSeedDist pk sk m ctx (by omega)]
      simp [pureBytesRomScheme, h, encodePureSig, Except.toOption]
  verify_eq pk mc sb := by
    cases sb with
    | none => rfl
    | some raw =>
      simp only [pureBytesRomScheme, decodePublicKey_encode, decodePureSig]
      cases decodeSignature S.vp (codec S) raw <;> rfl
  canonical := (Reduction.pureBytesView S.vp S.prims (codec S) optRand pkSeedDist).canonical

/-- **The typed random-oracle forger built from a byte forger.** -/
noncomputable def bytesToRom {S : Sha2Set}
    {optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y}
    {pkSeedDist : ProbComp S.prims.PkSeed}
    (F : StrongUnforgeableAdversary (pureBytesRomScheme S optRand pkSeedDist)) :
    StrongUnforgeableAdversary (pureRomScheme S optRand pkSeedDist) :=
  E2E.CodedRom.reduceS (pureBytesRomView S optRand pkSeedDist) (.error (.contextTooLong 0)) F

theorem pure_bytes_rom_advantage_le {S : Sha2Set}
    {optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y}
    {pkSeedDist : ProbComp S.prims.PkSeed}
    (F : StrongUnforgeableAdversary (pureBytesRomScheme S optRand pkSeedDist)) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) F ≤
        strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core))
          (toInternalRom (bytesToRom F)) ∧
      ∀ qh qs : ℕ, F.RomQueryBound qh qs → (toInternalRom (bytesToRom F)).RomQueryBound qh qs :=
  ⟨(E2E.CodedRom.strongUnforgeableAdvantage_le _ _ F).trans (pure_rom_advantage_le _),
    fun _ _ hF => toInternalRom_romQueryBound _ (E2E.CodedRom.romQueryBound_reduceS _ _ F hF)⟩

/-- **SUF-CMA of the byte-level external pure scheme in the three-oracle model** at the set `S`. -/
theorem pure_bytes_security_sha2 (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (F : StrongUnforgeableAdversary (pureBytesRomScheme S optRand pkSeedDist)) {qh qs : ℕ}
    (hF : F.RomQueryBound qh qs) :
    strongUnforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) F ≤
      securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs :=
  (E2E.CodedRom.strongUnforgeableAdvantage_le _ _ F).trans
    (pure_security_sha2 S optRand pkSeedDist (bytesToRom F)
      (E2E.CodedRom.romQueryBound_reduceS _ _ F hF))

/-- **EUF-CMA of the byte-level external pure scheme in the three-oracle model.** -/
theorem pure_bytes_security_sha2_euf (optRand : PublicKeyCore S.prims.core → ProbComp S.prims.Y)
    (pkSeedDist : ProbComp S.prims.PkSeed)
    (A : UnforgeableAdversary (pureBytesRomScheme S optRand pkSeedDist)) {qh qs : ℕ}
    (hA : A.RomQueryBound qh qs) :
    unforgeableAdvantage (ProbCompRuntime.rom (hashSpec S.prims.core)) A ≤
      securityBound S.vp.params (256 ^ S.vp.params.n) 2 1 qh qs :=
  (unforgeableAdvantage_le_strongUnforgeableAdvantage _ A).trans
    (pure_bytes_security_sha2 S optRand pkSeedDist ⟨A.main⟩ hA)

end ME2E

#print axioms ME2E.pureRomScheme_sign
#print axioms ME2E.pureRomScheme_sign_tooLong
#print axioms ME2E.pureRomScheme_verify_ok
#print axioms ME2E.pureRomScheme_instantiation
#print axioms ME2E.pure_rom_advantage_le
#print axioms ME2E.toInternalRom_romQueryBound
#print axioms ME2E.pure_security_sha2
#print axioms ME2E.pure_security_sha2_euf
#print axioms ME2E.simulateQ_sha_romSignAt
#print axioms ME2E.simulateQ_sha_pureBytesRom_keygen
#print axioms ME2E.simulateQ_sha_pureBytesRom_sign
#print axioms ME2E.simulateQ_sha_pureBytesRom_verify
#print axioms ME2E.pureBytesRomScheme_instantiation
#print axioms ME2E.pure_bytes_rom_advantage_le
#print axioms ME2E.pure_bytes_security_sha2
#print axioms ME2E.pure_bytes_security_sha2_euf
