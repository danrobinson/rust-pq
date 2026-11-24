import Integration.SlhDsaShakeApiForger
import Integration.SlhDsaShakePermutationXof
import ME2E.PureRom

namespace Reduction.ShakePermutation.Honest
open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec PQ.Interactive Quantum
open ShakeApi (Xof)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (base : Xof S)

private theorem rom_conformance (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp S.Node)
    (seeds : ProbComp S.Node) :
    (romScheme (vp := S.vp) (ShakeApi.primitives S base).core (Equiv.refl _) optRand seeds).map
      (simulateQ' (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))) =
      internalAlg S.vp (ShakeApi.primitives S base) optRand seeds := by
  apply romScheme_map_romAnswer
  intro pk sk a _
  simp only [ShakeApi.primitives,ShakeApi.bundle,ShakeSecurity.primitives,List.map_cons,List.map_nil,
    List.flatten_cons,List.flatten_nil,List.append_nil,Equiv.refl_apply]

noncomputable def pureRomScheme (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec (ShakeApi.primitives S base).core))
      (List SLHDSA.Byte × List SLHDSA.Byte)
      (PublicKeyCore (ShakeApi.primitives S base).core) (SecretKeyCore (ShakeApi.primitives S base).core)
      (Except External.Error (GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S base).core)) :=
  E2E.GuardedRom.scheme (romScheme (vp := S.vp) (ShakeApi.primitives S base).core (Equiv.refl _) optRand pkSeedDist)
    pureEncode

theorem pureRomScheme_instantiation (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) :
    (pureRomScheme S base optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))) =
      externalAlg S.vp (ShakeApi.primitives S base) optRand pkSeedDist := by
  rw [pureRomScheme, E2E.GuardedRom.map_scheme, rom_conformance]
  rfl

noncomputable def romSignAt (sk : SecretKeyCore (ShakeApi.primitives S base).core) (addrnd : (ShakeApi.primitives S base).Y)
    (msg : List SLHDSA.Byte) :
    OracleComp (unifSpec + hashSpec (ShakeApi.primitives S base).core)
      (GeneralScheme.SignatureCore S.vp (ShakeApi.primitives S base).core) := do
  let R ← (query (spec := prfMsgSpec (ShakeApi.primitives S base).core) ⟨sk.skPrf, addrnd, msg⟩ :
    OracleComp (unifSpec + hashSpec (ShakeApi.primitives S base).core) (ShakeApi.primitives S base).Y)
  GeneralScheme.signInternalWithSecretRandomizerM (ShakeApi.primitives S base).core
    (oracleSecret (ShakeApi.primitives S base).core (Equiv.refl _) sk.pkSeed sk.skSeed) msg sk.pkSeed sk.pkRoot R

theorem romScheme_sign_eq_romSignAt (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) (pk : PublicKeyCore (ShakeApi.primitives S base).core)
    (sk : SecretKeyCore (ShakeApi.primitives S base).core) (msg : List SLHDSA.Byte) :
    (romScheme (vp := S.vp) (ShakeApi.primitives S base).core (Equiv.refl _) optRand pkSeedDist).sign pk sk msg = (do
      let addrnd ← (optRand pk : ProbComp (ShakeApi.primitives S base).Y)
      romSignAt S base sk addrnd msg) := rfl

theorem simulateQ_sha_liftM {α : Type} (oa : ProbComp α) :
    simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))
      (liftM oa : OracleComp (unifSpec + hashSpec (ShakeApi.primitives S base).core) α) = oa := by
  rw [unifFwdAnswerImpl, QueryImpl.passthrough_add, QueryImpl.simulateQ_add_liftM_left,
    QueryImpl.liftTarget_self, simulateQ_id']


theorem simulateQ_sha_romSignAt (sk : SecretKeyCore (ShakeApi.primitives S base).core) (addrnd : (ShakeApi.primitives S base).Y)
    (msg : List SLHDSA.Byte) :
    simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base))) (romSignAt S base sk addrnd msg) =
      (pure (GeneralScheme.signInternal S.vp (ShakeApi.primitives S base) msg sk addrnd) : ProbComp _) := by
  have h := congrArg (fun A => A.sign ⟨sk.pkSeed, sk.pkRoot⟩ sk msg)
    (rom_conformance S base (fun _ => (pure addrnd : ProbComp (ShakeApi.primitives S base).Y))
      ($ᵗ (ShakeApi.primitives S base).PkSeed))
  simp only [SignatureAlg.map_sign, internalAlg] at h
  change simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base))) (liftM (pure addrnd) >>= _) = _ at h
  rw [simulateQ_bind, simulateQ_sha_liftM, pure_bind, pure_bind] at h
  exact h

/-! ### The byte-level scheme in the random-oracle model -/


noncomputable def romSignPureBytes (m ctx skb : List SLHDSA.Byte) (addrnd : (ShakeApi.primitives S base).Y) :
    OracleComp (unifSpec + hashSpec (ShakeApi.primitives S base).core) (Option (List SLHDSA.Byte)) :=
  match decodeSecretKey (ShakeApi.codec S base) skb with
  | .ok sk =>
    match pureEncode (m, ctx) with
    | .ok m' => (fun σ => some (encodeSignature S.vp (ShakeApi.codec S base) σ)) <$> romSignAt S base sk addrnd m'
    | .error _ => pure none
  | .error _ => pure none


noncomputable def pureBytesRomScheme (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) :
    SignatureAlg (OracleComp (unifSpec + hashSpec (ShakeApi.primitives S base).core))
      (List SLHDSA.Byte × List SLHDSA.Byte) (List SLHDSA.Byte) (List SLHDSA.Byte)
      (Option (List SLHDSA.Byte)) where
  keygen := (fun ks => (encodePublicKey (ShakeApi.codec S base) ks.1, encodeSecretKey (ShakeApi.codec S base) ks.2)) <$>
    (romScheme (vp := S.vp) (ShakeApi.primitives S base).core (Equiv.refl _) optRand pkSeedDist).keygen
  sign pk sk mc :=
    if mc.2.length ≤ 255 then
      match decodePublicKey (ShakeApi.codec S base) pk with
      | .ok k => do
        let addrnd ← (optRand k : ProbComp (ShakeApi.primitives S base).Y)
        romSignPureBytes S base mc.1 mc.2 sk addrnd
      | .error _ => pure none
    else pure none
  verify pk mc sig := match sig with
    | some raw =>
      match decodeSignature S.vp (ShakeApi.codec S base) raw, decodePublicKey (ShakeApi.codec S base) pk with
      | .ok s, .ok k => (pureRomScheme S base optRand pkSeedDist).verify k mc (.ok s)
      | _, _ => pure false
    | none => pure false

theorem simulateQ_sha_romSignPureBytes (m ctx skb : List SLHDSA.Byte) (addrnd : (ShakeApi.primitives S base).Y) :
    simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base))) (romSignPureBytes S base m ctx skb addrnd) =
      (pure (byteSignPure S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base) m ctx skb addrnd) : ProbComp _) := by
  unfold romSignPureBytes byteSignPure
  cases decodeSecretKey (ShakeApi.codec S base) skb with
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
    (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) (pk : List SLHDSA.Byte)
    (mc : List SLHDSA.Byte × List SLHDSA.Byte) (sig : Option (List SLHDSA.Byte)) :
    simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))
        ((pureBytesRomScheme S base optRand pkSeedDist).verify pk mc sig) =
      (pureBytesAlg S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base) optRand pkSeedDist).verify pk mc sig := by
  obtain ⟨m, ctx⟩ := mc
  cases sig with
  | none => exact simulateQ_pure _ _
  | some raw =>
    change simulateQ _ (match decodeSignature S.vp (ShakeApi.codec S base) raw, decodePublicKey (ShakeApi.codec S base) pk with
      | .ok s, .ok k => (pureRomScheme S base optRand pkSeedDist).verify k (m, ctx) (.ok s)
      | _, _ => pure false) =
      pure (byteVerifyPure S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base) m raw ctx pk)
    unfold byteVerifyPure
    cases decodeSignature S.vp (ShakeApi.codec S base) raw with
    | error e => exact simulateQ_pure _ _
    | ok s =>
      cases decodePublicKey (ShakeApi.codec S base) pk with
      | error e => exact simulateQ_pure _ _
      | ok k =>
        have hv := congrArg (fun A => A.verify k (m, ctx) (.ok s))
          (pureRomScheme_instantiation S base optRand pkSeedDist)
        simp only [SignatureAlg.map_verify] at hv
        exact hv.trans (Reduction.externalAlg_verify_ok S.vp (ShakeApi.primitives S base) optRand pkSeedDist k m ctx s)

theorem simulateQ_sha_pureBytesRom_keygen
    (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) :
    simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))
        (pureBytesRomScheme S base optRand pkSeedDist).keygen =
      (pureBytesAlg S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base) optRand pkSeedDist).keygen := by
  have hk := congrArg SignatureAlg.keygen (rom_conformance S base optRand pkSeedDist)
  simp only [SignatureAlg.map_keygen] at hk
  have hd : (pureBytesRomScheme S base optRand pkSeedDist).keygen =
      (fun ks => (encodePublicKey (ShakeApi.codec S base) ks.1, encodeSecretKey (ShakeApi.codec S base) ks.2)) <$>
        (romScheme (vp := S.vp) (ShakeApi.primitives S base).core (Equiv.refl _) optRand pkSeedDist).keygen := rfl
  rw [hd, simulateQ_map, hk]
  simp only [internalAlg, pureBytesAlg, map_bind, map_pure]
  rfl

theorem simulateQ_sha_pureBytesRom_sign
    (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) (pk sk : List SLHDSA.Byte)
    (mc : List SLHDSA.Byte × List SLHDSA.Byte) :
    simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))
        ((pureBytesRomScheme S base optRand pkSeedDist).sign pk sk mc) =
      (pureBytesAlg S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base) optRand pkSeedDist).sign pk sk mc := by
  obtain ⟨m, ctx⟩ := mc
  simp only [pureBytesRomScheme, pureBytesAlg]
  split_ifs with hc
  · cases decodePublicKey (ShakeApi.codec S base) pk with
    | error e => exact simulateQ_pure _ _
    | ok k =>
      change simulateQ (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base))) (liftM (optRand k) >>= _) = _
      rw [simulateQ_bind, simulateQ_sha_liftM]
      exact bind_congr fun a => simulateQ_sha_romSignPureBytes S base m ctx sk a
  · exact simulateQ_pure _ _


theorem pureBytesRomScheme_instantiation
    (optRand : PublicKeyCore (ShakeApi.primitives S base).core → ProbComp (ShakeApi.primitives S base).Y)
    (pkSeedDist : ProbComp (ShakeApi.primitives S base).PkSeed) :
    (pureBytesRomScheme S base optRand pkSeedDist).map
        (simulateQ' (unifFwdAnswerImpl (romAnswer (ShakeApi.primitives S base)))) =
      pureBytesAlg S.vp (ShakeApi.primitives S base) (ShakeApi.codec S base) optRand pkSeedDist :=
  SignatureAlg.ext (simulateQ_sha_pureBytesRom_keygen S base optRand pkSeedDist)
    (funext fun pk => funext fun sk => funext fun mc =>
      simulateQ_sha_pureBytesRom_sign S base optRand pkSeedDist pk sk mc)
    (funext fun pk => funext fun mc => funext fun sig =>
      simulateQ_sha_pureBytesRom_verify S base optRand pkSeedDist pk mc sig)

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.pureBytesRomScheme_instantiation
