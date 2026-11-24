import Integration.SlhDsaShakePermutationHonestBudget

namespace Reduction.ShakePermutation.Honest
open SLHDSA SLHDSA.Security MLink OracleComp OracleSpec Ideal.Transport
open ShakeApi (Xof)
set_option allowUnsafeReducibility true in
attribute [local reducible] ShakeSecurity.primitives
variable (S : Sha2Set) (N : ℕ) (b c : Xof S)
local notation "Pb" => ShakeApi.primitives S b
local notation "Pc" => ShakeApi.primitives S c
local notation "Raw" => OracleComp (RawSpec S N)
local notation "ROM" => unifSpec + hashSpec (Primitives.core (ShakeApi.primitives S b))

@[reducible] private def bridgeInst : HasQuery (publicHashSpec (Pb).core) Raw := ⟨fun q => rawHash S N b (.inl q)⟩

local instance : HasQuery (publicHashSpec (Pb).core) Raw := bridgeInst S N b

private def bridgeHom : HasQuery.QueryHom (publicHashSpec (Pb).core) (OracleComp ROM) Raw where
  toMonadHom := simulateQ' (rawImpl S N b)
  map_query' q := by simp [rawImpl]

private def secret (pk sk : S.Node) (a : Adrs) : Raw S.Node :=
  prefixBytes _ <$> readRaw S N (pk.toList ++ a.toVector.toList ++ sk.toList)

private theorem secret_eq (pk sk : S.Node) (a : Adrs) : simulateQ (rawImpl S N b)
    (oracleSecret (Pb).core (Equiv.refl _) pk sk a) = secret S N pk sk a := by
  change simulateQ _ (liftM ((ROM).query (.inr (.inl (.thash pk a.toVector [sk]))))) = _
  rw [simulateQ_spec_query]
  simp [rawImpl,rawHash,secret]

private theorem keyCore_eq (pk sk : S.Node) :
    simulateQ (rawImpl S N b) (GeneralScheme.keygenInternalWithSecretM (vp := S.vp) (Pb).core
      (oracleSecret (Pb).core (Equiv.refl _) pk sk) pk) =
    @GeneralScheme.keygenInternalWithSecretM S.vp (Pb).core Raw _ (bridgeInst S N b)
      (secret S N pk sk) pk :=
  @GeneralScheme.keygenInternalWithSecretM_natural S.vp (Pb).core (OracleComp ROM) Raw _ _ _ _ _ (bridgeInst S N b)
    (bridgeHom S N b) (oracleSecret (Pb).core (Equiv.refl _) pk sk) (secret S N pk sk) (fun a _ => secret_eq S N b pk sk a) pk

private theorem signCore_eq (sk : SecretKeyCore (Pb).core) (r : S.Node) (m : List SLHDSA.Byte) :
    simulateQ (rawImpl S N b) (GeneralScheme.signInternalWithSecretRandomizerM (vp := S.vp) (Pb).core
      (oracleSecret (Pb).core (Equiv.refl _) sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r) =
    @GeneralScheme.signInternalWithSecretRandomizerM S.vp (Pb).core Raw _ (bridgeInst S N b)
      (secret S N sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r :=
  @GeneralScheme.signInternalWithSecretRandomizerM_natural S.vp (Pb).core (OracleComp ROM) Raw _ _ _ _ _ (bridgeInst S N b)
    (bridgeHom S N b) (oracleSecret (Pb).core (Equiv.refl _) sk.pkSeed sk.skSeed)
      (secret S N sk.pkSeed sk.skSeed) (fun a _ => secret_eq S N b sk.pkSeed sk.skSeed a) m sk.pkSeed sk.pkRoot r

private theorem verifyCore_eq (pk : PublicKeyCore (Pb).core) (s : GeneralScheme.SignatureCore S.vp (Pb).core)
    (m : List SLHDSA.Byte) :
    simulateQ (rawImpl S N b) (GeneralScheme.verifyInternalM S.vp (Pb).core m s pk) =
    @GeneralScheme.verifyInternalM S.vp (Pb).core Raw _ (bridgeInst S N b) _ m s pk :=
  @GeneralScheme.verifyInternalM_natural S.vp (Pb).core (OracleComp ROM) Raw _ _ _ _ _ (bridgeInst S N b) _ (bridgeHom S N b) _ _ _

private theorem uniform {α : Type} (u : ProbComp α) :
    simulateQ (rawImpl S N b) (liftM u : OracleComp ROM α) = (liftM u : Raw α) := by
  rw [rawImpl,QueryImpl.simulateQ_add_liftM_left]
  induction u using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih => simp [ih]; rfl


private def skMap (sk : SecretKeyCore (Pb).core) : SecretKeyCore (Pc).core :=
  ⟨sk.skSeed,sk.skPrf,sk.pkSeed,sk.pkRoot⟩

private theorem decPk (xs : List SLHDSA.Byte) :
    decodePublicKey (ShakeApi.codec S c) xs =
      (trPk (Pb).core (Pc).PRF (Pc).PRFmsg) <$> decodePublicKey (ShakeApi.codec S b) xs := by
  unfold decodePublicKey WireCodec.decode
  cases decodeExact S.vp.params.publicKeyBytes xs with
  | error e => rfl
  | ok x => rfl

private theorem decSk (xs : List SLHDSA.Byte) :
    decodeSecretKey (ShakeApi.codec S c) xs = skMap S b c <$> decodeSecretKey (ShakeApi.codec S b) xs := by
  unfold decodeSecretKey WireCodec.decode
  cases decodeExact S.vp.params.secretKeyBytes xs with
  | error e => rfl
  | ok x => rfl

private theorem decSig (xs : List SLHDSA.Byte) :
    decodeSignature S.vp (ShakeApi.codec S c) xs =
      (trSig (Pb).core (Pc).PRF (Pc).PRFmsg) <$> decodeSignature S.vp (ShakeApi.codec S b) xs :=
  by kexact decodeSignature_tr S.vp (Pb).core (Pc).PRF (Pc).PRFmsg (ShakeApi.codec S b) xs

private theorem encSig (s : GeneralScheme.SignatureCore S.vp (Pb).core) :
    encodeSignature S.vp (ShakeApi.codec S c) (trSig (Pb).core (Pc).PRF (Pc).PRFmsg s) =
      encodeSignature S.vp (ShakeApi.codec S b) s :=
  by kexact encodeSignature_tr S.vp (Pb).core (Pc).PRF (Pc).PRFmsg (ShakeApi.codec S b) s

private theorem key_tr (pk sk : S.Node) :
    simulateQ (rawImpl S N c) (GeneralScheme.keygenInternalWithSecretM (vp := S.vp) (Pc).core
      (oracleSecret (Pc).core (Equiv.refl _) pk sk) pk) =
    simulateQ (rawImpl S N b) (GeneralScheme.keygenInternalWithSecretM (vp := S.vp) (Pb).core
      (oracleSecret (Pb).core (Equiv.refl _) pk sk) pk) := by
  rw [keyCore_eq,keyCore_eq]
  qm_kernel_rfl

private theorem sign_tr (sk : SecretKeyCore (Pb).core) (r : S.Node) (m : List SLHDSA.Byte) :
    simulateQ (rawImpl S N c) (GeneralScheme.signInternalWithSecretRandomizerM (vp := S.vp) (Pc).core
      (oracleSecret (Pc).core (Equiv.refl _) sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r) =
      (trSig (Pb).core (Pc).PRF (Pc).PRFmsg) <$>
    simulateQ (rawImpl S N b) (GeneralScheme.signInternalWithSecretRandomizerM (vp := S.vp) (Pb).core
      (oracleSecret (Pb).core (Equiv.refl _) sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r) := by
  rw [signCore_eq S N b sk]
  conv_lhs => change simulateQ _ (GeneralScheme.signInternalWithSecretRandomizerM (vp := S.vp) (Pc).core
    (oracleSecret (Pc).core (Equiv.refl _) (skMap S b c sk).pkSeed (skMap S b c sk).skSeed) m
    (skMap S b c sk).pkSeed (skMap S b c sk).pkRoot r)
  rw [signCore_eq S N c (skMap S b c sk)]
  exact signInternalWithSecretRandomizerM_tr (Pb).core (Pc).PRF (Pc).PRFmsg
    (bridgeInst S N b) (bridgeInst S N c) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (secret S N sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot r

private theorem verify_tr (pk : PublicKeyCore (Pb).core) (s : GeneralScheme.SignatureCore S.vp (Pb).core)
    (m : List SLHDSA.Byte) :
    simulateQ (rawImpl S N c) (GeneralScheme.verifyInternalM S.vp (Pc).core m
      (trSig (Pb).core (Pc).PRF (Pc).PRFmsg s) (trPk (Pb).core (Pc).PRF (Pc).PRFmsg pk)) =
    simulateQ (rawImpl S N b) (GeneralScheme.verifyInternalM S.vp (Pb).core m s pk) := by
  rw [verifyCore_eq,verifyCore_eq]
  exact verifyInternalM_setPrf (Pb).core (Pc).PRF (Pc).PRFmsg
    (bridgeInst S N b) (bridgeInst S N c) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) m s pk


private theorem encSignAt (sk : SecretKeyCore (Pb).core) (r : S.Node) (m : List SLHDSA.Byte) :
    simulateQ (rawImpl S N c) ((fun s => some (encodeSignature S.vp (ShakeApi.codec S c) s)) <$>
      romSignAt S c (skMap S b c sk) r m) =
    simulateQ (rawImpl S N b) ((fun s => some (encodeSignature S.vp (ShakeApi.codec S b) s)) <$>
      romSignAt S b sk r m) := by
  simp only [romSignAt,map_bind,simulateQ_bind,simulateQ_map]
  apply bind_congr
  intro R
  change _ <$> simulateQ (rawImpl S N c) (GeneralScheme.signInternalWithSecretRandomizerM (vp := S.vp) (Pc).core
    (oracleSecret (Pc).core (Equiv.refl _) sk.pkSeed sk.skSeed) m sk.pkSeed sk.pkRoot R) = _
  rw [sign_tr S N b c sk,Functor.map_map]
  congr 1
  funext s
  exact congrArg some (encSig S b c s)

private theorem encSign (m ctx sk : List SLHDSA.Byte) (r : S.Node) :
    simulateQ (rawImpl S N c) (romSignPureBytes S c m ctx sk r) =
    simulateQ (rawImpl S N b) (romSignPureBytes S b m ctx sk r) := by
  unfold romSignPureBytes
  rw [decSk S b c]
  cases decodeSecretKey (ShakeApi.codec S b) sk with
  | error e => simp [simulateQ_pure]
  | ok k =>
    cases pureEncode (m,ctx) with
    | error e => simp
    | ok m' => exact encSignAt S N b c k r m'

variable (rand : S.Node → S.Node → ProbComp S.Node) (seeds : ProbComp S.Node)

theorem rawScheme_independent : rawScheme S N c rand seeds = rawScheme S N b rand seeds := by
  apply SignatureAlg.ext
  · simp only [rawScheme,SignatureAlg.map_keygen,pureBytesRomScheme,romScheme_keygen,
      map_bind,map_pure,simulateQ_bind,simulateQ_pure,simulateQ']
    refine bind_congr_k ((uniform S N c seeds).trans (uniform S N b seeds).symm) fun pk => ?_
    refine bind_congr_k ((uniform S N c ($ᵗ S.Node)).trans (uniform S N b ($ᵗ S.Node)).symm) fun sk => ?_
    refine bind_congr_k ((uniform S N c ($ᵗ S.Node)).trans (uniform S N b ($ᵗ S.Node)).symm) fun pr => ?_
    rw [key_tr S N b c pk sk]
    rfl
  · funext pk sk mc
    simp only [rawScheme,SignatureAlg.map_sign,pureBytesRomScheme,simulateQ']
    split
    · rw [decPk S b c]
      cases decodePublicKey (ShakeApi.codec S b) pk with
      | error e => simp
      | ok k =>
        simp only [Functor.map,Except.map,simulateQ_bind]
        exact bind_congr_k ((uniform S N c (rand k.pkSeed k.pkRoot)).trans (uniform S N b (rand k.pkSeed k.pkRoot)).symm)
          (fun r => encSign S N b c mc.1 mc.2 sk r)
    · simp
  · funext pk mc sig
    simp only [rawScheme,SignatureAlg.map_verify,pureBytesRomScheme,simulateQ']
    cases sig with
    | none => simp
    | some raw =>
      dsimp only
      rw [decSig S b c,decPk S b c]
      cases decodeSignature S.vp (ShakeApi.codec S b) raw with
      | error e => simp
      | ok s =>
        cases decodePublicKey (ShakeApi.codec S b) pk with
        | error e => simp
        | ok k =>
          simp only [Functor.map,Except.map,pureRomScheme,E2E.GuardedRom.scheme]
          cases pureEncode mc with
          | error e => simp
          | ok m => exact verify_tr S N b c k s m

theorem runRaw (H : ShakeApi.RawTable S N) :
    (rawScheme S N b rand seeds).map (simulateQ' (Compression.SkGame.answerImpl H)) =
      ShakeApi.scheme S rand seeds (ShakeApi.extend H) := by
  rw [rawScheme_independent S N (ShakeApi.extend H) b,runRaw_self]

end Reduction.ShakePermutation.Honest
#print axioms Reduction.ShakePermutation.Honest.rawScheme_independent
