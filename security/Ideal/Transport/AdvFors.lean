import Ideal.Transport.AdvCommon
import Reduction.Open.Phase1Fors

/-!
# Core-invariance of the FORS adversaries `toDspr (Lazy.bOpenPreS A)`, `toTcr (Lazy.bOpenPreS A)`
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction TweakableHash

set_option linter.unusedSectionVars false

section Fors

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

theorem forsSigFromImages_setPrf (pkSeed : prims.PkSeed) (ys : List prims.Y) (md : List Byte)
    (adrs : Adrs) :
    forsSigFromImages (vp := vp) (prims := setPrf prims prf pm) pkSeed ys md adrs =
      (forsSigFromImages (vp := vp) (prims := prims) pkSeed ys md adrs).map
        (trFors _ prf pm) := by
  unfold forsSigFromImages
  exact forsSignWithSecret_tr (m := Id) prims.core prf pm _ _ _ md adrs

theorem opHt_setPrf (T : SecretTable vp prims) (pkSeed : prims.PkSeed) (m0 : prims.Y)
    (parts : DigestParts vp.params) :
    opHt (prims := setPrf prims prf pm) T pkSeed m0 parts =
      (opHt (prims := prims) T pkSeed m0 parts).map (trXmss _ prf pm) := by
  unfold opHt
  exact signWithSecret_tr (m := Id) prims.core prf pm _ _ _ _ m0 parts

theorem bind_ofFnM_tr {m : Type → Type} [Monad m] [LawfulMonad m] {α α' β β' : Type} {n : ℕ}
    (g' : Fin n → m α') (g : Fin n → m α) (f : α → α') (k' : Vector α' n → m β')
    (k : Vector α n → m β) (F : β → β') (hg : ∀ i, g' i = f <$> g i)
    (hk : ∀ v, k' (v.map f) = F <$> k v) :
    (Vector.ofFnM g' >>= k') = F <$> (Vector.ofFnM g >>= k) := by
  rw [funext hg, vector_ofFnM_map, bind_map_left, map_bind]
  exact bind_congr fun v => hk v

theorem openSign_setPrf (pk : PublicKeyCore prims.core) (tbl : SecretTable vp prims)
    (ys : List prims.Y) (m : List Byte) (R : prims.Y) :
    Reduction.openSign (prims := setPrf prims prf pm) (trPk _ prf pm pk) tbl ys m R =
      trSig _ prf pm <$> Reduction.openSign (prims := prims) pk tbl ys m R := by
  unfold Reduction.openSign
  refine bind_ofFnM_tr _ _ (trFors _ prf pm) _ _ _ (fun i => ?_) (fun v => ?_)
  · simp only [trPk_pkSeed, digestParts_setPrf prims prf pm,
      forsSigFromImages_setPrf prims prf pm, Vector.getElem_map, trFors_auth, map_bind, map_pure,
      trFors_mk]
    krfl
  · simp only [trPk_pkSeed, digestParts_setPrf prims prf pm, map_pure, trSig_mk]
    rw [forsPkFromSig_setPrf, opHt_setPrf]

theorem openPreAnswer_setPrf (pk : PublicKeyCore prims.core) (ys : List prims.Y)
    (log : G2Log prims) (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    openPreAnswer (prims := setPrf prims prf pm) (trPk _ prf pm pk) ys log msg
        (trSig _ prf pm sig) =
      openPreAnswer (prims := prims) pk ys log msg sig := by
  unfold openPreAnswer
  simp only [trSig_randomness, trSig_fors, Vector.getElem_map, trFors_sk, trPk_pkSeed,
    digestParts_setPrf prims prf pm]
  krfl

variable (codec : CoreWireCodec vp.params prims.core)
  (optRand : PublicKeyCore prims.core → ProbComp prims.Y)
  (optRand' : PublicKeyCore (setPrfC prims.core prf pm) → ProbComp prims.Y)
  (hopt : ∀ pk, optRand' (trPk _ prf pm pk) = optRand pk)
  (pkSeedDist : ProbComp prims.PkSeed)
  (S : List Byte → OracleComp (unifSpec + (List Byte →ₒ List Byte)) (List Byte × List Byte))

set_option quotPrecheck false in
/-- The typed forger over `prims` built from the byte-level main `S`. -/
local notation "Abase" =>
  (bytesToTyped (prims := prims) (codec := codec) (optRand := optRand) (pkSeedDist := pkSeedDist)
    ⟨S⟩)

set_option quotPrecheck false in
/-- The typed forger over `setPrf prims prf pm` built from the same byte-level main `S`. -/
local notation "Aset" =>
  (bytesToTyped (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
    (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩)

include hopt in
/-- Second phase of the OpenPRE adversary. -/
theorem bOpenPreS_find_setPrf (tbl : SecretTable vp prims) (pkSeed : prims.PkSeed)
    (ys : List prims.Y) :
    (Lazy.bOpenPreS Aset).find tbl pkSeed ys = (Lazy.bOpenPreS Abase).find tbl pkSeed ys := by
  unfold Lazy.bOpenPreS bOpenPreWith
  dsimp only
  rw [idealPk_setPrf]
  rw [runForgerLog_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist hopt S _ _ _ _
    (fun m R => openSign_setPrf prims prf pm _ tbl ys m R)]
  rw [bind_map_left]
  have hr : (lazyRandomizerLift (prims := setPrf prims prf pm) :
      G2Log prims → List Byte → prims.Y → OracleComp (openSpecY prims) prims.Y) =
      lazyRandomizerLift (prims := prims) := by krfl
  rw [hr]
  refine bind_congr (m := OracleComp (openSpecY prims)) fun z => ?_
  rw [openPreAnswer_setPrf]

/-- First phase of the TCR adversary (does not depend on the forger at all). -/
theorem toTcr_choose_setPrf :
    (toTcr (Lazy.bOpenPreS Aset)).choose = (toTcr (Lazy.bOpenPreS Abase)).choose :=
  Open.forsTcr_phase1_withHash ⟨prims.Thash, prims.Hmsg, prf, pm⟩ Aset Abase

/-- First phase of the DSPR adversary. -/
theorem toDspr_choose_setPrf :
    (toDspr (Lazy.bOpenPreS Aset)).choose = (toDspr (Lazy.bOpenPreS Abase)).choose :=
  Open.forsDspr_phase1_withHash ⟨prims.Thash, prims.Hmsg, prf, pm⟩ Aset Abase

include hopt in
/-- Second phase of the TCR adversary. -/
theorem toTcr_forge_setPrf (st : Open.ForsP1State vp prims) (pkSeed : prims.PkSeed) :
    (toTcr (Lazy.bOpenPreS Aset)).forge st pkSeed =
      (toTcr (Lazy.bOpenPreS Abase)).forge st pkSeed := by
  unfold toTcr SM_DT_OpenPRE_SourceFinalValidity.toTCR
  dsimp only
  rw [bOpenPreS_find_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S]

include hopt in
/-- Second phase of the DSPR adversary. -/
theorem toDspr_guess_setPrf (st : Open.ForsP1State vp prims) (pkSeed : prims.PkSeed) :
    (toDspr (Lazy.bOpenPreS Aset)).guess st pkSeed =
      (toDspr (Lazy.bOpenPreS Abase)).guess st pkSeed := by
  unfold toDspr SM_DT_OpenPRE_SourceFinalValidity.toDSPR
  dsimp only
  rw [bOpenPreS_find_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S]

theorem tcrAdv_mk_congr {ι PkSeed Tweak M Y : Type}
    {prob : SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y} {σ : Type}
    {c c' : OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)) σ}
    {f f' : σ → PkSeed → ProbComp (ℕ × M)} (hc : c = c') (hf : ∀ s pk, f s pk = f' s pk) :
    (⟨σ, c, f⟩ : SM_DT_TCR_SourceFinalValidity.Adversary prob) = ⟨σ, c', f'⟩ := by
  subst hc
  obtain rfl : f = f' := funext fun s => funext fun pk => hf s pk
  rfl

theorem dsprAdv_mk_congr {ι PkSeed Tweak M Y : Type}
    {prob : SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y} {σ : Type}
    {c c' : OracleComp (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)) σ}
    {f f' : σ → PkSeed → ProbComp (ℕ × Bool)} (hc : c = c') (hf : ∀ s pk, f s pk = f' s pk) :
    (⟨σ, c, f⟩ : SM_DT_DSPR_SourceFinalValidity.Adversary prob) = ⟨σ, c', f'⟩ := by
  subst hc
  obtain rfl : f = f' := funext fun s => funext fun pk => hf s pk
  rfl

include hopt in
/-- **The TCR adversary over `setPrf prims prf pm` is the TCR adversary over `prims`.** -/
theorem toTcr_setPrf :
    toTcr (Lazy.bOpenPreS Aset) = toTcr (Lazy.bOpenPreS Abase) :=
  tcrAdv_mk_congr (σ := Open.ForsP1State vp prims)
    (toTcr_choose_setPrf prims prf pm codec optRand optRand' pkSeedDist S)
    (toTcr_forge_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- **The DSPR adversary over `setPrf prims prf pm` is the DSPR adversary over `prims`.** -/
theorem toDspr_setPrf :
    toDspr (Lazy.bOpenPreS Aset) = toDspr (Lazy.bOpenPreS Abase) :=
  dsprAdv_mk_congr (σ := Open.ForsP1State vp prims)
    (toDspr_choose_setPrf prims prf pm codec optRand optRand' pkSeedDist S)
    (toDspr_guess_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- The same for the strong (SUF) forger wrapper. -/
theorem toTcr_setPrf_S :
    toTcr (Lazy.bOpenPreS (bytesToTypedS (prims := setPrf prims prf pm)
        (codec := trCodec _ prf pm codec) (optRand := optRand') (pkSeedDist := pkSeedDist)
        ⟨S⟩).toUnforgeableAdversary) =
      toTcr (Lazy.bOpenPreS (bytesToTypedS (prims := prims) (codec := codec) (optRand := optRand)
        (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary) :=
  toTcr_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

include hopt in
theorem toDspr_setPrf_S :
    toDspr (Lazy.bOpenPreS (bytesToTypedS (prims := setPrf prims prf pm)
        (codec := trCodec _ prf pm codec) (optRand := optRand') (pkSeedDist := pkSeedDist)
        ⟨S⟩).toUnforgeableAdversary) =
      toDspr (Lazy.bOpenPreS (bytesToTypedS (prims := prims) (codec := codec) (optRand := optRand)
        (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary) :=
  toDspr_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

include hopt in
/-- The SM-DT-TCR experiment of the FORS TCR adversary does not depend on `PRF`, `PRF_msg`. -/
theorem toTcr_experiment_setPrf :
    SM_DT_TCR_SourceFinalValidity.experiment (toTcr (Lazy.bOpenPreS Aset)) =
      SM_DT_TCR_SourceFinalValidity.experiment (toTcr (Lazy.bOpenPreS Abase)) :=
  congrArg SM_DT_TCR_SourceFinalValidity.experiment
    (toTcr_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- The SM-DT-DSPR experiment of the FORS DSPR adversary does not depend on `PRF`, `PRF_msg`. -/
theorem toDspr_experiment_setPrf [Fintype prims.Y] :
    SM_DT_DSPR_SourceFinalValidity.experiment (toDspr (Lazy.bOpenPreS Aset)) =
      SM_DT_DSPR_SourceFinalValidity.experiment (toDspr (Lazy.bOpenPreS Abase)) :=
  congrArg SM_DT_DSPR_SourceFinalValidity.experiment
    (toDspr_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

include hopt in
/-- The `SPprob` baseline experiment likewise. -/
theorem toDspr_spExperiment_setPrf [Fintype prims.Y] :
    SM_DT_DSPR_SourceFinalValidity.spExperiment (toDspr (Lazy.bOpenPreS Aset)) =
      SM_DT_DSPR_SourceFinalValidity.spExperiment (toDspr (Lazy.bOpenPreS Abase)) :=
  congrArg SM_DT_DSPR_SourceFinalValidity.spExperiment
    (toDspr_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

end Fors

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms openSign_setPrf
#print axioms openPreAnswer_setPrf
#print axioms bOpenPreS_find_setPrf
#print axioms toTcr_setPrf
#print axioms toDspr_setPrf
#print axioms toTcr_setPrf_S
#print axioms toDspr_setPrf_S
#print axioms toTcr_experiment_setPrf
#print axioms toDspr_experiment_setPrf
#print axioms toDspr_spExperiment_setPrf
end AxiomCheck
