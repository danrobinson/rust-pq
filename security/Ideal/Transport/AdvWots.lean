import Ideal.Transport.AdvCommon
import Reduction.Open.Phase1Wots

/-!
# Core-invariance of the WOTS adversaries `rUd`, `rPre`, `rTcrT` at `Lazy.bWotsS A`
-/

open OracleComp OracleSpec SLHDSA SLHDSA.Security

namespace Ideal.Transport

open Reduction TweakableHash

set_option linter.unusedSectionVars false

section Wots

variable {vp : ValidatedParams} (prims : Primitives vp.params)
  (prf : prims.PkSeed → prims.SkSeed → Adrs → prims.Y)
  (pm : prims.SkPrf → prims.Y → List Byte → prims.Y)
variable [SampleableType prims.SkSeed] [SampleableType prims.SkPrf] [SampleableType prims.Y]
  [DecidableEq prims.Y] [DecidableEq prims.PkSeed] [DecidableEq prims.AdrsKey] [Inhabited prims.Y]

/-- The phase-2 signer of `bWotsS`. -/
theorem signFromHist_tr (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte) (R : prims.Y) :
    signFromHist (prims := setPrf prims prf pm) tbl hist (trPk _ prf pm pk) msg R =
      trSig _ prf pm (signFromHist (prims := prims) tbl hist pk msg R) := by
  unfold signFromHist
  dsimp only
  rw [trSig_mk]
  have hf := forsSignWithSecret_tr (m := Id) prims.core prf pm
    (fun a x => prims.F pk.pkSeed a x) (fun a l r => prims.H pk.pkSeed a l r)
    (fun a => secretOf vp prims tbl a) (digestParts pk R msg).md.toList
    (digestParts pk R msg).forsAdrs
  refine congrArg₂ (fun a b => (⟨R, a, b⟩ :
    GeneralScheme.SignatureCore vp (setPrfC prims.core prf pm))) ?_ ?_
  · kexact hf
  · rw [Vector.map_ofFn]
    krfl

/-- The WOTS-game answer extracted from a forgery. -/
theorem wotsAnswer_setPrf (tbl : SecretTable vp prims) (hist : List (WotsGame.Entry prims))
    (pk : PublicKeyCore prims.core) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) :
    wotsAnswer (prims := setPrf prims prf pm) tbl hist (trPk _ prf pm pk) msg
        (trSig _ prf pm sig) =
      wotsAnswer (prims := prims) tbl hist pk msg sig := by
  unfold wotsAnswer
  dsimp only
  rw [trSig_randomness, signFromHist_tr, digestParts_setPrf, wotsLayer?_setPrf]
  cases wotsLayer? pk (digestParts pk sig.randomness msg) sig
      (signFromHist tbl hist pk msg sig.randomness) with
  | none => krfl
  | some j =>
    dsimp only
    rw [trSig_hypertree, trSig_fors, trPk_pkSeed, forsPkFromSig_setPrf, layerMsg_setPrf,
      Vector.getElem_map, trXmss_wots]

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
/-- Second phase of the WOTS-game adversary. -/
theorem bWotsS_forge_setPrf (st : Open.WState vp prims) (pkSeed : prims.PkSeed) :
    (Lazy.bWotsS Aset).forge st pkSeed = (Lazy.bWotsS Abase).forge st pkSeed := by
  unfold Lazy.bWotsS Lazy.bWotsWith
  dsimp only
  have h := g2RunWith_bytesToTyped_tr prf pm codec optRand optRand' pkSeedDist hopt S
    ⟨pkSeed, st.2.2⟩ (signFromHist st.1 st.2.1 ⟨pkSeed, st.2.2⟩) _
    (fun m R => signFromHist_tr prims prf pm st.1 st.2.1 ⟨pkSeed, st.2.2⟩ m R)
  have hw := wotsAnswer_setPrf prims prf pm st.1 st.2.1 ⟨pkSeed, st.2.2⟩
  simp only [trPk_mk] at h hw
  rw [h, bind_map_left]
  simp only [hw]

/-! ### SM-UD -/

/-- First phase of the SM-UD adversary (independent of the forger). -/
theorem rUd_pick_setPrf :
    @Eq (OracleComp (Open.udSpecC prims.AdrsKey prims.Y) (Open.RState vp prims))
      (rUd (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)).pick
      (rUd pkSeedDist (Lazy.bWotsS Abase)).pick :=
  Open.wotsUd_phase1_hashfree_all ⟨prims.Thash, prims.Hmsg, prf, pm⟩ Aset Abase

include hopt in
/-- Second phase of the SM-UD adversary. -/
theorem rUd_distinguish_setPrf (st : Open.RState vp prims) (pkSeed : prims.PkSeed) :
    (rUd (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)).distinguish st pkSeed =
      (rUd pkSeedDist (Lazy.bWotsS Abase)).distinguish st pkSeed := by
  have h := bWotsS_forge_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S st.1 pkSeed
  kexact congrArg (fun x : ProbComp (ℕ × prims.Y × WotsSig vp.params prims.core) =>
    (x >>= fun r => pure (WotsGame.win pkSeed st.2 r.1 r.2.1 r.2.2) : ProbComp Bool)) h

theorem udAdv_mk_congr {ι PkSeed Tweak M M' Y : Type}
    (prob : SM_DT_UD_Problem ι PkSeed Tweak M M' Y) (σ : Type)
    (c c' : OracleComp (unifSpec + (SM_DT_UD_challengeSpec Tweak Y +
      collectionSpec prob.thColl)) σ)
    (f f' : σ → PkSeed → ProbComp Bool) (hc : c = c') (hf : ∀ s pk, f s pk = f' s pk) :
    (⟨σ, c, f⟩ : SM_DT_UD_Adversary prob) = ⟨σ, c', f'⟩ := by
  subst hc
  obtain rfl : f = f' := funext fun s => funext fun pk => hf s pk
  rfl

include hopt in
/-- **The SM-UD adversary over `setPrf prims prf pm` is the SM-UD adversary over `prims`.** -/
theorem rUd_setPrf :
    rUd (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset) =
      rUd pkSeedDist (Lazy.bWotsS Abase) := by
  have hc := rUd_pick_setPrf prims prf pm codec optRand optRand' pkSeedDist S
  have hf := rUd_distinguish_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S
  kexact udAdv_mk_congr (wotsUdProblem vp prims pkSeedDist) (Open.RState vp prims) _ _ _ _ hc hf

include hopt in
/-- The SM-UD experiments (both worlds) do not depend on `PRF`, `PRF_msg`. -/
theorem rUd_experiment_setPrf (world : SM_DT_UD_World) :
    SM_DT_UD_Experiment world (rUd (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)) =
      SM_DT_UD_Experiment world (rUd pkSeedDist (Lazy.bWotsS Abase)) :=
  congrArg (SM_DT_UD_Experiment world)
    (rUd_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

/-! ### SM-PRE -/

/-- First phase of the SM-PRE adversary (independent of the forger). -/
theorem rPre_choose_setPrf :
    @Eq (OracleComp (Open.preSpecC prims.AdrsKey prims.Y) (Open.RState vp prims))
      (rPre (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)).choose
      (rPre pkSeedDist (Lazy.bWotsS Abase)).choose :=
  Open.wotsPre_phase1_hashfree_all ⟨prims.Thash, prims.Hmsg, prf, pm⟩ Aset Abase

include hopt in
/-- Second phase of the SM-PRE adversary. -/
theorem rPre_invert_setPrf (st : Open.RState vp prims) (pkSeed : prims.PkSeed) :
    (rPre (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)).invert st pkSeed =
      (rPre pkSeedDist (Lazy.bWotsS Abase)).invert st pkSeed := by
  have h := bWotsS_forge_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S st.1 pkSeed
  kexact congrArg (fun x : ProbComp (ℕ × prims.Y × WotsSig vp.params prims.core) =>
    (x >>= fun r => pure (preAnswer pkSeed st.2 r.1 r.2.1 r.2.2) : ProbComp (ℕ × prims.Y))) h

theorem preAdv_mk_congr {ι PkSeed Tweak M M' Y : Type}
    (prob : SM_DT_PRE_Problem ι PkSeed Tweak M M' Y) (σ : Type)
    (c c' : OracleComp (unifSpec + (SM_DT_PRE_challengeSpec Tweak Y +
      collectionSpec prob.thColl)) σ)
    (f f' : σ → PkSeed → ProbComp (ℕ × M')) (hc : c = c') (hf : ∀ s pk, f s pk = f' s pk) :
    (⟨σ, c, f⟩ : SM_DT_PRE_Adversary prob) = ⟨σ, c', f'⟩ := by
  subst hc
  obtain rfl : f = f' := funext fun s => funext fun pk => hf s pk
  rfl

include hopt in
/-- **The SM-PRE adversary over `setPrf prims prf pm` is the SM-PRE adversary over `prims`.** -/
theorem rPre_setPrf :
    rPre (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset) =
      rPre pkSeedDist (Lazy.bWotsS Abase) := by
  have hc := rPre_choose_setPrf prims prf pm codec optRand optRand' pkSeedDist S
  have hf := rPre_invert_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S
  kexact preAdv_mk_congr (wotsPreProblem vp prims pkSeedDist) (Open.RState vp prims) _ _ _ _ hc hf

include hopt in
/-- The SM-PRE experiment does not depend on `PRF`, `PRF_msg`. -/
theorem rPre_experiment_setPrf :
    SM_DT_PRE_Experiment (rPre (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)) =
      SM_DT_PRE_Experiment (rPre pkSeedDist (Lazy.bWotsS Abase)) :=
  congrArg SM_DT_PRE_Experiment
    (rPre_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

/-! ### SM-TCR (tight cap) -/

/-- First phase of the chain SM-TCR adversary (independent of the forger). -/
theorem rTcrT_choose_setPrf :
    @Eq (OracleComp (Open.tcrSpecC prims.AdrsKey prims.Y) (Open.RState vp prims))
      (rTcrT (vp := vp) (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)).choose
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS Abase)).choose :=
  Open.wotsTcrT_phase1_hashfree_all ⟨prims.Thash, prims.Hmsg, prf, pm⟩ Aset Abase

include hopt in
/-- Second phase of the chain SM-TCR adversary. -/
theorem rTcrT_forge_setPrf (st : Open.RState vp prims) (pkSeed : prims.PkSeed) :
    (rTcrT (vp := vp) (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)).forge st
        pkSeed =
      (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS Abase)).forge st pkSeed := by
  have h := bWotsS_forge_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S st.1 pkSeed
  kexact congrArg (fun x : ProbComp (ℕ × prims.Y × WotsSig vp.params prims.core) =>
    (x >>= fun r => pure (tcrAnswer pkSeed st.2 r.1 r.2.1 r.2.2) : ProbComp (ℕ × prims.Y))) h

theorem wtcrAdv_mk_congr {ι PkSeed Tweak M Y : Type}
    (prob : SM_DT_TCR_Problem ι PkSeed Tweak M Y) (σ : Type)
    (c c' : OracleComp (unifSpec + (SM_DT_TCR_challengeSpec Tweak M Y +
      collectionSpec prob.thColl)) σ)
    (f f' : σ → PkSeed → ProbComp (ℕ × M)) (hc : c = c') (hf : ∀ s pk, f s pk = f' s pk) :
    (⟨σ, c, f⟩ : SM_DT_TCR_Adversary prob) = ⟨σ, c', f'⟩ := by
  subst hc
  obtain rfl : f = f' := funext fun s => funext fun pk => hf s pk
  rfl

include hopt in
/-- **The chain SM-TCR adversary over `setPrf prims prf pm` is the one over `prims`.** -/
theorem rTcrT_setPrf :
    rTcrT (vp := vp) (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset) =
      rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS Abase) := by
  have hc := rTcrT_choose_setPrf prims prf pm codec optRand optRand' pkSeedDist S
  have hf := rTcrT_forge_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S
  kexact wtcrAdv_mk_congr (wotsTcrProblemT vp prims pkSeedDist) (Open.RState vp prims) _ _ _ _
    hc hf

include hopt in
/-- The chain SM-TCR experiment does not depend on `PRF`, `PRF_msg`. -/
theorem rTcrT_experiment_setPrf :
    SM_DT_TCR_Experiment
        (rTcrT (vp := vp) (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS Aset)) =
      SM_DT_TCR_Experiment (rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS Abase)) :=
  congrArg SM_DT_TCR_Experiment
    (rTcrT_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S)

/-! ### The same at the strong (SUF) forger wrapper -/

set_option quotPrecheck false in
local notation "AbaseS" =>
  (bytesToTypedS (prims := prims) (codec := codec) (optRand := optRand)
    (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary

set_option quotPrecheck false in
local notation "AsetS" =>
  (bytesToTypedS (prims := setPrf prims prf pm) (codec := trCodec _ prf pm codec)
    (optRand := optRand') (pkSeedDist := pkSeedDist) ⟨S⟩).toUnforgeableAdversary

include hopt in
theorem rUd_setPrf_S :
    rUd (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS AsetS) =
      rUd pkSeedDist (Lazy.bWotsS AbaseS) :=
  rUd_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

include hopt in
theorem rPre_setPrf_S :
    rPre (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS AsetS) =
      rPre pkSeedDist (Lazy.bWotsS AbaseS) :=
  rPre_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

include hopt in
theorem rTcrT_setPrf_S :
    rTcrT (vp := vp) (prims := setPrf prims prf pm) pkSeedDist (Lazy.bWotsS AsetS) =
      rTcrT (vp := vp) pkSeedDist (Lazy.bWotsS AbaseS) :=
  rTcrT_setPrf prims prf pm codec optRand optRand' hopt pkSeedDist S

end Wots

end Ideal.Transport

section AxiomCheck
open Ideal.Transport
#print axioms signFromHist_tr
#print axioms wotsAnswer_setPrf
#print axioms bWotsS_forge_setPrf
#print axioms rUd_setPrf
#print axioms rPre_setPrf
#print axioms rTcrT_setPrf
#print axioms rUd_experiment_setPrf
#print axioms rPre_experiment_setPrf
#print axioms rTcrT_experiment_setPrf
#print axioms rUd_setPrf_S
#print axioms rPre_setPrf_S
#print axioms rTcrT_setPrf_S
end AxiomCheck
