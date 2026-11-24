import MIdeal.Wots128fFixed

/-! The concrete WOTS experiments of the SHA2-128f byte-forger reduction agree
with the ideal-compression experiments for the fixed two-phase adversaries. -/

namespace MIdeal.Wots128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport TweakableHash ENNReal
open Ideal.Realize.Wots Reduction.Resources2 Reduction.Lazy
open Class128f (vp P)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
attribute [local irreducible] preChoose tcrChoose udChoose
section First
variable (seeds : ProbComp (Bytes 16)) (ref : CompressionTables)
set_option maxRecDepth 3000 in
set_option maxHeartbeats 300000 in
theorem pre_experiment (c : CF St Blk) :
    let g : CompressionTables := (c,ref.2)
    let D := preAdv rand A seeds ref
    @SM_DT_PRE_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)
      _ _ sampY128 _ (rPre (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))) =
      SM_DT_PRE_Experiment (D.inst id Function.injective_id c) := by
  let g : CompressionTables := (c,ref.2)
  let C := rPre (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))
  let D := preAdv rand A seeds ref
  let B := D.inst id Function.injective_id c
  have hc : C.choose = B.choose := by
    have h := instImpl_emb (α := PhaseState) c (preChoose rand A seeds ref)
    have both := (pre_choose_at rand A seeds ref g).trans h.symm
    dsimp only [C,B,D,preAdv,PreAdv.inst,preChoose] at both ⊢
    kexact both
  have hf (st : PhaseState) (pk : Bytes 16) : C.invert st pk = B.invert st pk :=
    (pre_fixed rand A ref.1 g seeds st pk).symm
  have eq : C = (⟨PhaseState,B.choose,B.invert⟩ : SM_DT_PRE_Adversary (wotsPreProblem vp (P g) seeds)) := by
    kexact preAdv_mk_congr (wotsPreProblem vp (P g) seeds) PhaseState _ _ _ _ hc hf
  apply (congrArg (SM_DT_PRE_Experiment ) eq).trans
  have h := SM_DT_PRE_Experiment_congr (iT := inferInstanceAs (DecidableEq (Bytes 22))) (iT' := inferInstanceAs (DecidableEq (Bytes 22)))
    (iY := inferInstanceAs (DecidableEq (Bytes 16))) (iY' := inferInstanceAs (DecidableEq (Bytes 16))) (iS := sampY128) seeds
    (fun pk tw x => (P g).Thash pk tw [x]) ((Hash128f.chainFamily seeds).evalT c) id Function.injective_id Function.injective_id
    (fun _ : Unit => List (Bytes 16)) (fun _ => (P g).Thash) ((Hash128f.chainFamily seeds).evalC c)
    (wotsChainTargets vp) (by funext pk tw x; exact Hash128f.shape g pk tw [x])
    (by funext _ pk tw xs; exact Hash128f.shape g pk tw xs) PhaseState B.choose B.invert
  dsimp only [Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T, THFam.preProb, THFam.udProb,
    THFam.tcrProb, THFam.coll, wotsPreProblem, wotsUdProblem, wotsTcrProblemT] at h ⊢
  kexact h

set_option maxRecDepth 3000 in
set_option maxHeartbeats 300000 in
theorem tcr_experiment (c : CF St Blk) :
    let g : CompressionTables := (c,ref.2)
    let D := tcrAdv rand A seeds ref
    @SM_DT_TCR_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16)
      _ _ _ _ (rTcrT (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))) =
      SM_DT_TCR_Experiment (D.inst c) := by
  let g : CompressionTables := (c,ref.2)
  let C := rTcrT (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))
  let D := tcrAdv rand A seeds ref
  let B := D.inst c
  have hc : C.choose = B.choose := by
    have h := instImpl_emb (α := PhaseState) c (tcrChoose rand A seeds ref)
    have both := (tcr_choose_at rand A seeds ref g).trans h.symm
    dsimp only [C,B,D,tcrAdv,TcrAdv.inst,tcrChoose] at both ⊢
    kexact both
  have hf (st : PhaseState) (pk : Bytes 16) : C.forge st pk = B.forge st pk :=
    (tcr_fixed rand A ref.1 g seeds st pk).symm
  have eq : C = (⟨PhaseState,B.choose,B.forge⟩ : SM_DT_TCR_Adversary (wotsTcrProblemT vp (P g) seeds)) := by
    kexact wtcrAdv_mk_congr (wotsTcrProblemT vp (P g) seeds) PhaseState _ _ _ _ hc hf
  apply (congrArg (SM_DT_TCR_Experiment ) eq).trans
  have h := SM_DT_TCR_Experiment_congr (iT := inferInstanceAs (DecidableEq (Bytes 22))) (iT' := inferInstanceAs (DecidableEq (Bytes 22)))
    (iM := inferInstanceAs (DecidableEq (Bytes 16))) (iM' := inferInstanceAs (DecidableEq (Bytes 16))) (iY := inferInstanceAs (DecidableEq (Bytes 16))) (iY' := inferInstanceAs (DecidableEq (Bytes 16))) seeds
    (fun pk tw x => (P g).Thash pk tw [x]) ((Hash128f.FWots128T seeds).evalT c)
    (fun _ : Unit => List (Bytes 16)) (fun _ => (P g).Thash) ((Hash128f.FWots128T seeds).evalC c)
    (wotsStepTargetsT vp) (Hash128f.FWots128T seeds).numTargets
    (by funext pk tw x; exact Hash128f.shape g pk tw [x]) (by funext _ pk tw xs; exact Hash128f.shape g pk tw xs)
    rfl PhaseState B.choose B.forge
  dsimp only [Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T, THFam.preProb, THFam.udProb,
    THFam.tcrProb, THFam.coll, wotsPreProblem, wotsUdProblem, wotsTcrProblemT] at h ⊢
  kexact h

set_option maxRecDepth 3000 in
set_option maxHeartbeats 300000 in
theorem ud_experiment (world : SM_DT_UD_World) (c : CF St Blk) :
    let g : CompressionTables := (c,ref.2)
    let D := udAdv rand A seeds ref
    @SM_DT_UD_Experiment Unit (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16)
      _ world _ (rUd (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))) =
      SM_DT_UD_Experiment world (D.inst id Function.injective_id c) := by
  let g : CompressionTables := (c,ref.2)
  let C := rUd (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))
  let D := udAdv rand A seeds ref
  let B := D.inst id Function.injective_id c
  have hc : C.pick = B.pick := by
    have h := instImpl_emb (α := PhaseState) c (udChoose rand A seeds ref)
    have both := (ud_choose_at rand A seeds ref g).trans h.symm
    dsimp only [C,B,D,udAdv,UdAdv.inst,udChoose] at both ⊢
    kexact both
  have hf (st : PhaseState) (pk : Bytes 16) : C.distinguish st pk = B.distinguish st pk :=
    (ud_fixed rand A ref.1 g seeds st pk).symm
  have eq : C = (⟨PhaseState,B.pick,B.distinguish⟩ : SM_DT_UD_Adversary (wotsUdProblem vp (P g) seeds)) := by
    kexact udAdv_mk_congr (wotsUdProblem vp (P g) seeds) PhaseState _ _ _ _ hc hf
  apply (congrArg (SM_DT_UD_Experiment world) eq).trans
  have h := SM_DT_UD_Experiment_congr (iT := inferInstanceAs (DecidableEq (Bytes 22))) (iT' := inferInstanceAs (DecidableEq (Bytes 22))) world seeds
    (fun pk tw x => (P g).Thash pk tw [x]) ((Hash128f.chainFamily seeds).evalT c) id Function.injective_id Function.injective_id
    (@uniformSample (Bytes 16) sampY128) (@uniformSample (Bytes 16) sampY128)
    (fun _ : Unit => List (Bytes 16)) (fun _ => (P g).Thash) ((Hash128f.chainFamily seeds).evalC c)
    (wotsChainTargets vp) (by funext pk tw x; exact Hash128f.shape g pk tw [x])
    (by funext _ pk tw xs; exact Hash128f.shape g pk tw xs) PhaseState B.pick B.distinguish
  dsimp only [Hash128f.chainFamily,Hash128f.FWots128T,Ideal.FWots128T, THFam.preProb, THFam.udProb,
    THFam.tcrProb, THFam.coll, wotsPreProblem, wotsUdProblem, wotsTcrProblemT] at h ⊢
  kexact h
end First
end MIdeal.Wots128f
#print axioms MIdeal.Wots128f.ud_experiment
#print axioms MIdeal.Wots128f.pre_experiment
#print axioms MIdeal.Wots128f.tcr_experiment
