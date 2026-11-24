import MIdeal.Wots128fExperiments
import MIdeal.Wots128fCounts
import MReduction.Resources

/-! Bounds for the three classical WOTS games of the actual SHA2-128f byte-forger
reduction, averaged over both compression tables. The phase-two query budgets are
derived directly from the byte adversary's raw compression and signing queries. -/

namespace MIdeal.Wots128f

set_option maxRecDepth 3000
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

attribute [local irreducible] preChoose tcrChoose udChoose
private theorem instance_count : (wotsInsts vp).length = 84327972908386521672 :=
  MReduction.wotsInsts_length_128f

private theorem collection_base : wotsQc vp = 309473119577164986225223 := by
  have h := wotsQc_closed vp
  rw [instance_count, show treeC vp = 15 by decide, show forsC vp = 4192 by decide,
    show vp.params.h = 66 by decide] at h
  have arithmetic (q : ℕ) (eqn : q + 2^66 * 15 =
      2^66 * 4192 + (84327972908386521672 + 1) * 15) : q = 309473119577164986225223 := by omega
  exact arithmetic _ h

private theorem challenges_chains : (wotsInsts vp).length * (vp.params.len * 1) = 2951479051793528258520 := by
  rw [instance_count, show vp.params.len = 35 by decide]
private theorem challenges_steps : (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)) = 44272185776902923877800 := by
  rw [instance_count,show vp.params.len = 35 by decide,show vp.params.w = 16 by decide]
private theorem collections_chains : wotsQc vp + (wotsInsts vp).length * (vp.params.len * (vp.params.w - 1)) = 353745305354067910103023 := by
  rw [collection_base,challenges_steps]
private theorem collections_steps : wotsQc vp + (wotsInsts vp).length * (vp.params.len * 1) = 312424598628958514483743 := by
  rw [collection_base,challenges_chains]
variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
variable (seeds : ProbComp (Bytes 16))
variable (q qs L : ℕ)
    (hq : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isPortQP i = true) q)
    (hs : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained isSignQP i = true) qs)
    (hl : ∀ pk, IsQueryBoundP (A.main pk) (fun i => PureCompression.retained (isLongQP L) i = true) 0)
    (ho : ∀ pk z, z ∈ support (A.main pk) → z.1.1.length ≤ L)

private theorem outer_const (loss : ℝ≥0∞) :
    cfAvg (fun _ : CF Chain512 Block512 => loss) ≤ loss := by
  let _ : MeasurableSpace (CF Chain512 Block512) := ⊤
  unfold cfAvg
  rw [MeasureTheory.lintegral_const]
  exact mul_le_of_le_one_right' (evalDist_apply_univ_le_one _)


noncomputable def preLoss (q qs L : ℕ) : ℝ≥0∞ :=
  2 * (phaseBudget (wotsPreHashes vp) q qs L + 1 : ℕ) * ((2 : ℝ≥0∞)^128)⁻¹ +
    ((2951479051793528258520 + 353745305354067910103023) * (1 + 2 * blockBudget) + 2 : ℕ) * ((2 : ℝ≥0∞)^256)⁻¹

include hq hs hl ho in
theorem pre_term :
    PureCompression.average (fun g => SM_DT_PRE_Advantage
      (rPre (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g)))) ≤ preLoss q qs L := by
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => let g : CompressionTables := (c,other)
        SM_DT_PRE_Advantage (rPre (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g)))) ≤ preLoss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := preAdv rand A seeds ref
    have he (c : CF St Blk) := congrArg evalDist (pre_experiment rand A seeds ref c)
    have eq := (cfAvg_of_evalDist_eq he).trans (@preAdvantage_eq_cfAdvantage St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) (Bytes 16) Unit _ _ sampY128 _ (Hash128f.chainFamily seeds) id Function.injective_id D).symm
    apply eq.le.trans
    have hf : D.InvertBound (phaseBudget (wotsPreHashes vp) q qs L) := fun st pk => pre_count rand A ref q qs L hq hs hl ho st pk
    have ch := pre_chal rand A seeds ref
    have co := pre_coll rand A seeds ref
    rw [challenges_chains] at ch
    rw [collections_chains] at co
    have h := Hash128f.wotsPre_bound seeds 1
      (fun _ => le_trans (MeasureTheory.measure_mono (Set.subset_univ _)) (evalDist_apply_univ_le_one _))
      D 0 (2951479051793528258520) (353745305354067910103023) blockBudget (phaseBudget (wotsPreHashes vp) q qs L)
      (pre_zero rand A seeds ref) ch co (pre_len rand A seeds ref) hf
    simpa only [preLoss,Nat.cast_zero,zero_mul,Nat.mul_zero,Nat.add_zero,Nat.zero_add,add_zero] using h
  exact (cfAvg_mono bound).trans (outer_const _)

noncomputable def tcrLoss (q qs L : ℕ) : ℝ≥0∞ :=
  (phaseBudget (wotsTcrHashes vp) q qs L + 1 : ℕ) * ((2 : ℝ≥0∞)^128)⁻¹ +
    ((44272185776902923877800 + 312424598628958514483743) * (1 + 2 * blockBudget) + 2 : ℕ) * ((2 : ℝ≥0∞)^256)⁻¹

include hq hs hl ho in
theorem tcr_term :
    PureCompression.average (fun g => SM_DT_TCR_Advantage
      (rTcrT (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g)))) ≤ tcrLoss q qs L := by
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => let g : CompressionTables := (c,other)
        SM_DT_TCR_Advantage (rTcrT (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g)))) ≤ tcrLoss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := tcrAdv rand A seeds ref
    have he (c : CF St Blk) := congrArg evalDist (tcr_experiment rand A seeds ref c)
    have eq := (cfAvg_of_evalDist_eq he).trans ((cfAdvantage_eq_idealAdvT _).trans
        (tcrAdvantage_eq_idealAdv (Hash128f.FWots128T seeds) D).symm)
    apply eq.le.trans
    have hf : D.ForgeBound (phaseBudget (wotsTcrHashes vp) q qs L) := fun st pk => tcr_count rand A ref q qs L hq hs hl ho st pk
    have ch := tcr_chal rand A seeds ref
    have co := tcr_coll rand A seeds ref
    rw [challenges_steps] at ch
    rw [collections_steps] at co
    have h := Hash128f.wotsTcr_bound seeds 1
      (fun _ => le_trans (MeasureTheory.measure_mono (Set.subset_univ _)) (evalDist_apply_univ_le_one _))
      D 0 (44272185776902923877800) (312424598628958514483743) blockBudget (phaseBudget (wotsTcrHashes vp) q qs L)
      (tcr_zero rand A seeds ref) ch co (tcr_len rand A seeds ref) hf
    simpa only [tcrLoss,Nat.cast_zero,zero_mul,Nat.mul_zero,Nat.add_zero,Nat.zero_add,add_zero] using h
  exact (cfAvg_mono bound).trans (outer_const _)

noncomputable def udLoss (q qs L : ℕ) : ℝ≥0∞ :=
  phaseBudget (wotsWinHashes vp) q qs L * ((2 : ℝ≥0∞)^128)⁻¹ +
    (2 * ((2951479051793528258520 + 353745305354067910103023) * (1 + 2 * blockBudget) + 1) : ℕ) * ((2 : ℝ≥0∞)^256)⁻¹

include hq hs hl ho in
theorem ud_term :
    PureCompression.average (fun g => SM_DT_UD_RealSuccess (rUd (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g)))) ≤
      PureCompression.average (fun g => SM_DT_UD_IdealSuccess (rUd (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g)))) + udLoss q qs L := by
  let R (g : CompressionTables) := rUd (prims := P g) seeds (Lazy.bWotsS (reduced rand A seeds g))
  let I (other : CF Chain512 Block512) := cfAvg fun c => SM_DT_UD_IdealSuccess (R (c,other))
  have bounds (other : CF Chain512 Block512) :
      (cfAvg fun c => SM_DT_UD_RealSuccess (R (c,other))) ≤ I other + udLoss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := udAdv rand A seeds ref
    have hf : D.DistBound (phaseBudget (wotsWinHashes vp) q qs L) := fun st pk => ud_count rand A ref q qs L hq hs hl ho st pk
    have real := cfAvg_of_evalDist_eq (fun c => congrArg evalDist (ud_experiment rand A seeds ref .real c))
    have ideal := cfAvg_of_evalDist_eq (fun c => congrArg evalDist (ud_experiment rand A seeds ref .ideal c))
    have ch := ud_chal rand A seeds ref
    have co := ud_coll rand A seeds ref
    rw [challenges_chains] at ch
    rw [collections_chains] at co
    have h := Hash128f.wotsUd_bound seeds 1
      (fun _ => le_trans (MeasureTheory.measure_mono (Set.subset_univ _)) (evalDist_apply_univ_le_one _))
      D 0 2951479051793528258520 353745305354067910103023 blockBudget (phaseBudget (wotsWinHashes vp) q qs L)
      (ud_zero rand A seeds ref) ch co (ud_len rand A seeds ref) hf
    rw [udRealI_eq_cfAdvantage,udIdealI_eq_cfAdvantage] at h
    have final := add_le_add ideal.symm.le (le_refl (udLoss q qs L))
    apply real.le.trans
    apply le_trans ?_ final
    simp only [udLoss,Nat.cast_zero,zero_mul,mul_zero,Nat.zero_add,add_zero,add_assoc,D,
      UdAdv.inst, THFam.udProb] at h ⊢
    kexact h
  apply (cfAvg_mono bounds).trans
  rw [cfAvg_add]
  exact add_le_add le_rfl (outer_const _)

end MIdeal.Wots128f

#print axioms MIdeal.Wots128f.pre_term
#print axioms MIdeal.Wots128f.tcr_term

#print axioms MIdeal.Wots128f.ud_term
