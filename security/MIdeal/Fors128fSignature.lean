import MIdeal.Fors128fFixed
namespace MIdeal.Fors128f
open Ideal Ideal.Realize MLink SLHDSA SLHDSA.Security OracleComp OracleSpec Reduction Reduction.Open Ideal.Transport TweakableHash ENNReal
open Ideal.Realize.Fors Reduction.Resources2 Reduction.Lazy
open Class128f (vp P)
attribute [local irreducible] wotsChainTargets wotsStepTargets wotsStepTargetsT Lazy.structSecIdx Lazy.sparseTable wotsInsts
noncomputable local instance expY (g : CompressionTables) : SampleableType (P g).Y := sampY128
local instance expSk (g : CompressionTables) : SampleableType (P g).SkSeed := inferInstanceAs (SampleableType (Bytes 16))
local instance expPrf (g : CompressionTables) : SampleableType (P g).SkPrf := inferInstanceAs (SampleableType (Bytes 16))
local instance expInh (g : CompressionTables) : Inhabited (P g).Y := inferInstanceAs (Inhabited (Bytes 16))
local instance expEqY (g : CompressionTables) : DecidableEq (P g).Y := inferInstanceAs (DecidableEq (Bytes 16))
local instance expEqPk (g : CompressionTables) : DecidableEq (P g).PkSeed := inferInstanceAs (DecidableEq (Bytes 16))
local instance expEqAd (g : CompressionTables) : DecidableEq (P g).AdrsKey := inferInstanceAs (DecidableEq (Bytes 22))
local instance expFinite (g : CompressionTables) : Fintype (P g).Y := inferInstanceAs (Fintype (Bytes 16))

variable (rand : Bytes 16 → Bytes 16 → ProbComp (Bytes 16)) (A : PureCompression.Forger)
variable (seeds : ProbComp (Bytes 16)) (ref : CompressionTables) (c : CF St Blk)

set_option maxHeartbeats 350000 in
theorem tcr_experiment :
    let g : CompressionTables := (c,ref.2)
    let D := tcrAdv rand A seeds ref
    SM_DT_TCR_SourceFinalValidity.experiment (toTcr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))) =
        SM_DT_TCR_SourceFinalValidity.experiment (D.inst c) := by
  let g : CompressionTables := (c,ref.2)
  let C := toTcr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))
  let D := tcrAdv rand A seeds ref
  let B := D.inst c
  have hc : C.choose = B.choose := by
    have h := instImpl_emb (α := State) c (choose ref)
    exact (tcr_choose_fixed rand A seeds ref.1 g).trans h.symm
  have hf (st : State) (pk : Bytes 16) : C.forge st pk = B.forge st pk :=
    tcr_fixed rand A seeds ref.1 g st pk
  have eq : C = (⟨State,B.choose,B.forge⟩ : SM_DT_TCR_SourceFinalValidity.Adversary (forsTcrProblem vp (P g) seeds)) :=
    tcrAdv_mk_congr (σ := State) hc hf
  have he := Fors.eval_eq Sha2Set.s128f seeds g
  have h := SM_DT_TCR_FV_experiment_congr (PkSeed := Bytes 16) (Tweak := Bytes 22) (M := Bytes 16) (Y := Bytes 16)
    (iT := inferInstanceAs (DecidableEq (Bytes 22))) (iT' := inferInstanceAs (DecidableEq (Bytes 22)))
    (iM := inferInstanceAs (DecidableEq (Bytes 16))) (iM' := inferInstanceAs (DecidableEq (Bytes 16)))
    (iY := inferInstanceAs (DecidableEq (Bytes 16))) (iY' := inferInstanceAs (DecidableEq (Bytes 16)))
    
    seeds _ _ (openPreTargets vp) (Fors.family Sha2Set.s128f seeds).numTargets he rfl State B.choose B.forge
  exact (congrArg SM_DT_TCR_SourceFinalValidity.experiment eq).trans h

set_option maxHeartbeats 350000 in
theorem dspr_experiment :
    let g : CompressionTables := (c,ref.2)
    let D := dsprAdv rand A seeds ref
    SM_DT_DSPR_SourceFinalValidity.experiment (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))) =
        SM_DT_DSPR_SourceFinalValidity.experiment (D.inst c) ∧
      SM_DT_DSPR_SourceFinalValidity.spExperiment (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))) =
        SM_DT_DSPR_SourceFinalValidity.spExperiment (D.inst c) := by
  let g : CompressionTables := (c,ref.2)
  let C := toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g))
  let D := dsprAdv rand A seeds ref
  let B := D.inst c
  have hc : C.choose = B.choose := by
    have h := instImpl_emb (α := State) c (choose ref)
    exact (dspr_choose_fixed rand A seeds ref.1 g).trans h.symm
  have hf (st : State) (pk : Bytes 16) : C.guess st pk = B.guess st pk :=
    dspr_fixed rand A seeds ref.1 g st pk
  have eq : C = (⟨State,B.choose,B.guess⟩ : SM_DT_DSPR_SourceFinalValidity.Adversary (forsDsprProblem vp (P g) seeds)) :=
    dsprAdv_mk_congr (σ := State) hc hf
  have he := Fors.eval_eq Sha2Set.s128f seeds g
  have h := SM_DT_DSPR_FV_experiment_congr (PkSeed := Bytes 16) (Tweak := Bytes 22) (M := Bytes 16) (Y := Bytes 16)
    (iT := inferInstanceAs (DecidableEq (Bytes 22))) (iT' := inferInstanceAs (DecidableEq (Bytes 22)))
    (iM := inferInstanceAs (DecidableEq (Bytes 16))) (iM' := inferInstanceAs (DecidableEq (Bytes 16)))
    (iY := inferInstanceAs (DecidableEq (Bytes 16))) (iY' := inferInstanceAs (DecidableEq (Bytes 16)))
    (iF := inferInstanceAs (Fintype (Bytes 16))) (iF' := inferInstanceAs (Fintype (Bytes 16)))
    seeds _ _ (openPreTargets vp) (Fors.family Sha2Set.s128f seeds).numTargets he rfl State B.choose B.guess
  exact ⟨(congrArg SM_DT_DSPR_SourceFinalValidity.experiment eq).trans h.1, (congrArg SM_DT_DSPR_SourceFinalValidity.spExperiment eq).trans h.2⟩
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



private theorem choose_zero :
    IsQueryBoundP (simulateQ embImpl (choose ref) :
      OracleComp (Fors.family Sha2Set.s128f seeds).fvAdvS State)
      (fun i => THFam.fvIsH (Fors.family Sha2Set.s128f seeds) i = true) 0 :=
  emb_noH _ (fun t => by rcases t with n | t <;> simp [embIdx, THFam.fvIsH]) _

private theorem choose_challenges :
    IsQueryBoundP (simulateQ embImpl (choose ref) :
      OracleComp (Fors.family Sha2Set.s128f seeds).fvAdvS State)
      (fun i => THFam.fvIsChal (Fors.family Sha2Set.s128f seeds) i = true) (openPreTargets vp) := by
  refine emb_bound _ _ _ (chal_of_eq (vp := vp) (prims := P ref) (choose ref) (choose_def ref) _ fun t ht => ?_)
  rcases t with n | (x | q)
  · simp [embIdx, THFam.fvIsChal] at ht
  · rfl
  · simp [embIdx, THFam.fvIsChal] at ht

def budget (q qs L : ℕ) := phaseBudget q qs (L+257)
noncomputable def tcrLoss (q qs L : ℕ) : ℝ≥0∞ :=
  (budget q qs L + 1 : ℕ) * ((2:ℝ≥0∞)^128)⁻¹ + (155838093934698292051968 + 2 : ℕ)*((2:ℝ≥0∞)^256)⁻¹
noncomputable def dsprLoss : ℝ≥0∞ := (2*155838093934698292051968 + 3 : ℕ) * ((2:ℝ≥0∞)^256)⁻¹

include hq hs hl ho in
private theorem dspr_phase : (dsprAdv rand A seeds ref).GuessBound (budget q qs L) := by
  intro st pk
  exact phase_count ref (fun tg z => forsDsprPost tg z) _ _ q qs (L+257)
    (PureCompression.typed_port _ A ref _ hq) (PureCompression.typed_sign _ A ref _ hs)
    (PureCompression.typed_long _ A ref _ hl) (PureCompression.typed_out _ A ref _ ho)
    st.1 st.2.1 st.2.2 pk

include hq hs hl ho in
private theorem tcr_phase : (tcrAdv rand A seeds ref).ForgeBound (budget q qs L) := by
  intro st pk
  exact phase_count ref (fun _ z => forsTcrPost z) _ _ q qs (L+257)
    (PureCompression.typed_port _ A ref _ hq) (PureCompression.typed_sign _ A ref _ hs)
    (PureCompression.typed_long _ A ref _ hl) (PureCompression.typed_out _ A ref _ ho)
    st.1 st.2.1 st.2.2 pk


include hq hs hl ho in
theorem tcr_term :
    PureCompression.average (fun g => SM_DT_TCR_SourceFinalValidity.advantage
      (toTcr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g)))) ≤ tcrLoss q qs L := by
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => SM_DT_TCR_SourceFinalValidity.advantage
        (toTcr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds (c,other))))) ≤ tcrLoss q qs L := by
    let ref : CompressionTables := (default,other)
    let D := tcrAdv rand A seeds ref
    have eq := (cfAvg_of_evalDist_eq (fun c => congrArg evalDist (tcr_experiment rand A seeds ref c))).trans ((cfAdvantage_eq_idealAdv _).trans (tcrFVAdvantage_eq_idealAdv (Fors.family Sha2Set.s128f seeds) D).symm)
    have b := Fors.tcr_bound Sha2Set.s128f seeds 1 (fun _ => le_trans (MeasureTheory.measure_mono (Set.subset_univ _)) (evalDist_apply_univ_le_one _)) D 0 (openPreTargets vp) (budget q qs L)
      (choose_zero seeds ref) (choose_challenges seeds ref) (tcr_phase rand A seeds ref q qs L hq hs hl ho)
    apply eq.le.trans
    dsimp only [tcrLoss]
    have hc : Fintype.card Sha2Set.s128f.Node = 2^128 := by rw [card_bytes]; decide
    rw [MReduction.openPreTargets_128f_val, hc] at b
    simp only [Nat.mul_zero,Nat.zero_add,Nat.cast_zero,zero_mul,add_zero, Nat.cast_pow,Nat.cast_ofNat] at b
    exact b
  exact (cfAvg_mono bound).trans (outer_const _)

include hq hs hl ho in
theorem dspr_term (hcap : 4*budget q qs L ≤ 2^128) :
    PureCompression.average (fun g => SM_DT_DSPR_SourceFinalValidity.Success
      (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g)))) ≤
      PureCompression.average (fun g => SM_DT_DSPR_SourceFinalValidity.SPProbability
        (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds g)))) + dsprLoss := by
  let I (other : CF Chain512 Block512) := cfAvg fun c => SM_DT_DSPR_SourceFinalValidity.SPProbability
    (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds (c,other))))
  have bound (other : CF Chain512 Block512) :
      (cfAvg fun c => SM_DT_DSPR_SourceFinalValidity.Success
        (toDspr (Lazy.bOpenPreS (Wots128f.reduced rand A seeds (c,other))))) ≤ I other + dsprLoss := by
    let ref : CompressionTables := (default,other)
    let D := dsprAdv rand A seeds ref
    have re := (cfAvg_of_evalDist_eq (fun c => congrArg evalDist (dspr_experiment rand A seeds ref c).1)).trans (cfAdvantage_eq_idealAdv _)
    have ie := (cfAvg_of_evalDist_eq (fun c => congrArg evalDist (dspr_experiment rand A seeds ref c).2)).trans (cfAdvantage_eq_idealAdv _)
    have b := Fors.dspr_bound Sha2Set.s128f seeds 1 (fun _ => le_trans (MeasureTheory.measure_mono (Set.subset_univ _)) (evalDist_apply_univ_le_one _)) D 0 (openPreTargets vp) (budget q qs L)
      (choose_zero seeds ref) (choose_challenges seeds ref) (dspr_phase rand A seeds ref q qs L hq hs hl ho) (by rw [card_bytes]; exact hcap)
    apply re.le.trans
    apply le_trans ?_ (add_le_add ie.symm.le (le_refl dsprLoss))
    rw [MReduction.openPreTargets_128f_val] at b
    simp only [Nat.zero_add,Nat.cast_zero,zero_mul,mul_zero,add_zero] at b
    dsimp only [D,dsprSuccessI,dsprSPI,dsprLoss] at b ⊢
    kexact b
  apply (cfAvg_mono bound).trans
  rw [cfAvg_add]
  exact add_le_add le_rfl (outer_const _)
end MIdeal.Fors128f
#print axioms MIdeal.Fors128f.dspr_term
#print axioms MIdeal.Fors128f.tcr_term
