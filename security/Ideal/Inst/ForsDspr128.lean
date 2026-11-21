import Ideal.Games.Dspr
import Ideal.Inst.ForsTcr128

/-!
# The FORS-leaf SM-DSPR game of SLH-DSA-SHA2-128s in the ideal-compression model

The Reduction's FORS-leaf SM-DSPR problem `Reduction.forsDsprProblem Link.vp prims pkSeedDist`
(VCVio's source-final-validity SM-DT-DSPR, stand-alone on `F = Thash` at arity one, cap
`openPreTargets vp`), taken at the generic SHA-256 primitives `primsG (liftC g)` over a
compression table `g`, is the problem of the Merkle–Damgård family `FFors128 pkSeedDist`
(`forsDsprProblem_eq_dsprProb`); at `g = realCF` it is the Reduction's own problem at
`Link.prims` (`forsDsprProblem_realCF`).  `Ideal.dspr_bound_uniform` gives, for an adversary
whose guess phase makes at most `q₂ ≤ 2^126` compression queries,

`forsDsprSuccess ≤ forsDsprSP + 2·q₁·γ + (4 q₁ + 2 qch + 3)/2^256`

where `forsDsprSuccess`, `forsDsprSP` are VCVio's `Success` and `SPProbability` of the
Reduction's problem at `primsG (liftC g)`, averaged over a uniform table `g`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash SLHDSA

/-- The source-final-validity SM-DSPR experiments at a stand-alone problem depend on the problem
only through its components (and not on the choice of instances). -/
theorem SM_DT_DSPR_FV_experiment_congr {PkSeed Tweak M Y : Type}
    {iF iF' : Fintype M}
    {iT iT' : DecidableEq Tweak} {iM iM' : DecidableEq M} {iY iY' : DecidableEq Y}
    (sg : ProbComp PkSeed) (e e' : PkSeed → Tweak → M → Y) (N N' : ℕ) (he : e = e')
    (hN : N = N')
    (State : Type)
    (choose : OracleComp (unifSpec + (SM_DT_DSPR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y))) State)
    (guess : State → PkSeed → ProbComp (ℕ × Bool)) :
    @SM_DT_DSPR_SourceFinalValidity.experiment Empty PkSeed Tweak M Y iF iT iM iY
        (.standalone { seedGen := sg, eval := e } N)
        { State := State, choose := choose, guess := guess } =
      @SM_DT_DSPR_SourceFinalValidity.experiment Empty PkSeed Tweak M Y iF' iT' iM' iY'
        (.standalone { seedGen := sg, eval := e' } N')
        { State := State, choose := choose, guess := guess } ∧
    @SM_DT_DSPR_SourceFinalValidity.spExperiment Empty PkSeed Tweak M Y iF iT iM iY
        (.standalone { seedGen := sg, eval := e } N)
        { State := State, choose := choose, guess := guess } =
      @SM_DT_DSPR_SourceFinalValidity.spExperiment Empty PkSeed Tweak M Y iF' iT' iM' iY'
        (.standalone { seedGen := sg, eval := e' } N')
        { State := State, choose := choose, guess := guess } := by
  subst he hN
  obtain rfl := Subsingleton.elim iF iF'
  obtain rfl := Subsingleton.elim iT iT'
  obtain rfl := Subsingleton.elim iM iM'
  obtain rfl := Subsingleton.elim iY iY'
  exact ⟨rfl, rfl⟩

/-- The Reduction's FORS-leaf SM-DSPR problem at the generic primitives over the table `g` is
the problem of `FFors128` at `g`. -/
theorem forsDsprProblem_eq_dsprProb (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist =
      (FFors128 pkSeedDist).dsprProb g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show (.standalone
          { seedGen := pkSeedDist, eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] }
          (Reduction.openPreTargets Link.vp) :
        SM_DT_DSPR_SourceFinalValidity.Problem Empty (Bytes 16) (Bytes 22) (Bytes 16)
          (Bytes 16)) = _
  rw [h]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem forsDsprProblem_realCF (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.forsDsprProblem Link.vp (primsG (liftC realCF)) pkSeedDist =
      Reduction.forsDsprProblem Link.vp Link.prims pkSeedDist := by
  rw [liftC_realCF]
  rfl

/-- The message/digest type of the generic primitives is `Bytes 16`, a finite type (the DSPR
winning predicate decides whether a second preimage exists; cf. the Reduction's
`instFintypeY128s` at `Link.prims`). -/
instance instFintypeYG (g : CF St Blk) : Fintype (primsG (liftC g)).Y :=
  inferInstanceAs (Fintype (Bytes 16))

/-- Ideal-model adversaries against the Reduction's FORS-leaf SM-DSPR game. -/
abbrev ForsDsprAdv128 (pkSeedDist : ProbComp (Bytes 16)) := DsprAdv (FFors128 pkSeedDist)

/-- The adversary against the Reduction's FORS-leaf SM-DSPR problem at the table `g`. -/
def instForsDspr {pkSeedDist : ProbComp (Bytes 16)} (A : ForsDsprAdv128 pkSeedDist)
    (g : CF St Blk) :
    SM_DT_DSPR_SourceFinalValidity.Adversary
      (Reduction.forsDsprProblem Link.vp (primsG (liftC g)) pkSeedDist) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  guess := fun st pk => simulateQ (instImpl₀ g) (A.guess st pk)

/-- Raw DSPR prediction success against the Reduction's FORS-leaf SM-DSPR game in the
ideal-compression model: the probability that VCVio's `experiment` (defining `Success`) for the
Reduction's problem at `primsG (liftC g)` returns `true`, for a uniform table `g`
(see `forsDsprSuccess_def`). -/
noncomputable def forsDsprSuccess (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsDsprAdv128 pkSeedDist) : ℝ≥0∞ :=
  idealAdv St Blk fun g => SM_DT_DSPR_SourceFinalValidity.experiment (instForsDspr A g)

/-- The `SPprob` baseline of the Reduction's FORS-leaf SM-DSPR game in the ideal-compression
model: VCVio's `spExperiment` (defining `SPProbability`), table-averaged
(see `forsDsprSP_def`). -/
noncomputable def forsDsprSP (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsDsprAdv128 pkSeedDist) : ℝ≥0∞ :=
  idealAdv St Blk fun g => SM_DT_DSPR_SourceFinalValidity.spExperiment (instForsDspr A g)

theorem forsDsprSuccess_eq_idealAdv (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsDsprAdv128 pkSeedDist) :
    forsDsprSuccess pkSeedDist A =
      idealAdv St Blk fun g =>
        SM_DT_DSPR_SourceFinalValidity.experiment (instForsDspr A g) := rfl

theorem forsDsprSP_eq_idealAdv (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsDsprAdv128 pkSeedDist) :
    forsDsprSP pkSeedDist A =
      idealAdv St Blk fun g =>
        SM_DT_DSPR_SourceFinalValidity.spExperiment (instForsDspr A g) := rfl

/-- The success probability, unfolded. -/
theorem forsDsprSuccess_def (pkSeedDist : ProbComp (Bytes 16)) (A : ForsDsprAdv128 pkSeedDist) :
    forsDsprSuccess pkSeedDist A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_DSPR_SourceFinalValidity.experiment (instForsDspr A g)] {true} :=
  (forsDsprSuccess_eq_idealAdv pkSeedDist A).trans (idealAdv_def _)

/-- The baseline probability, unfolded. -/
theorem forsDsprSP_def (pkSeedDist : ProbComp (Bytes 16)) (A : ForsDsprAdv128 pkSeedDist) :
    forsDsprSP pkSeedDist A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_DSPR_SourceFinalValidity.spExperiment (instForsDspr A g)] {true} :=
  (forsDsprSP_eq_idealAdv pkSeedDist A).trans (idealAdv_def _)

/-- At every table, the experiments of the Reduction's problem are the experiments of the
family's problem. -/
theorem experiment_instForsDspr (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsDsprAdv128 pkSeedDist) (g : CF St Blk) :
    SM_DT_DSPR_SourceFinalValidity.experiment (instForsDspr A g) =
        SM_DT_DSPR_SourceFinalValidity.experiment (A.inst g) ∧
      SM_DT_DSPR_SourceFinalValidity.spExperiment (instForsDspr A g) =
        SM_DT_DSPR_SourceFinalValidity.spExperiment (A.inst g) := by
  have he : (fun (pk : Bytes 16) (t : Bytes 22) (x : Bytes 16) =>
      (primsG (liftC g)).Thash pk t [x]) = (FFors128 pkSeedDist).evalT g := by
    funext pk t x
    exact primsG_Thash_shape g pk t [x]
  exact SM_DT_DSPR_FV_experiment_congr (PkSeed := Bytes 16) (Tweak := Bytes 22) (M := Bytes 16)
    (Y := Bytes 16) pkSeedDist _ _ (Reduction.openPreTargets Link.vp)
    (FFors128 pkSeedDist).numTargets he (by simp only [FFors128])
    A.State (simulateQ (instImpl g) A.choose)
    (fun st pk => simulateQ (instImpl₀ g) (A.guess st pk))

theorem forsDsprSuccess_eq (pkSeedDist : ProbComp (Bytes 16)) (A : ForsDsprAdv128 pkSeedDist) :
    forsDsprSuccess pkSeedDist A = dsprSuccessI (FFors128 pkSeedDist) A :=
  congrArg (idealAdv St Blk) (funext fun g => (experiment_instForsDspr pkSeedDist A g).1)

theorem forsDsprSP_eq (pkSeedDist : ProbComp (Bytes 16)) (A : ForsDsprAdv128 pkSeedDist) :
    forsDsprSP pkSeedDist A = dsprSPI (FFors128 pkSeedDist) A :=
  congrArg (idealAdv St Blk) (funext fun g => (experiment_instForsDspr pkSeedDist A g).2)

/-- SM-DSPR (source final validity) of the 128s FORS-leaf `F` in the ideal-compression model:
raw prediction success is at most the `SPprob` baseline plus the hidden-prefix error, for
adversaries whose guess phase makes at most `2^126` compression queries. -/
theorem forsDspr_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : ForsDsprAdv128 pkSeedDist) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hq₂ : A.GuessBound q₂)
    (hq₂le : q₂ ≤ 2 ^ 126) :
    forsDsprSuccess pkSeedDist A ≤ forsDsprSP pkSeedDist A + 2 * (q₁ * γ) +
      (4 * q₁ + 2 * qch + 3 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  have hcard : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    rw [card_St, Nat.cast_pow, Nat.cast_ofNat]
  rw [forsDsprSuccess_eq, forsDsprSP_eq, ← hcard]
  refine dspr_bound_uniform (F := FFors128 pkSeedDist) sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x])
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    (fun y => ?_) ?_ A q₁ qch q₂ hq₁ hch hq₂ ?_
  · rw [card_bytes]
    exact (prEvent_out16_eq y).trans (by norm_num)
  · rw [card_bytes]; norm_num
  · rw [card_bytes]
    have : (256 : ℕ) ^ 16 = 4 * 2 ^ 126 := by norm_num
    omega

/-- `forsDspr_bound_128s` for a uniform public seed. -/
theorem forsDspr_bound_128s_uniform
    (A : ForsDsprAdv128 ($ᵗ (Bytes 16))) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hq₂ : A.GuessBound q₂)
    (hq₂le : q₂ ≤ 2 ^ 126) :
    forsDsprSuccess ($ᵗ (Bytes 16)) A ≤
      forsDsprSP ($ᵗ (Bytes 16)) A + 2 * (q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹) +
      (4 * q₁ + 2 * qch + 3 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  forsDspr_bound_128s _ _ (fun s => by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, card_bytes]
    norm_num) A q₁ qch q₂ hq₁ hch hq₂ hq₂le

end Ideal

#print axioms Ideal.forsDsprProblem_eq_dsprProb
#print axioms Ideal.forsDsprProblem_realCF
#print axioms Ideal.forsDsprSuccess_def
#print axioms Ideal.forsDsprSP_def
#print axioms Ideal.forsDsprSuccess_eq
#print axioms Ideal.forsDsprSP_eq
#print axioms Ideal.forsDspr_bound_128s
#print axioms Ideal.forsDspr_bound_128s_uniform
