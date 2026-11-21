import Ideal.Games.TcrFV
import Ideal.Sha.Shape
import Reduction.ForsTightFinal

/-!
# The FORS-leaf SM-TCR game of SLH-DSA-SHA2-128s in the ideal-compression model

The Reduction's FORS-leaf SM-TCR problem `Reduction.forsTcrProblem Link.vp prims pkSeedDist`
(VCVio's source-final-validity SM-DT-TCR, stand-alone on `F = Thash` at arity one, cap
`openPreTargets vp`), taken at the generic SHA-256 primitives `primsG (liftC g)` over a
compression table `g`, is the problem of the Merkle–Damgård family `FFors128 pkSeedDist`
(`forsTcrProblem_eq_fvProb`); at `g = realCF` it is the Reduction's own problem at `Link.prims`
(`forsTcrProblem_realCF`).  `Ideal.tcrFV_bound` gives

`forsTcrAdvantage ≤ (q₂ + 1)/2^128 + q₁·γ + (2 q₁ + qch + 2)/2^256`.
-/

open OracleComp OracleSpec ENNReal

namespace Ideal

open TweakableHash SLHDSA

/-- The source-final-validity SM-TCR experiment at a stand-alone problem depends on the problem
only through its components; adversaries with the same components against stand-alone problems
with equal hash functions have the same experiment. -/
theorem SM_DT_TCR_FV_experiment_congr {PkSeed Tweak M Y : Type}
    {iT iT' : DecidableEq Tweak} {iM iM' : DecidableEq M} {iY iY' : DecidableEq Y}
    (sg : ProbComp PkSeed) (e e' : PkSeed → Tweak → M → Y) (N N' : ℕ) (he : e = e')
    (hN : N = N')
    (State : Type)
    (choose : OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y))) State)
    (forge : State → PkSeed → ProbComp (ℕ × M)) :
    @SM_DT_TCR_SourceFinalValidity.experiment Empty PkSeed Tweak M Y iT iM iY
        (.standalone { seedGen := sg, eval := e } N)
        { State := State, choose := choose, forge := forge } =
      @SM_DT_TCR_SourceFinalValidity.experiment Empty PkSeed Tweak M Y iT' iM' iY'
        (.standalone { seedGen := sg, eval := e' } N')
        { State := State, choose := choose, forge := forge } := by
  subst he hN
  obtain rfl := Subsingleton.elim iT iT'
  obtain rfl := Subsingleton.elim iM iM'
  obtain rfl := Subsingleton.elim iY iY'
  rfl

/-- `F = Thash` at arity one, stand-alone, with the FORS-leaf target cap, as a Merkle–Damgård
family (index type `Empty`: no collection). -/
def FFors128 (pkSeedDist : ProbComp (Bytes 16)) :
    THFam St Blk (Bytes 16) (Bytes 22) (Bytes 16) (Bytes 16) Empty where
  IV := IV128
  sb := sb128
  seedGen := pkSeedDist
  tch := fun t x => tblocks t [x]
  out := out16
  Msg := fun i => i.elim
  cch := fun i => i.elim
  cout := fun i => i.elim
  numTargets := Reduction.openPreTargets Link.vp

/-- The Reduction's FORS-leaf SM-TCR problem at the generic primitives over the table `g` is the
problem of `FFors128` at `g`. -/
theorem forsTcrProblem_eq_fvProb (pkSeedDist : ProbComp (Bytes 16)) (g : CF St Blk) :
    Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist =
      (FFors128 pkSeedDist).fvProb g := by
  have h : (primsG (liftC g)).Thash =
      fun pk a xs => out16 (keyedChain IV128 sb128 g pk (tblocks a xs)) := by
    funext pk a xs
    exact primsG_Thash_shape g pk a xs
  show (.standalone
          { seedGen := pkSeedDist, eval := fun pk t x => (primsG (liftC g)).Thash pk t [x] }
          (Reduction.openPreTargets Link.vp) :
        SM_DT_TCR_SourceFinalValidity.Problem Empty (Bytes 16) (Bytes 22) (Bytes 16)
          (Bytes 16)) = _
  rw [h]
  rfl

/-- At the real compression function the problem is the Reduction's own. -/
theorem forsTcrProblem_realCF (pkSeedDist : ProbComp (Bytes 16)) :
    Reduction.forsTcrProblem Link.vp (primsG (liftC realCF)) pkSeedDist =
      Reduction.forsTcrProblem Link.vp Link.prims pkSeedDist := by
  rw [liftC_realCF]
  rfl

/-- Ideal-model adversaries against the Reduction's FORS-leaf SM-TCR game. -/
abbrev ForsTcrAdv128 (pkSeedDist : ProbComp (Bytes 16)) := FvAdv (FFors128 pkSeedDist)

/-- The adversary against the Reduction's FORS-leaf SM-TCR problem at the table `g`. -/
def instFors {pkSeedDist : ProbComp (Bytes 16)} (A : ForsTcrAdv128 pkSeedDist) (g : CF St Blk) :
    SM_DT_TCR_SourceFinalValidity.Adversary
      (Reduction.forsTcrProblem Link.vp (primsG (liftC g)) pkSeedDist) where
  State := A.State
  choose := simulateQ (instImpl g) A.choose
  forge := fun st pk => simulateQ (instImpl₀ g) (A.forge st pk)

/-- Advantage against the Reduction's FORS-leaf SM-TCR game in the ideal-compression model:
the probability that VCVio's source-final-validity experiment for the Reduction's problem at
`primsG (liftC g)` returns `true`, for a uniform table `g` (see `forsTcrAdvantage_def`). -/
noncomputable def forsTcrAdvantage (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsTcrAdv128 pkSeedDist) : ℝ≥0∞ :=
  idealAdv St Blk fun g => SM_DT_TCR_SourceFinalValidity.experiment (instFors A g)

theorem forsTcrAdvantage_eq_idealAdv (pkSeedDist : ProbComp (Bytes 16))
    (A : ForsTcrAdv128 pkSeedDist) :
    forsTcrAdvantage pkSeedDist A =
      idealAdv St Blk fun g => SM_DT_TCR_SourceFinalValidity.experiment (instFors A g) := rfl

/-- The advantage, unfolded. -/
theorem forsTcrAdvantage_def (pkSeedDist : ProbComp (Bytes 16)) (A : ForsTcrAdv128 pkSeedDist) :
    forsTcrAdvantage pkSeedDist A = 𝒟[do
      let g ← $ᵗ (CF St Blk)
      SM_DT_TCR_SourceFinalValidity.experiment (instFors A g)] {true} :=
  (forsTcrAdvantage_eq_idealAdv pkSeedDist A).trans (idealAdv_def _)

/-- At every table, the experiment of the Reduction's problem is the experiment of the family's
problem. -/
theorem experiment_instFors (pkSeedDist : ProbComp (Bytes 16)) (A : ForsTcrAdv128 pkSeedDist)
    (g : CF St Blk) :
    SM_DT_TCR_SourceFinalValidity.experiment (instFors A g) =
      SM_DT_TCR_SourceFinalValidity.experiment (A.inst g) := by
  have he : (fun (pk : Bytes 16) (t : Bytes 22) (x : Bytes 16) =>
      (primsG (liftC g)).Thash pk t [x]) = (FFors128 pkSeedDist).evalT g := by
    funext pk t x
    exact primsG_Thash_shape g pk t [x]
  exact SM_DT_TCR_FV_experiment_congr (PkSeed := Bytes 16) (Tweak := Bytes 22) (M := Bytes 16)
    (Y := Bytes 16) pkSeedDist _ _ (Reduction.openPreTargets Link.vp)
    (FFors128 pkSeedDist).numTargets he (by simp only [FFors128])
    A.State (simulateQ (instImpl g) A.choose)
    (fun st pk => simulateQ (instImpl₀ g) (A.forge st pk))

theorem forsTcrAdvantage_eq (pkSeedDist : ProbComp (Bytes 16)) (A : ForsTcrAdv128 pkSeedDist) :
    forsTcrAdvantage pkSeedDist A = tcrFVAdvantage (FFors128 pkSeedDist) A := by
  rw [forsTcrAdvantage_eq_idealAdv, tcrFVAdvantage_eq_idealAdv]
  exact congrArg (idealAdv St Blk) (funext fun g => experiment_instFors pkSeedDist A g)

/-- SM-TCR (source final validity) of the 128s FORS-leaf `F` in the ideal-compression model. -/
theorem forsTcr_bound_128s (pkSeedDist : ProbComp (Bytes 16))
    (γ : ℝ≥0∞) (hγ : ∀ s, Pr{let s' ← pkSeedDist}[s' = s] ≤ γ)
    (A : ForsTcrAdv128 pkSeedDist) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hq₂ : A.ForgeBound q₂) :
    forsTcrAdvantage pkSeedDist A ≤ (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * γ +
      (2 * q₁ + qch + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have hs : ∀ (t : Bytes 22) (x : Bytes 16), (tblocks t [x]).2 = [] :=
    fun t x => tblocks_snd_of_length_one t [x] rfl
  have hcard : (Fintype.card St : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
    rw [card_St, Nat.cast_pow, Nat.cast_ofNat]
  rw [forsTcrAdvantage_eq, ← hcard]
  exact tcrFV_bound (F := FFors128 pkSeedDist) sb128_injective γ hγ hs btw128
    (fun t x => btw128_tblocks t [x])
    (fun t x x' h => List.singleton_injective
      (tblocks_injective (Prod.ext h ((hs t x).trans (hs t x').symm))).2)
    _ (fun y => (prEvent_out16_eq y).le) A q₁ qch q₂ hq₁ hch hq₂

/-- `forsTcr_bound_128s` for a uniform public seed. -/
theorem forsTcr_bound_128s_uniform
    (A : ForsTcrAdv128 ($ᵗ (Bytes 16))) (q₁ qch q₂ : ℕ)
    (hq₁ : A.ChooseBound q₁) (hch : A.ChalBound qch) (hq₂ : A.ForgeBound q₂) :
    forsTcrAdvantage ($ᵗ (Bytes 16)) A ≤
      (q₂ + 1 : ℕ) * ((2 : ℝ≥0∞) ^ 128)⁻¹ + q₁ * ((2 : ℝ≥0∞) ^ 128)⁻¹ +
      (2 * q₁ + qch + 2 : ℕ) * ((2 : ℝ≥0∞) ^ 256)⁻¹ :=
  forsTcr_bound_128s _ _ (fun s => by
    rw [SampleableType.prEvent_uniformSample_eq_singleton, card_bytes]
    norm_num) A q₁ qch q₂ hq₁ hch hq₂

end Ideal

#print axioms Ideal.forsTcrProblem_eq_fvProb
#print axioms Ideal.forsTcrProblem_realCF
#print axioms Ideal.forsTcrAdvantage_def
#print axioms Ideal.forsTcrAdvantage_eq
#print axioms Ideal.forsTcr_bound_128s
#print axioms Ideal.forsTcr_bound_128s_uniform
